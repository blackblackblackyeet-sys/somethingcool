#!/usr/bin/env python3
"""LAN Blocks 3D - server (Python standard library only).

Serves index.html over HTTP and speaks a minimal WebSocket protocol for the
game connection. The server owns all the physics; browsers just send their
controls and draw what the server tells them.

THE GAME
  * Everyone spawns into a long 3D arena. Walk up to another player and press
    Q to tether to them (press Q next to them again to untether). You can be
    tethered to several people at once.
  * Everyone joined together by ropes is a group. The WHOLE group has to reach
    the finish line. If anyone touches a spike (or falls in the void) the whole
    group goes back to the start. When a group finishes, only THAT group resets.
  * The more players in a group, the shorter the ropes: with n players each rope
    is 1/(n-1) of the normal length (never shorter than MIN_REST).
  * The tether wraps around poles and walls like a real rope - as many times
    as you like.
  * Two scoreboards: fastest finish times, and most players finished at once
    (each one uses the other as its tiebreaker).

Movement is icy and bouncy: low friction, long slides, walls bounce you back.
  DOCK  - hold next to a wall/floor to lock in place as an anchor.
  GRAB  - hold near a tethered friend to pick them up. Let go to throw them.
          A rider can press jump to leap off for a double-height hop.
  SLINGSHOT - dock, let your partner run away to stretch the tether (they
          get extra pulling strength while leaning into a taut rope), then
          they let go and fly back at you. Grab them as they pass and jump.

The host (whoever opens the page on the machine running this server, or opens
/?host=<HOST_KEY> when it is hosted online) gets a panel with Kick buttons.

Coordinates: x = along the race (finish is +x), y = up, z = sideways.
Run with:  python3 server.py
"""
import asyncio
import base64
import gzip
import hashlib
import hmac
import json
import math
import os
import socket
import struct
import time
import traceback
from urllib.parse import unquote_plus

PORT = int(os.environ.get("PORT", 3000))
SIZE = 40                  # player cube size
TICK_RATE = 60
STATE_EVERY = 3            # send positions every Nth tick (3 = 20 updates/s; the page smooths in between)
MAX_DT = 1 / 30            # if the server falls behind, take bigger steps (up to this) so the game keeps real-time speed

# --- icy movement ---
MOVE_SPEED = 520           # px/s   top speed from your own running (hold W cap)
GROUND_ACCEL = 1100        # px/s^2 slow to get going (and slow to turn around)
AIR_ACCEL = 800
GROUND_FRICTION = 280      # px/s^2 very little: you slide a long way
AIR_FRICTION = 40
OVERSPEED_GROUND = 200     # extra drag only when going faster than MOVE_SPEED
OVERSPEED_AIR = 8          # (low, so slingshot speed carries through the air)
WALL_BOUNCE = 0.75         # fraction of speed kept when you hit a wall (bouncy!)
BOUNCE_MIN = 100           # slower than this and you just stop

# --- floaty, flowing jumps ---
GRAVITY = 1500             # px/s^2
FALL_MULT = 1.25           # fall a bit faster than you rise
JUMP_SPEED = 760           # px/s   (~4.8 blocks high, ~1s in the air)
JUMP_CUT = 0.65            # let go of jump early: upward speed capped to this fraction
COYOTE = 0.25              # s you can still jump after leaving a ledge (generous: online lag eats into this)
JUMP_BUFFER = 0.15         # s a jump press is remembered before landing
MAX_FALL = 1300
MAX_SPEED = 2600           # cap so slingshots stay sane (was 1500)
VOID_Y = -700              # fall below this and your pair is sent back

# --- the energy tether ---
TETHER_REST = 280          # px of rope before it gets taut (2 players; more players = shorter)
MIN_REST = 60              # ropes never get shorter than this, however big the group
TETHER_K = 6.0             # pull strength: acceleration per px of stretch
TETHER_DAMP = 0.5          # drag on the beam while it is being stretched further
TETHER_MAX_ACC = 4500
LEAN_BOOST = 3.2           # your running strength x this while leaning away from a taut rope
LEAN_DOT = -0.3            # "leaning away" = heading . direction-to-rope below this
ROPE_OUTSET = 3.0          # how far outside a pole's corner the rope sits
MAX_PIVOTS = 300           # practically unlimited wraps

# --- linking (Q) ---
LINK_RANGE = 130           # px between cube centres
LINK_COOLDOWN = 0.4
START_LINE_X = 300         # tethering while both are behind this restarts both run timers

# --- grabbing ---
GRAB_RANGE = 90            # px between cube centres
GRAB_COOLDOWN = 0.6        # s before someone you just dropped/threw can be re-grabbed
THROW_X = 450
THROW_Y = 350

FINISH_PAUSE = 2.5         # s the finishing pair sees their time before going back to the start

CHAT_MAX = 120
CHAT_COOLDOWN = 0.4
KICK_BLOCK_SECONDS = 60    # a kicked address can't rejoin for this long

WS_GUID = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"
COLORS = ["#e74c3c", "#3498db", "#2ecc71", "#f1c40f",
          "#9b59b6", "#e67e22", "#1abc9c", "#ff69b4"]
HERE = os.path.dirname(os.path.abspath(__file__))
SCORES_FILE = os.path.join(HERE, "scores.json")


# ---------- the arena ----------
# Box = (x0, y0, z0, x1, y1, z1, kind)
K_SOLID, K_POLE, K_WALL, K_SPIKE, K_EDGE, K_GOLD, K_WHITE = 0, 1, 2, 3, 4, 5, 6
HALF_W = 500               # arena spans z = -500 .. 500
START_X = 150              # where pairs spawn

GAP_X0 = 2400              # the floor ends here: the big launch gap starts
GAP_W = 900                # width of the gap (needs a slingshot to cross)
LAND_X = GAP_X0 + GAP_W
RUNOUT = 900               # flat landing/braking zone before the next hazard
OFF = LAND_X + RUNOUT - 2100   # everything after the gap is shifted by this
FINISH_X = 4300 + OFF      # the finish line
END_X = 4540 + OFF


def build_level():
    B = []

    def box(x0, x1, y0, y1, z0, z1, k):
        B.append((x0, y0, z0, x1, y1, z1, k))

    def pole(x, z, h=320):
        box(x - 25, x + 25, 0, h, z - 25, z + 25, K_POLE)

    # floor, with the big void gap
    box(0, GAP_X0, -40, 0, -HALF_W, HALF_W, K_SOLID)
    box(LAND_X, END_X, -40, 0, -HALF_W, HALF_W, K_SOLID)

    # tall bouncy boundary walls
    box(-40, 0, 0, 700, -HALF_W - 40, HALF_W + 40, K_EDGE)
    box(-40, END_X + 40, 0, 700, -HALF_W - 40, -HALF_W, K_EDGE)
    box(-40, END_X + 40, 0, 700, HALF_W, HALF_W + 40, K_EDGE)
    box(END_X, END_X + 40, 0, 700, -HALF_W, HALF_W, K_EDGE)

    # start line
    box(280, 300, 0, 2, -HALF_W, HALF_W, K_WHITE)

    # A: pole field (x 500..900) - the tether will catch on these
    for i, x in enumerate(range(500, 1100, 200)):
        off = 100 if i % 2 else 0
        for z in (-300, 0, 300):
            pole(x, z + off)

    # B: the launch run. Long flat runway, then a gap too wide to jump normally.
    #    Dock at the gold line, partner runs back to the white line and pulls the
    #    rope tight, lets go, flies past, grabs you, and you jump together.
    box(GAP_X0 - 120, GAP_X0 - 100, 0, 2, -HALF_W, HALF_W, K_GOLD)
    box(GAP_X0 - 1000, GAP_X0 - 980, 0, 2, -HALF_W, HALF_W, K_WHITE)

    # C: spike strips (after a long runout so slingshot speed can bleed off)
    box(2200 + OFF, 2400 + OFF, 0, 30, -HALF_W, HALF_W, K_SPIKE)
    box(2600 + OFF, 2720 + OFF, 0, 30, -HALF_W, -100, K_SPIKE)
    box(2600 + OFF, 2720 + OFF, 0, 30, 100, HALF_W, K_SPIKE)

    # D: S-bend walls - run opposite sides of a wall and the rope wraps its end
    box(3000 + OFF, 3040 + OFF, 0, 220, -HALF_W, 100, K_WALL)
    box(3300 + OFF, 3340 + OFF, 0, 220, -100, HALF_W, K_WALL)
    for x, z in ((3150, 250), (3150, -250), (3450, -300), (3450, 300)):
        pole(x + OFF, z)

    # E: slalom to the finish
    for x, z in ((3800, -250), (3800, 150), (3950, -100), (3950, 300),
                 (4100, -300), (4100, 50)):
        pole(x + OFF, z)

    # finish arch
    pole(FINISH_X, -460, 340)
    pole(FINISH_X, 460, 340)
    box(FINISH_X - 10, FINISH_X + 10, 300, 340, -460, 460, K_GOLD)
    box(FINISH_X - 15, FINISH_X + 15, 0, 2, -HALF_W, HALF_W, K_WHITE)
    return B


BOXES = build_level()
SOLIDS = [b for b in BOXES if b[6] in (K_SOLID, K_POLE, K_WALL, K_EDGE)]
SPIKES = [b for b in BOXES if b[6] == K_SPIKE]
# footprints the tether can wrap around: (x0, z0, x1, z1, y0, y1)
RECTS = [(b[0], b[2], b[3], b[5], b[1], b[4]) for b in BOXES if b[6] in (K_POLE, K_WALL)]
EPS = 0.001


def overlaps(x, y, z, b, grow=0.0):
    return (x - grow < b[3] - EPS and x + SIZE + grow > b[0] + EPS and
            y - grow < b[4] - EPS and y + SIZE + grow > b[1] + EPS and
            z - grow < b[5] - EPS and z + SIZE + grow > b[2] + EPS)


def free_at(x, y, z):
    return not any(overlaps(x, y, z, b) for b in SOLIDS)


def near_solid(p):
    return any(overlaps(p["x"], p["y"], p["z"], b, 3.0) for b in SOLIDS)


def lane_z(lane):
    return ((lane % 7) - 3) * 120.0


# ---------- game state ----------
players = {}   # id -> player dict
clients = {}   # id -> StreamWriter
links = {}     # id -> a rope between two players
groups = []    # lists of player ids joined together by ropes (rebuilt every tick)
finish_events = []      # groups that just finished and are waiting to go back to the start
next_id = 1
next_link = 1
event_seq = 0
event_text = ""
event_kind = "bad"
kick_block = {}         # ip -> monotonic time the block ends
server_load = 0.0       # ms of work per tick (smoothed), shown to players
best_runs = []          # fastest finishes: [{"names", "time", "count"}]
best_groups = []        # most players finished at once: same fields
LOCAL_IPS = {"127.0.0.1", "::1"}
HOST_KEY = os.environ.get("HOST_KEY", "").strip()   # when hosted online: open /?host=<key> to be the host


def clean_name(raw, fallback):
    name = "".join(ch for ch in str(raw) if ch.isprintable()).strip()[:14]
    return name or fallback


def clean_chat(raw):
    text = "".join(ch for ch in str(raw) if ch.isprintable())
    return " ".join(text.split())[:CHAT_MAX]


def new_player(pid, ip="?", host=False):
    return {
        "id": pid, "name": f"P{pid}", "ip": ip, "host": host,
        "x": START_X, "y": 0.0, "z": lane_z(pid),
        "vx": 0.0, "vy": 0.0, "vz": 0.0,
        "on_ground": False, "docked": False, "spin": 0.0, "lean": None,
        "coyote": 0.0, "jump_buf": 0.0, "jump_prev": False, "jump_edge": False,
        "link_prev": False, "link_edge": False, "link_cd": 0.0,
        "rising_jump": False, "grab_cd": 0.0,
        "carried_by": None, "carrying": None, "team": None,
        "fin": False, "fin_time": 0.0,
        "run_start": time.monotonic(), "last_chat": 0.0,
        "color": COLORS[(pid - 1) % len(COLORS)],
        "input": {"mx": 0.0, "mz": 0.0, "jump": False, "dock": False,
                  "grab": False, "link": False},
    }


def center(p):
    return (p["x"] + SIZE / 2, p["y"] + SIZE / 2, p["z"] + SIZE / 2)


def linked_players(p):
    """Everyone p has a rope to."""
    out = []
    for l in links.values():
        if l["a"] == p["id"]:
            o = players.get(l["b"])
        elif l["b"] == p["id"]:
            o = players.get(l["a"])
        else:
            continue
        if o is not None:
            out.append(o)
    return out


def find_link(aid, bid):
    for l in links.values():
        if (l["a"] == aid and l["b"] == bid) or (l["a"] == bid and l["b"] == aid):
            return l
    return None


def group_of(p):
    """The players p is roped together with (including p). Just [p] if alone."""
    for g in groups:
        if p["id"] in g:
            return [players[i] for i in g if i in players]
    return [p]


def names_of(ids):
    ns = [players[i]["name"] for i in ids if i in players]
    if not ns:
        return "?"
    if len(ns) == 1:
        return ns[0]
    if len(ns) == 2:
        return f"{ns[0]} & {ns[1]}"
    if len(ns) == 3:
        return f"{ns[0]}, {ns[1]} & {ns[2]}"
    return f"{ns[0]}, {ns[1]}, {ns[2]} +{len(ns) - 3}"


def compute_groups():
    """Everyone joined by ropes forms a group (p["team"] = lowest id in it).
    Every rope in a group of n players has rest length TETHER_REST / (n - 1)."""
    global groups
    parent = {pid: pid for pid in players}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for l in links.values():
        if l["a"] in parent and l["b"] in parent:
            ra, rb = find(l["a"]), find(l["b"])
            if ra != rb:
                parent[max(ra, rb)] = min(ra, rb)
    comp = {}
    for pid in players:
        comp.setdefault(find(pid), []).append(pid)
    groups = [sorted(m) for m in comp.values() if len(m) > 1]
    groups.sort()
    for p in players.values():
        p["team"] = None
    size = {}
    for g in groups:
        for pid in g:
            players[pid]["team"] = g[0]
            size[pid] = len(g)
    for l in links.values():
        n = size.get(l["a"], 2)
        l["rest"] = max(MIN_REST, TETHER_REST / max(1, n - 1))


def place(p, x, z):
    p["x"], p["y"], p["z"] = x, 0.0, z
    p["vx"] = p["vy"] = p["vz"] = 0.0
    p["on_ground"] = False
    p["docked"] = False
    p["spin"] = 0.0
    p["lean"] = None
    p["carried_by"] = p["carrying"] = None
    p["coyote"] = p["jump_buf"] = 0.0
    p["rising_jump"] = False
    p["fin"] = False
    p["run_start"] = time.monotonic()


def reset_ids(ids):
    """Send these players back to the start line, side by side, and unwind their ropes."""
    ps = [players[i] for i in sorted(ids) if i in players]
    n = len(ps)
    if not n:
        return
    z0 = lane_z(ps[0]["id"])
    for i, p in enumerate(ps):
        z = z0 + (i - (n - 1) / 2) * 56
        place(p, START_X, max(-HALF_W + 20, min(HALF_W - 20 - SIZE, z)))
    idset = {p["id"] for p in ps}
    for l in links.values():
        if l["a"] in idset or l["b"] in idset:
            l["pivots"] = []


def reset_solo(p):
    place(p, START_X, lane_z(p["id"]))


# ---------- messaging helpers ----------
def encode(obj):
    return make_frame(json.dumps(obj, separators=(",", ":")).encode())


def send_to(pid, obj):
    w = clients.get(pid)
    if w is not None and not w.is_closing():
        try:
            w.write(encode(obj))
        except Exception:
            pass


def broadcast_text(text, droppable=False):
    frame = make_frame(text.encode())
    for w in list(clients.values()):
        if w.is_closing():
            continue
        try:
            # A slow connection must never build up a queue of old frames (that is what makes a game
            # feel like it lags more and more). Skip this one - the next frame is fresher anyway.
            if droppable and w.transport.get_write_buffer_size() > 24000:
                continue
            w.write(frame)
        except Exception:
            pass


def broadcast(obj, droppable=False):
    broadcast_text(json.dumps(obj, separators=(",", ":")), droppable)


def notice(pid, text):
    send_to(pid, {"type": "notice", "text": text})


def sys_chat(text):
    broadcast({"type": "chat", "id": 0, "name": "", "color": "#999", "text": text, "sys": True})


def announce(text, kind="bad"):
    global event_seq, event_text, event_kind
    event_seq += 1
    event_text = text
    event_kind = kind
    broadcast({"type": "event", "text": text, "kind": kind})
    print(text)


# ---------- scoreboards ----------
def sort_scores():
    # fastest: quickest time wins, more players wins a tie
    best_runs.sort(key=lambda e: (e["time"], -e["count"]))
    # most players at once: biggest group wins, quicker time wins a tie
    best_groups.sort(key=lambda e: (-e["count"], e["time"]))
    del best_runs[10:]
    del best_groups[10:]


def load_scores():
    try:
        with open(SCORES_FILE) as f:
            data = json.load(f)
        for key, dest, fallback in (("fastest", best_runs, []), ("most", best_groups, data.get("fastest", []))):
            for e in data.get(key, fallback):
                if isinstance(e, dict) and "names" in e and "time" in e:
                    dest.append({"names": str(e["names"])[:60], "time": float(e["time"]),
                                 "count": int(e.get("count", 2))})
        sort_scores()
        print(f"Loaded scores from {SCORES_FILE}")
    except (OSError, ValueError, TypeError):
        pass


def save_scores():
    try:
        with open(SCORES_FILE, "w") as f:
            json.dump({"fastest": best_runs, "most": best_groups}, f)
    except OSError:
        pass


def scores_msg():
    return {"type": "scores", "fastest": best_runs[:5], "most": best_groups[:5]}


def record_finish(ids, secs):
    entry = {"names": names_of(ids), "time": round(secs, 2), "count": len(ids)}
    best_runs.append(dict(entry))
    best_groups.append(dict(entry))
    sort_scores()
    save_scores()
    broadcast(scores_msg())


# ---------- tethering (Q) ----------
def link(a, b):
    """Rope two players together. Returns the new rope (None if they already have one)."""
    global next_link
    if find_link(a["id"], b["id"]) is not None:
        return None
    lid = next_link
    next_link += 1
    t = {"id": lid, "a": a["id"], "b": b["id"], "pivots": [], "rope": [], "len": 0.0, "rest": TETHER_REST}
    links[lid] = t
    compute_groups()
    # roping up while everyone is still behind the start line restarts the run timers
    members = group_of(a)
    if all(p["x"] + SIZE / 2 < START_LINE_X for p in members):
        now = time.monotonic()
        for p in members:
            p["run_start"] = now
    return t


def unlink(t):
    a, b = players.get(t["a"]), players.get(t["b"])
    for p, q in ((a, b), (b, a)):
        if p is not None and q is not None and p["carrying"] == q["id"]:
            detach(p, "drop")
    links.pop(t["id"], None)
    for p in (a, b):
        if p is not None:
            p["spin"] = 0.0
            p["lean"] = None
    compute_groups()


def handle_links():
    """Q toggles a rope to the NEAREST player."""
    for p in list(players.values()):
        if not p["link_edge"] or p["link_cd"] > 0:
            continue
        p["link_cd"] = LINK_COOLDOWN
        pc = center(p)
        near = sorted(((math.dist(pc, center(q)), q) for q in players.values()
                       if q is not p and math.dist(pc, center(q)) <= LINK_RANGE),
                      key=lambda e: e[0])
        if not near:
            notice(p["id"], "Nobody close enough - get next to a player and press Q")
            continue
        q = near[0][1]
        t = find_link(p["id"], q["id"])
        if t is not None:
            unlink(t)
            sys_chat(f"{p['name']} untethered from {q['name']}")
        else:
            link(p, q)
            sys_chat(f"{p['name']} tethered to {q['name']}")


# ---------- kicking (host only) ----------
def kick(target_id, by_id):
    target = players.get(target_id)
    by = players.get(by_id)
    if target is None or by is None or not by["host"] or target_id == by_id or target["host"]:
        return
    kick_block[target["ip"]] = time.monotonic() + KICK_BLOCK_SECONDS
    send_to(target_id, {"type": "kicked", "text": "You were kicked by the host."})
    sys_chat(f"{target['name']} was kicked by the host")
    print(f"Kicked {target['name']} ({target['ip']})")
    w = clients.get(target_id)
    if w is not None:
        w.close()


# ---------- carrying ----------
def detach(c, mode="drop"):
    """Carrier c puts their rider down. mode: drop | throw | jump."""
    r = players.get(c["carrying"])
    c["carrying"] = None
    if r is None:
        return
    r["carried_by"] = None
    r["grab_cd"] = GRAB_COOLDOWN
    px, py, pz = c["x"], c["y"] + SIZE + 2, c["z"]
    if not free_at(px, py, pz):
        px, py, pz = c["x"], c["y"], c["z"]
    r["x"], r["y"], r["z"] = px, py, pz
    r["vx"], r["vy"], r["vz"] = c["vx"], c["vy"], c["vz"]
    r["on_ground"] = False
    r["rising_jump"] = False
    if mode == "throw":
        inp = c["input"]
        mx, mz = inp["mx"], inp["mz"]
        m = math.hypot(mx, mz)
        if m < 0.1:
            sp = math.hypot(c["vx"], c["vz"])
            if sp > 80:
                mx, mz, m = c["vx"], c["vz"], sp
        if m > 0.1:
            r["vx"] = c["vx"] + mx / m * THROW_X
            r["vz"] = c["vz"] + mz / m * THROW_X
            r["vy"] = max(c["vy"], 0.0) + THROW_Y
    elif mode == "jump":
        r["vy"] = JUMP_SPEED


def handle_carry():
    # let go of the grab key -> throw whoever you were carrying
    for c in list(players.values()):
        if c["carrying"] is not None and not c["input"]["grab"]:
            detach(c, "throw")
    # a rider pressing jump leaps off the carrier's head
    for r in list(players.values()):
        if r["carried_by"] is not None and r["jump_edge"]:
            c = players.get(r["carried_by"])
            if c is not None:
                detach(c, "jump")
    # holding grab near a tethered friend picks them up (so you can catch them mid-flight)
    for c in list(players.values()):
        if not c["input"]["grab"] or c["carrying"] is not None or c["carried_by"] is not None:
            continue
        q, qd = None, GRAB_RANGE
        for o in linked_players(c):
            if o["carried_by"] is not None or o["carrying"] is not None or o["grab_cd"] > 0:
                continue
            d = math.dist((o["x"], o["y"], o["z"]), (c["x"], c["y"], c["z"]))
            if d <= qd:
                q, qd = o, d
        if q is not None:
            q["carried_by"] = c["id"]
            q["docked"] = False
            c["carrying"] = q["id"]
            q["x"], q["y"], q["z"] = c["x"], c["y"], c["z"]
            q["vx"], q["vy"], q["vz"] = c["vx"], c["vy"], c["vz"]


def sync_riders():
    for r in players.values():
        if r["carried_by"] is not None:
            c = players.get(r["carried_by"])
            if c is None:
                r["carried_by"] = None
                continue
            r["x"], r["y"], r["z"] = c["x"], c["y"], c["z"]
            r["vx"], r["vy"], r["vz"] = c["vx"], c["vy"], c["vz"]
            r["on_ground"] = False
            r["docked"] = False


# ---------- the rope: wraps around poles and walls, any number of times ----------
def seg_rect_t(ax, az, bx, bz, x0, z0, x1, z1):
    """Liang-Barsky: portion (t0, t1) of the segment inside the rectangle, or None."""
    dx, dz = bx - ax, bz - az
    t0, t1 = 0.0, 1.0
    for p, q in ((-dx, ax - x0), (dx, x1 - ax), (-dz, az - z0), (dz, z1 - az)):
        if abs(p) < 1e-9:
            if q < 0:
                return None
        else:
            t = q / p
            if p < 0:
                if t > t1:
                    return None
                if t > t0:
                    t0 = t
            else:
                if t < t0:
                    return None
                if t < t1:
                    t1 = t
    return (t0, t1) if t0 < t1 else None


def seg_hits(ax, az, bx, bz, r, ya=None, yb=None, shrink=1.5):
    res = seg_rect_t(ax, az, bx, bz, r[0] + shrink, r[1] + shrink, r[2] - shrink, r[3] - shrink)
    if res is None:
        return False
    if ya is not None:
        y = ya + (yb - ya) * (res[0] + res[1]) / 2
        if y > r[5] or y < r[4] - 10:     # rope passes over the top of it
            return False
    return True


def first_rect_hit(s, e, ya=None, yb=None, shrink=1.5):
    """Index of the pole/wall the segment s->e runs into first, or None."""
    minx, maxx = (s[0], e[0]) if s[0] < e[0] else (e[0], s[0])
    minz, maxz = (s[1], e[1]) if s[1] < e[1] else (e[1], s[1])
    best, best_t = None, 2.0
    for ri, r in enumerate(RECTS):
        if r[2] < minx or r[0] > maxx or r[3] < minz or r[1] > maxz:
            continue
        res = seg_rect_t(s[0], s[1], e[0], e[1], r[0] + shrink, r[1] + shrink,
                         r[2] - shrink, r[3] - shrink)
        if res is None:
            continue
        if ya is not None:
            y = ya + (yb - ya) * (res[0] + res[1]) / 2
            if y > r[5] or y < r[4] - 10:
                continue
        if res[0] < best_t:
            best, best_t = ri, res[0]
    return best


def find_detour(s, e, r):
    """Shortest way around rectangle r for the segment s->e (via 1 or 2 corners)."""
    o = ROPE_OUTSET
    C = [(r[0] - o, r[1] - o), (r[2] + o, r[1] - o), (r[2] + o, r[3] + o), (r[0] - o, r[3] + o)]

    def clear(p, q):
        return not seg_hits(p[0], p[1], q[0], q[1], r)

    best = None
    for c in C:
        if clear(s, c) and clear(c, e):
            ln = math.dist(s, c) + math.dist(c, e)
            if best is None or ln < best[0]:
                best = (ln, [c])
    for i in range(4):
        for ci, cj in ((C[i], C[(i + 1) % 4]), (C[(i + 1) % 4], C[i])):
            if clear(s, ci) and clear(ci, cj) and clear(cj, e):
                ln = math.dist(s, ci) + math.dist(ci, cj) + math.dist(cj, e)
                if best is None or ln < best[0]:
                    best = (ln, [ci, cj])
    return best[1] if best else None


def cross2(ox, oz, ax, az, bx, bz):
    return (ax - ox) * (bz - az) - (az - oz) * (bx - ax)


def rope_points(t, a, b):
    ax, ay, az = a["x"] + SIZE / 2, a["y"] + SIZE / 2, a["z"] + SIZE / 2
    bx, by, bz = b["x"] + SIZE / 2, b["y"] + SIZE / 2, b["z"] + SIZE / 2
    pts = [(ax, az)] + [(q["x"], q["z"]) for q in t["pivots"]] + [(bx, bz)]
    cum = [0.0]
    for i in range(1, len(pts)):
        cum.append(cum[-1] + math.dist(pts[i - 1], pts[i]))
    tot = cum[-1] or 1.0
    ys = [ay + (by - ay) * c / tot for c in cum]
    return pts, ys, cum[-1]


def update_rope(t, a, b):
    """Unwrap straightened pivots, wrap new ones, return (pts, ys, xz_length).

    Pivots are fixed points, so only the two moving ends of the rope can change:
    unwrapping is checked from both ends inwards, and wrapping only needs the
    first and last segments (plus any segments a new wrap just created).
    There is no practical limit on how many times it wraps."""
    piv = t["pivots"]
    A = (a["x"] + SIZE / 2, a["z"] + SIZE / 2)
    B = (b["x"] + SIZE / 2, b["z"] + SIZE / 2)

    def P(k):
        if k == 0:
            return A
        if k == len(piv) + 1:
            return B
        q = piv[k - 1]
        return (q["x"], q["z"])

    def not_needed(j):
        prev, cur, nxt = P(j), P(j + 1), P(j + 2)
        n1, n2 = math.dist(prev, cur), math.dist(cur, nxt)
        if n1 < 0.5 or n2 < 0.5:
            return True                      # duplicate point
        sin = cross2(prev[0], prev[1], cur[0], cur[1], nxt[0], nxt[1]) / (n1 * n2)
        if sin * piv[j]["s"] < -0.01:        # rope now bends the other way
            return not seg_hits(prev[0], prev[1], nxt[0], nxt[1], RECTS[piv[j]["r"]])
        return False

    while piv:
        if not_needed(0):
            piv.pop(0)
        elif not_needed(len(piv) - 1):
            piv.pop()
        else:
            break

    todo = [0, len(piv)]                     # segment i runs from P(i) to P(i+1)
    steps = 0
    while todo and steps < 60 and len(piv) < MAX_PIVOTS:
        steps += 1
        i = todo.pop()
        pts, ys, _ = rope_points(t, a, b)
        if i >= len(pts) - 1:
            continue
        s, e = pts[i], pts[i + 1]
        ri = first_rect_hit(s, e, ys[i], ys[i + 1])
        if ri is None:
            continue
        detour = find_detour(s, e, RECTS[ri])
        if not detour:
            continue
        k = len(detour)
        piv[i:i] = [{"x": c[0], "z": c[1], "r": ri, "s": 0} for c in detour]
        pts2, _, _ = rope_points(t, a, b)
        for q in range(i, i + k):
            p0, p1, p2 = pts2[q], pts2[q + 1], pts2[q + 2]
            piv[q]["s"] = 1 if cross2(p0[0], p0[1], p1[0], p1[1], p2[0], p2[1]) >= 0 else -1
        todo = [j + k if j > i else j for j in todo]
        todo.extend(range(i, i + k + 1))

    return rope_points(t, a, b)


def apply_tethers(dt):
    for p in players.values():
        p["lean"] = None
        p["spin"] = 0.0

    def unit(frm, to):
        dx, dy, dz = to[0] - frm[0], to[1] - frm[1], to[2] - frm[2]
        d = math.sqrt(dx * dx + dy * dy + dz * dz) or 1.0
        return dx / d, dy / d, dz / d

    lean_best = {}
    for t in links.values():
        a, b = players.get(t["a"]), players.get(t["b"])
        if not a or not b:
            continue
        rest = t["rest"]
        ca = (a["x"] + SIZE / 2, a["y"] + SIZE / 2, a["z"] + SIZE / 2)
        cb = (b["x"] + SIZE / 2, b["y"] + SIZE / 2, b["z"] + SIZE / 2)
        if a["carried_by"] == b["id"] or b["carried_by"] == a["id"]:
            t["pivots"] = []
            t["rope"] = [list(ca), list(cb)]
            t["len"] = 0.0
            continue

        pts, ys, xz_len = update_rope(t, a, b)
        length = math.hypot(xz_len, cb[1] - ca[1])
        t["len"] = length
        t["rope"] = [[round(p[0]), round(y), round(p[1])] for p, y in zip(pts, ys)]

        # spin: angular velocity of each end around the pole it is wrapped on
        if t["pivots"]:
            for who, pv in ((a, t["pivots"][0]), (b, t["pivots"][-1])):
                rx, rz = who["x"] + SIZE / 2 - pv["x"], who["z"] + SIZE / 2 - pv["z"]
                r2 = rx * rx + rz * rz
                if r2 > 400:
                    who["spin"] = max(-12.0, min(12.0, -(rx * who["vz"] - rz * who["vx"]) / r2))

        if length <= rest or (a["docked"] and b["docked"]):
            continue

        ua = unit(ca, (pts[1][0], ys[1], pts[1][1]))
        ub = unit(cb, (pts[-2][0], ys[-2], pts[-2][1]))
        stretch = length - rest
        # a taut rope lets you lean into it: running away from it is much stronger
        for who, u in ((a, ua), (b, ub)):
            h = math.hypot(u[0], u[2])
            if h > 0.05 and stretch > lean_best.get(who["id"], -1.0):
                lean_best[who["id"]] = stretch
                who["lean"] = (u[0] / h, u[2] / h)
        rel = -(a["vx"] * ua[0] + a["vy"] * ua[1] + a["vz"] * ua[2]) \
              - (b["vx"] * ub[0] + b["vy"] * ub[1] + b["vz"] * ub[2])
        acc = min(TETHER_MAX_ACC, TETHER_K * stretch + TETHER_DAMP * max(rel, 0.0))
        share = 1.0 if (a["docked"] or b["docked"]) else 0.5
        if not a["docked"]:
            a["vx"] += ua[0] * acc * share * dt
            a["vy"] += ua[1] * acc * share * dt
            a["vz"] += ua[2] * acc * share * dt
        if not b["docked"]:
            b["vx"] += ub[0] * acc * share * dt
            b["vy"] += ub[1] * acc * share * dt
            b["vz"] += ub[2] * acc * share * dt


# ---------- movement ----------
def update_edges(p, dt):
    """Per-tick bookkeeping for jump / link presses (runs for every player)."""
    inp = p["input"]
    edge = inp["jump"] and not p["jump_prev"]
    p["jump_edge"] = edge
    p["jump_prev"] = inp["jump"]
    p["jump_buf"] = JUMP_BUFFER if edge else max(0.0, p["jump_buf"] - dt)
    p["coyote"] = COYOTE if p["on_ground"] else max(0.0, p["coyote"] - dt)
    p["grab_cd"] = max(0.0, p["grab_cd"] - dt)
    p["link_edge"] = inp["link"] and not p["link_prev"]
    p["link_prev"] = inp["link"]
    p["link_cd"] = max(0.0, p["link_cd"] - dt)


def step_player(p, dt):
    inp = p["input"]

    # docking: hold the dock key while touching something solid to lock in place
    p["docked"] = bool(inp["dock"] and (p["docked"] or near_solid(p)))
    if p["docked"]:
        p["vx"] = p["vy"] = p["vz"] = 0.0
        return

    on = p["on_ground"]
    vx, vy, vz = p["vx"], p["vy"], p["vz"]
    mx, mz = inp["mx"], inp["mz"]
    m = math.hypot(mx, mz)
    if m > 1.0:
        mx, mz, m = mx / m, mz / m, 1.0

    # --- icy running ---
    fr = (GROUND_FRICTION if on else AIR_FRICTION) * dt
    over = (OVERSPEED_GROUND if on else OVERSPEED_AIR) * dt
    if m > 0.05:
        ux, uz = mx / m, mz / m
        accel = (GROUND_ACCEL if on else AIR_ACCEL) * dt
        lean = p["lean"]
        if lean is not None and ux * lean[0] + uz * lean[1] < LEAN_DOT:
            accel *= LEAN_BOOST               # leaning into a taut tether: pull hard
        target = MOVE_SPEED * m               # your own running never exceeds this
        s = vx * ux + vz * uz
        if s < target:
            add = min(accel, target - s)
            vx += ux * add
            vz += uz * add
            s += add
        # sideways drift bleeds off slowly; excess speed along your heading too
        lx, lz = vx - s * ux, vz - s * uz
        lm = math.hypot(lx, lz)
        if lm > 0:
            k = max(0.0, lm - fr * 0.8) / lm
            lx, lz = lx * k, lz * k
        if s > MOVE_SPEED:
            s = max(MOVE_SPEED, s - over)
        vx, vz = s * ux + lx, s * uz + lz
    else:
        sp = math.hypot(vx, vz)
        if sp > 0:
            drag = fr + (over if sp > MOVE_SPEED else 0.0)
            k = max(0.0, sp - drag) / sp
            vx, vz = vx * k, vz * k

    # --- fluid jumping: buffered, forgiving, hold to keep bouncing ---
    wants_jump = inp["jump"] or p["jump_buf"] > 0
    if wants_jump and (on or p["coyote"] > 0):
        vy = JUMP_SPEED
        p["coyote"] = 0.0
        p["jump_buf"] = 0.0
        p["rising_jump"] = True
    elif p["rising_jump"] and not inp["jump"] and vy > 0:
        vy = min(vy, JUMP_SPEED * JUMP_CUT)       # short-hop if you let go early
        p["rising_jump"] = False
    if vy <= 0:
        p["rising_jump"] = False

    vy = max(vy - GRAVITY * (FALL_MULT if vy < 0 else 1.0) * dt, -MAX_FALL)
    hs = math.hypot(vx, vz)
    if hs > MAX_SPEED:
        vx, vz = vx * MAX_SPEED / hs, vz * MAX_SPEED / hs
    vy = min(vy, MAX_SPEED)

    # --- move in small sub-steps (so fast slingshots can't tunnel through walls) ---
    steps = max(1, min(10, int(max(abs(vx), abs(vz), abs(vy)) * dt / 20.0) + 1))
    sdt = dt / steps
    landed = False
    for _ in range(steps):
        for axis in (0, 2):
            v = vx if axis == 0 else vz
            key = "x" if axis == 0 else "z"
            p[key] += v * sdt
            hit = False
            for b in SOLIDS:
                if overlaps(p["x"], p["y"], p["z"], b):
                    lo, hi = (b[0], b[3]) if axis == 0 else (b[2], b[5])
                    if v > 0:
                        p[key] = lo - SIZE
                    elif v < 0:
                        p[key] = hi
                    else:
                        p[key] = lo - SIZE if p[key] + SIZE / 2 < (lo + hi) / 2 else hi
                    hit = True
            if hit:
                v = -v * WALL_BOUNCE if abs(v) > BOUNCE_MIN else 0.0
                if axis == 0:
                    vx = v
                else:
                    vz = v

        p["y"] += vy * sdt
        for b in SOLIDS:
            if overlaps(p["x"], p["y"], p["z"], b):
                if vy < 0:
                    p["y"] = b[4]
                    landed = True
                elif vy > 0:
                    p["y"] = b[1] - SIZE
                vy = 0.0
    p["on_ground"] = landed

    p["vx"], p["vy"], p["vz"] = vx, vy, vz


def hit_hazard(p):
    if p["y"] < VOID_Y or p["x"] < -60 or abs(p["z"]) > HALF_W + 60:
        return "fell out of the arena"
    for b in SPIKES:
        if (p["x"] + 6 < b[3] and p["x"] + SIZE - 6 > b[0] and
                p["z"] + 6 < b[5] and p["z"] + SIZE - 6 > b[2] and
                p["y"] < b[4] - 4 and p["y"] + SIZE > b[1]):
            return "hit a spike"
    return None


def team_progress(p):
    return max(0.0, min(1.0, (p["x"] + SIZE / 2 - START_X) / (FINISH_X - START_X)))


def run_time(p, now):
    if p["fin"]:
        return p["fin_time"]
    return now - p["run_start"]


def tick(dt):
    """One step of the whole game."""
    for p in players.values():
        update_edges(p, dt)
    handle_links()
    compute_groups()
    handle_carry()
    apply_tethers(dt)
    for p in players.values():
        if p["carried_by"] is None:
            step_player(p, dt)
    sync_riders()

    # hazards: anyone touching one sends their whole roped group back to the start
    for p in list(players.values()):
        if p["fin"]:
            continue
        why = hit_hazard(p)
        if why:
            g = [q["id"] for q in group_of(p)]
            if len(g) > 1:
                announce(f"{p['name']} {why}! {names_of(g)} back to the start")
                reset_ids(g)
            else:
                announce(f"{p['name']} {why}! Back to the start")
                reset_solo(p)

    # finish: the WHOLE group over the line -> only that group resets
    now = time.monotonic()
    for g in groups:
        ps = [players[i] for i in g if i in players]
        if len(ps) < 2 or any(p["fin"] for p in ps):
            continue
        if all(p["x"] + SIZE / 2 >= FINISH_X for p in ps):
            secs = now - min(p["run_start"] for p in ps)
            for p in ps:
                p["fin"] = True
                p["fin_time"] = secs
            finish_events.append({"ids": list(g), "until": now + FINISH_PAUSE})
            record_finish(g, secs)
            announce(f"{names_of(g)} finished in {secs:.1f}s!", "good")
            sys_chat(f"{names_of(g)} finished in {secs:.1f}s!")
    for ev in list(finish_events):
        if now >= ev["until"]:
            finish_events.remove(ev)
            reset_ids(ev["ids"])


def topo_obj():
    """Everything that only changes occasionally: who is here, rope shapes, who is roped to whom."""
    return {
        "type": "topo",
        "players": [[p["id"], p["name"], p["color"]] for p in players.values()],
        "ropes": [[t["id"], t["a"], t["b"], round(t["rest"]),
                   [[round(q["x"]), round(q["z"])] for q in t["pivots"]]] for t in links.values()],
        "groups": [[g, names_of(g)] for g in groups],
    }


def build_state(now):
    """The part that changes every update: one short row per player."""
    return {
        "type": "s",
        "p": [[p["id"], round(p["x"]), round(p["y"]), round(p["z"]),
               round(p["vx"] / 10), round(p["vy"] / 10), round(p["vz"] / 10),
               (1 if p["docked"] else 0) | (2 if p["fin"] else 0),
               p["carried_by"] or 0, round(p["spin"] * 10)]
              for p in players.values()],
    }


def dumps(obj):
    return json.dumps(obj, separators=(",", ":"))


last_topo = None
last_state = None
last_state_at = 0.0
last_timers_at = 0.0


def current_topo():
    global last_topo
    if last_topo is None:
        last_topo = dumps(topo_obj())
    return last_topo


def send_world(now):
    global last_topo, last_state, last_state_at, last_timers_at
    topo = dumps(topo_obj())
    if topo != last_topo:                  # rare: someone joined/left/renamed, a rope wrapped, groups changed
        last_topo = topo
        broadcast_text(topo)
    st = dumps(build_state(now))
    if st != last_state or now - last_state_at > 1.0:      # nothing moved -> send nothing (1s keepalive)
        last_state, last_state_at = st, now
        broadcast_text(st, droppable=True)
    if now - last_timers_at >= 1.0:        # run timers: once a second, the page counts up in between
        last_timers_at = now
        broadcast({"type": "t", "a": [[p["id"], round(run_time(p, now), 1), 1 if p["fin"] else 0]
                                      for p in players.values()]})


async def game_loop():
    global server_load
    step = 1 / TICK_RATE
    last = next_t = time.monotonic()
    n = 0
    while True:
        t0 = time.monotonic()
        elapsed = t0 - last
        last = t0
        # normally a fixed step; if we have fallen behind, take a bigger one so game speed stays real
        dt = step if elapsed < step * 1.5 else min(elapsed, MAX_DT)
        try:
            tick(dt)
            n += 1
            if n % STATE_EVERY == 0:
                send_world(t0)
        except Exception:
            traceback.print_exc()
        server_load = server_load * 0.95 + (time.monotonic() - t0) * 1000 * 0.05
        next_t += step
        delay = next_t - time.monotonic()
        if delay < -0.1:                 # fell far behind: don't try to catch up
            next_t = time.monotonic()
        await asyncio.sleep(max(0.0, delay))


# ---------- minimal WebSocket helpers ----------
def find_index():
    """Look for index.html next to server.py, or in a public/ subfolder."""
    for candidate in (os.path.join(HERE, "index.html"),
                      os.path.join(HERE, "public", "index.html")):
        if os.path.isfile(candidate):
            return candidate
    return None


def make_frame(payload: bytes, opcode: int = 1) -> bytes:
    n = len(payload)
    header = bytes([0x80 | opcode])
    if n < 126:
        header += bytes([n])
    elif n < 65536:
        header += bytes([126]) + struct.pack(">H", n)
    else:
        header += bytes([127]) + struct.pack(">Q", n)
    return header + payload


async def read_frame(reader):
    b1, b2 = await reader.readexactly(2)
    opcode = b1 & 0x0F
    masked = b2 & 0x80
    length = b2 & 0x7F
    if length == 126:
        length = struct.unpack(">H", await reader.readexactly(2))[0]
    elif length == 127:
        length = struct.unpack(">Q", await reader.readexactly(8))[0]
    mask = await reader.readexactly(4) if masked else b""
    data = await reader.readexactly(length)
    if masked:
        data = bytes(b ^ mask[i % 4] for i, b in enumerate(data))
    return opcode, data


def num(v, lo=-1.0, hi=1.0):
    try:
        v = float(v)
    except (TypeError, ValueError):
        return 0.0
    if v != v:
        return 0.0
    return max(lo, min(hi, v))


# ---------- connection handler ----------
async def handle(reader, writer):
    global next_id
    try:
        raw = await reader.readuntil(b"\r\n\r\n")
    except Exception:
        writer.close()
        return

    lines = raw.decode("latin-1").split("\r\n")
    parts = lines[0].split(" ")
    full_path = parts[1] if len(parts) > 1 else "/"
    path, _, query = full_path.partition("?")
    host_key = ""
    for kv in query.split("&"):
        if kv.startswith("host="):
            host_key = unquote_plus(kv[5:]).strip()
    headers = {}
    for line in lines[1:]:
        if ":" in line:
            k, v = line.split(":", 1)
            headers[k.strip().lower()] = v.strip()

    # Plain HTTP: serve the game page
    if headers.get("upgrade", "").lower() != "websocket":
        extra = ""
        if path in ("/", "/index.html"):
            index_path = find_index()
            if index_path:
                with open(index_path, "rb") as f:
                    body = f.read()
                status = "200 OK"
                if "gzip" in headers.get("accept-encoding", "").lower():
                    body = gzip.compress(body, 6)
                    extra = "Content-Encoding: gzip\r\nVary: Accept-Encoding\r\n"
            else:
                body = ("Could not find index.html. Put it in the same folder as server.py "
                        f"(looked in: {HERE}).").encode()
                status = "500 Internal Server Error"
        else:
            body, status = b"Not found", "404 Not Found"
        writer.write(
            f"HTTP/1.1 {status}\r\nContent-Type: text/html; charset=utf-8\r\n"
            f"{extra}Content-Length: {len(body)}\r\nConnection: close\r\n\r\n".encode() + body
        )
        await writer.drain()
        writer.close()
        return

    # Who is this? The host is whoever connects from this very machine.
    # (If the connection came through a tunnel/proxy, nobody is the host.)
    peer = writer.get_extra_info("peername")
    peer_ip = peer[0] if peer else "?"
    proxied = any(h in headers for h in ("x-forwarded-for", "cf-connecting-ip", "forwarded", "x-real-ip"))
    ip = peer_ip
    if proxied:
        ip = (headers.get("x-forwarded-for") or headers.get("cf-connecting-ip")
              or headers.get("x-real-ip") or peer_ip).split(",")[0].strip()
    is_host = (not proxied) and peer_ip in LOCAL_IPS
    host_status = "local" if is_host else "none"
    if not is_host and host_key:
        if not HOST_KEY:
            host_status = "server_no_key"
        elif hmac.compare_digest(host_key.encode(), HOST_KEY.encode()):
            is_host, host_status = True, "ok"
        else:
            host_status = "wrong"
        print(f"Host key attempt from {ip}: {host_status}")

    # WebSocket handshake
    accept = base64.b64encode(
        hashlib.sha1((headers["sec-websocket-key"] + WS_GUID).encode()).digest()
    ).decode()
    writer.write(
        ("HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\n"
         f"Connection: Upgrade\r\nSec-WebSocket-Accept: {accept}\r\n\r\n").encode()
    )
    await writer.drain()

    sock = writer.get_extra_info("socket")
    if sock is not None:
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)

    blocked_for = kick_block.get(ip, 0) - time.monotonic()
    if blocked_for > 0 and not is_host:
        writer.write(make_frame(json.dumps({
            "type": "kicked",
            "text": f"You were kicked by the host. You can rejoin in {int(blocked_for) + 1}s."}).encode()))
        try:
            await writer.drain()
        except Exception:
            pass
        writer.close()
        return

    pid = next_id
    next_id += 1
    players[pid] = new_player(pid, ip, is_host)
    clients[pid] = writer
    print(f"Player {pid} joined from {ip}{' (host)' if is_host else ''} ({len(players)} online)")

    writer.write(make_frame(json.dumps({
        "type": "welcome", "id": pid, "size": SIZE, "host": is_host, "host_status": host_status,
        "boxes": [list(b) for b in BOXES],
        "start_x": START_X, "finish_x": FINISH_X, "half_w": HALF_W,
        "tether_rest": TETHER_REST, "grab_range": GRAB_RANGE, "link_range": LINK_RANGE,
        "scores": scores_msg(),
    }).encode()))
    writer.write(make_frame(dumps(topo_obj()).encode()))

    try:
        while True:
            opcode, data = await read_frame(reader)
            if opcode == 8:                      # close
                break
            elif opcode == 9:                    # ping -> pong
                writer.write(make_frame(data, 10))
            elif opcode == 1:                    # text message
                try:
                    msg = json.loads(data.decode())
                except (ValueError, UnicodeDecodeError):
                    continue
                if not isinstance(msg, dict):
                    continue
                me = players.get(pid)
                if me is None:
                    break
                kind = msg.get("type")
                if kind == "input":
                    me["input"] = {
                        "mx": num(msg.get("mx")), "mz": num(msg.get("mz")),
                        "jump": bool(msg.get("jump")),
                        "dock": bool(msg.get("dock")),
                        "grab": bool(msg.get("grab")),
                        "link": bool(msg.get("link")),
                    }
                elif kind == "name":
                    old = me["name"]
                    me["name"] = clean_name(msg.get("name", ""), f"P{pid}")
                    if me["name"] != old:
                        print(f"{old} is now called {me['name']}")
                elif kind == "ping":
                    t = msg.get("t")
                    if isinstance(t, (int, float)) and not isinstance(t, bool):
                        send_to(pid, {"type": "pong", "t": t, "load": round(server_load, 1)})
                elif kind == "chat":
                    text = clean_chat(msg.get("text", ""))
                    now = time.monotonic()
                    if text and now - me["last_chat"] >= CHAT_COOLDOWN:
                        me["last_chat"] = now
                        broadcast({"type": "chat", "id": pid, "name": me["name"],
                                   "color": me["color"], "text": text})
                elif kind == "kick":
                    if me["host"]:
                        try:
                            kick(int(msg.get("id")), pid)
                        except (TypeError, ValueError):
                            pass
    except (asyncio.IncompleteReadError, ConnectionError):
        pass
    except Exception:
        traceback.print_exc()
    finally:
        me = players.get(pid)
        name = me["name"] if me else f"P{pid}"
        if me is not None:
            if me["carrying"] is not None:
                detach(me, "drop")
            if me["carried_by"] is not None:
                carrier = players.get(me["carried_by"])
                if carrier is not None:
                    carrier["carrying"] = None
            for t in [t for t in links.values() if pid in (t["a"], t["b"])]:
                unlink(t)
        players.pop(pid, None)
        clients.pop(pid, None)
        compute_groups()
        print(f"{name} left ({len(players)} online)")
        writer.close()


def route_ip(target):
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect((target, 1))             # no packet is actually sent
        return s.getsockname()[0]
    except OSError:
        return None
    finally:
        s.close()


def lan_ips():
    """Every private IPv4 address this machine has (first one is the main route)."""
    found = []
    for target in ("10.255.255.255", "172.16.255.255", "192.168.255.255", "8.8.8.8"):
        ip = route_ip(target)
        if ip and ip not in found and not ip.startswith("127."):
            found.append(ip)
    try:
        for info in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            ip = info[4][0]
            if ip not in found and not ip.startswith(("127.", "169.254.")):
                found.append(ip)
    except OSError:
        pass
    return found


async def main():
    load_scores()
    ips = lan_ips()
    LOCAL_IPS.update(ips)
    server = await asyncio.start_server(handle, "0.0.0.0", PORT)
    index_path = find_index()
    print(f"\nClient page: {index_path or 'NOT FOUND - put index.html next to server.py'}")
    print(f"Game server running on port {PORT}")
    print(f"  You (host): http://localhost:{PORT}")
    for i, ip in enumerate(ips):
        print(f"  Friends{'' if i == 0 else ' (other address)'}:  http://{ip}:{PORT}")
    print("\nPress Ctrl+C to stop.\n")
    async with server:
        await asyncio.gather(server.serve_forever(), game_loop())


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        print("\nStopped.")
