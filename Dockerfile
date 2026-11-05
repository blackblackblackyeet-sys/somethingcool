FROM python:3.12-slim
WORKDIR /app
COPY server.py index.html ./
ENV PORT=8080
CMD ["python3", "-u", "server.py"]
