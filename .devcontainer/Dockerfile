# Force platform to linux/amd64; there is no Z3 release for linux/arm64:
# https://github.com/Z3Prover/z3/issues/7201
FROM --platform=linux/amd64 mcr.microsoft.com/devcontainers/java:21-bullseye

RUN wget -qO- https://github.com/apalache-mc/apalache/releases/download/v0.44.11/apalache.tgz | tar xz -C /opt/
ENV PATH="/opt/apalache/bin/:${PATH}"