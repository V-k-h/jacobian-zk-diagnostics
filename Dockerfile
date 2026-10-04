# Reproduction container for the paper's measured tables and certificate
# study ("make check", "make tables", "make study"). The Lean kernel checks
# and the circom/Picus corpus study are host-side extras; see README.md.
FROM golang:1.25-bookworm
RUN apt-get update && apt-get install -y --no-install-recommends \
    python3 rsync && rm -rf /var/lib/apt/lists/*
WORKDIR /artifact
COPY . .
# Warm the Go module cache so runs are network-free afterwards.
RUN cd frontends/gnark && go mod download \
 && cd ../../study/exporter && go mod download \
 && cd ../exporter-patched && go mod download \
 && cd ../exporter-advisory && go mod download
CMD ["bash", "run_all.sh"]
