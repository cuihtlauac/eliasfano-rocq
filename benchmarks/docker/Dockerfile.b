FROM eliasfano-bench-base:latest

# Copy task files and build configuration
COPY --chown=vscode:vscode tasks/b/ /home/vscode/task/

# Pre-build EliasFanoSpec.vo and EliasFano.vo
WORKDIR /home/vscode/task
RUN eval $(opam env) && dune build theories/EliasFano.vo

# Workspace is where the agent writes code
USER root
RUN mkdir -p /workspace && chown vscode:vscode /workspace
USER vscode

RUN mkdir -p /workspace/theories && \
    cp theories/EliasFanoSpec.v /workspace/theories/ && \
    cp theories/EliasFano.v /workspace/theories/ && \
    cp theories/EliasFanoInt63_skeleton.v /workspace/theories/EliasFanoInt63.v && \
    cp theories/dune /workspace/theories/ && \
    cp dune-project /workspace/ && \
    cp -r _build /workspace/

WORKDIR /workspace
