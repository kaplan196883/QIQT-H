# QIQT-H — pinned, from-source verification container.
#
# For reviewers who (reasonably) don't want to run `bash verify/verify.sh` on
# their own machine. This rebuilds the WHOLE stack — Lean, Mathlib, the project —
# from source at the exact toolchain + manifest revisions pinned in the repo, then
# runs the verification capsule (clean-room rebuild + independent kernel re-check +
# axiom audit) and prints the claim card.
#
#   docker build -t qiqt-verify -f verify/Dockerfile .
#   docker run --rm qiqt-verify
#
# ⚠ This is a FULL Mathlib + project build from source. Expect it to take on the
#    order of an hour of CPU and several GB of RAM/disk — that thoroughness is the
#    point. For a faster check, run `bash verify/verify.sh` locally (it reuses the
#    pinned Mathlib build) instead.
#
# Nothing but the base image, the pinned source in this repo, and your CPU is trusted.

FROM ubuntu:24.04

RUN apt-get update && apt-get install -y --no-install-recommends \
      curl git ca-certificates build-essential \
    && rm -rf /var/lib/apt/lists/*

# elan (the Lean toolchain manager); the exact lean4 version is pinned by
# lean/mathlib/lean-toolchain inside the repo, so elan installs it automatically.
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

COPY . /qiqt
WORKDIR /qiqt/lean/mathlib

# Builds Mathlib + the QIQTH project from source at the pinned revisions (slow).
RUN lake build QIQTH

# Clean-room re-check + axiom audit + claim card.
CMD ["bash", "/qiqt/verify/verify.sh"]
