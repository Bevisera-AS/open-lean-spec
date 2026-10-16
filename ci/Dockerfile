# Pinned build environment for lean-spec CI.
#
# There is no maintained upstream Lean 4 image: leanprovercommunity/lean4 was last
# pushed 2024-08-20, and leanprover/lean4#6996 (a request to maintain an official
# one) was closed as not planned. So the environment is built here and pinned by
# digest, which also makes it an identified artefact rather than "whatever elan
# resolved that morning".
#
# Build locally:
#   docker build --build-arg LEAN_TOOLCHAIN="$(cat lean-toolchain)" -t lean-spec-ci ci
#
# In CI the `build-ci-image` job passes the argument from lean-toolchain, so the
# image can never drift from the toolchain the project actually pins.

FROM debian:bookworm-slim

ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.35.0

# bubblewrap: `lake check` sandboxes the code it checks with `bwrap`.
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      ca-certificates \
      curl \
      git \
      build-essential \
      bubblewrap \
 && rm -rf /var/lib/apt/lists/* \
 && mkdir -p /run/user
# `lake check` binds /run/user into its read-only sandbox root; bwrap fails with
# "Can't mkdir /run/user" when the image lacks it.

ENV ELAN_HOME=/opt/elan
ENV PATH=/opt/elan/bin:$PATH

RUN curl -sSfL https://elan.lean-lang.org/elan-init.sh \
      | sh -s -- -y --default-toolchain "$LEAN_TOOLCHAIN" \
 && elan --version \
 && lean --version \
 && lake --version

WORKDIR /work
