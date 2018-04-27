# Create a Docker image that is ready to run Verdi tests,
# using Coq 8.7.

# Use Ubuntu LTS version.
FROM ubuntu:xenial
MAINTAINER Karl Palmskog <palmskog@gmail.com>

# According to
# https://docs.docker.com/engine/userguide/eng-image/dockerfile_best-practices/:
#  * Put "apt-get update" and "apt-get install" in the same RUN command.
#  * Do not run "apt-get upgrade"; instead get upstream to update.
RUN apt-get -qqy update \
&& apt-get -qqy install \
  software-properties-common \
  git \
  gnuplot \
  gawk \
  make \
  m4 \
  aspcud \
  ocaml \
  opam \
&& apt-get clean \
&& rm -rf /var/lib/apt/lists/* \
&& opam init --compiler=4.05.0 --yes --auto-setup \
&& eval `opam config env` \
&& opam repo add coq-released https://coq.inria.fr/opam/released \
&& opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net \
&& opam pin add coq 8.7.2 --yes \
&& opam pin add coq-mathcomp-ssreflect 1.6.4 --yes \
