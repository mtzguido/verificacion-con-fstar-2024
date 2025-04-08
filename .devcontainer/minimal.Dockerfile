FROM ubuntu:24.10

SHELL ["/bin/bash", "-c"]

# Base dependencies: opam
# CI dependencies: jq (to identify F* branch)
# python3 (for interactive tests)
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
      ca-certificates \
      curl \
      wget \
      git \
      gnupg \
      sudo \
      libgmp-dev \
      opam \
      pkg-config \
    && apt-get clean -y
# FIXME: libgmp-dev and pkg-config should be installed automatically by opam,
# but it is not working, so just adding it above.

# Create a new user and give them sudo rights
ARG USER=vscode
RUN useradd -d /home/$USER -s /bin/bash -m $USER
RUN echo "$USER ALL=NOPASSWD: ALL" >> /etc/sudoers
USER $USER
ENV HOME /home/$USER
WORKDIR $HOME
RUN mkdir -p $HOME/bin

# Make sure ~/bin is in the PATH
RUN echo 'export PATH=$HOME/bin:$PATH' | tee --append $HOME/.profile $HOME/.bashrc $HOME/.bash_profile

# Install OCaml
ARG OCAML_VERSION=4.14.2
RUN opam init --compiler=$OCAML_VERSION --disable-sandboxing
RUN opam option depext-run-installs=true
ENV OPAMYES=1
RUN opam install --yes batteries zarith stdint yojson dune menhir menhirLib pprint sedlex ppxlib process ppx_deriving ppx_deriving_yojson memtrace

# Get compiled Z3
RUN wget -nv https://github.com/Z3Prover/z3/releases/download/Z3-4.8.5/z3-4.8.5-x64-ubuntu-16.04.zip \
 && unzip z3-4.8.5-x64-ubuntu-16.04.zip \
 && cp z3-4.8.5-x64-ubuntu-16.04/bin/z3 $HOME/bin/z3 \
 && rm -r z3-4.8.5-*

# Get F* master and build
RUN eval $(opam env) && opam install fstar

# Get F* release and extract into home
# ARG FSTAR_RELEASE_LINK=https://github.com/FStarLang/FStar/releases/download/v2024.09.05/fstar_2024.09.05_Linux_x86_64.tar.gz
# RUN wget -nv $FSTAR_RELEASE_LINK \
#  && tar xzf fstar_*.tar.gz -C $HOME \

# Instrument .profile and .bashrc to set the opam switch. Note that this
# just appends the *call* to eval $(opam env) in these files, so we
# compute the new environments fter the fact. Calling opam env here
# would perhaps thrash some variables set by the devcontainer infra.
RUN echo 'eval $(opam env --set-switch)' | tee --append $HOME/.profile
RUN echo 'eval $(opam env --set-switch)' | tee --append $HOME/.bashrc

# Also just link F* into bin
RUN eval $(opam env --set-switch) && ln -s $(which fstar.exe) $HOME/bin/fstar.exe
