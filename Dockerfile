FROM ubuntu:latest

RUN apt-get -yyq update && apt-get -yyq install opam libgmp-dev python2.7
RUN opam init -a --disable-sandboxing
RUN opam pin add -y fstar https://github.com/FStarLang/FStar.git\#v2023.02.21

RUN mkdir /src
ADD *.fst verify.sh /src/

ENTRYPOINT ["/bin/bash", "/src/verify.sh"]
