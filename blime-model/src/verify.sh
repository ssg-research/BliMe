#!/bin/bash

set +ex

eval $(opam env)
fstar.exe /src/*.fst
