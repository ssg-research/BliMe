BliMe formal model
==================

This directory contains a formal model of BliMe's taint-tracking policy written in F\*.  The proof contained in the model verifies that the taint-tracking policy as applied to a simple model ISA does not allow for information flow between blinded and unblinded machine state.

You can verify the proofs by running 

```console
$ docker build -t blime-model .
$ docker run -it blime-model 
[WARNING] Running as root is not recommended
Verified module: Value
Verified module: Multi
Verified module: Memory
Verified module: Cpu
Verified module: InstructionDecoder
Verified module: ISA
All verification conditions discharged successfully
```

More details on the proofs themselves can be found [here](https://blinded-computation.github.io/blime-model/).
