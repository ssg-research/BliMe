Blinded Memory
==============

This repository brings together the source code for the Blinded Memory (BliMe) project.

BliMe is an architecture to realize efficient and secure outsourced computation. BliMe consists of a novel and minimal set of ISA extensions implementing a taint-tracking policy to ensure the confidentiality of client data even in the presence of server vulnerabilities. To secure outsourced computation, the BliMe extensions can be used together with an attestable, fixed-function hardware security module (HSM) and an encryption engine that provides atomic decrypt-and-taint and encrypt-and-untaint operations. Clients rely on remote attestation and key agreement with the HSM to ensure that their data can be transferred securely to and from the encryption engine and will always be protected by BliMe’s taint-tracking policy while at the server.

This repository contains three main parts:

  - `firesim` contains a [FireSim](https://fires.im/) configuration that allows you to run a BliMe-enabled [BOOM](https://boom-core.org/) RISC-V core on an AWS F1 EC2 instance.
  - `gem5` contains a modified [gem5](https://www.gem5.org/) simulator that allows you to simulate the performance impact of BliMe.
  - `model` contains a model of BliMe's taint-tracking policy as applied to a model ISA, written in F*, along with a proof that this policy is secure from an information-flow point of view.

For more details, see the [preprint](https://arxiv.org/abs/2204.09649) and the [project web page](https://ssg-research.github.io/blime/).

You can cite BliMe as
```bibtex
@inproceedings{blime24,
  title = {BliMe: Verifiably Secure Outsourced Computation with Hardware-Enforced Taint Tracking},
  author = {H ElAtali and L J Gunn and H Liljestrand and N Asokan},
  booktitle = {Network and Distributed Systems Symposium (NDSS)},
  location = {San Diego, CA, USA},
  year = {2024},
  isbn = {1-891562-93-2},
  doi = {10.14722/ndss.2024.24105}
}
```
