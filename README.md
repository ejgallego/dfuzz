dfuzz: Linear Dependent Types for Differential Privacy
=====

This repository implements a type checker for the linear dependent
lambda calculus of [1].

The details of the algorithm are on a IFL 2014 paper:

http://arxiv.org/abs/1503.04522

[1] Marco Gaboardi, Andreas Haeberlen, Justin Hsu, Arjun Narayan, and Benjamin C. Pierce. 2013. Linear dependent types for differential privacy. In Proceedings of the 40th annual ACM SIGPLAN-SIGACT symposium on Principles of programming languages (POPL '13). ACM, New York, NY, USA, 357-370. DOI=10.1145/2429069.2429113 http://doi.acm.org/10.1145/2429069.2429113

## Install

You need ocaml >= 4.07.1 plus dune, and the why3
dependencies plus standard gnu tools like gcc and make.

You can obtain all that by doing:
```
$ opam install --deps-only -d -t .
```

then run

```
$ why3 config --detect
$ dune build
```

to compile the tool

## How to compile and run programs

To typecheck a program type:

```
$ dune exec -- dfuzz examples/dfuzz/cdf.fz
```

Running the program is still not supported in dFuzz.


