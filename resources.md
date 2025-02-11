---
layout: page
title: Resources
permalink: /resources/
---

# Course Website

This course website, including all of the lecture materials, lives
[here](http://kcsrk.info/cs6225_s25_iitm/).

# Software

We need Coq and F\* for this course. It is easiest to install them using
[opam](https://opam.ocaml.org/), the OCaml package manager. Install opam for
your OS using [these
instructions](https://opam.ocaml.org/doc/Install.html#Binary-distribution). It
is recommended that you use Linux or macOS for this course.

## Coq

Then follow the instructions below install `coq`:

```bash
$ opam switch create cs6225 4.14.0 #create a fresh opam switch named cs6225 with OCaml 4.14.0
$ eval $(opam env --switch=cs6225)
$ opam pin add coq 8.16.0 #Install coq
$ opam install coqide #Install coqide
```

## F*

We will use [VSCode
devcontainers](https://hub.docker.com/r/microsoft/vscode-devcontainers) for F*
parts. You can start dev container with all the dependencies by

```bash
$ git clone https://github.com/kayceesrk/cs6225_s25_iitm
$ cd cs6225_s25_iitm
$ code . #start VSCode from root directory of the cloned repo
```

VSCode will prompt that it has found a dev container in the repo and whether to
reopen the folder to develop in a container. Click on "Reopen in container".
Among the two options shown in the command palette at the top, choose "CS6225 F*
devcontainer (from DockerHub)" option. This will download 2.5GB docker image
(takes a while) and reopens the project in the devcontainer.

# Text Books

We will use the two freely available books:

* *Formal Reasoning about Programs*, Adam Chlipala. Freely available [online](http://adam.chlipala.net/frap/).
* *Proof-oriented Programming in F\**, Nikhil Swamy, Guido Martínez, and Aseem Rastogi. Freely available [online](http://fstar-lang.org/tutorial/proof-oriented-programming-in-fstar.pdf).

Other reference books are:

* *Software Foundations*, Benjamin Pierce et al. Freely available [online](https://softwarefoundations.cis.upenn.edu/).
* *Types and Programming Languages*, Benjamin Pierce, MIT Press, 1st edition, 2002. Ebook is available in IITM library.
* *Practical Foundations for Programming Languages*, Robert Harper, Cambridge University Press, 2nd edition, 2016. Freely available [online](https://www.cs.cmu.edu/~rwh/pfpl/2nded.pdf).

# Tactics Reference

* Appendix in the [Frap book](http://adam.chlipala.net/frap/frap_book.pdf)
* [Cornell CS3110 Coq Cheat Sheet](https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html#leftright)
* [Coq tactic index](https://pjreddie.com/coq-tactics/)
* [Coq manual](https://coq.inria.fr/refman/proof-engine/tactics.html)
