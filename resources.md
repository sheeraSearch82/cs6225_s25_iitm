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

Then follow the instructions below:

```bash
$ opam switch create cs6225 4.14.0 #create a fresh opam switch named cs6225 with OCaml 4.14.0
$ eval $(opam env --switch=cs6225)
$ opam pin add coq 8.16.0 #Install coq
$ opam install coqide #Install coqide
```

F\* and karamel require GNU make. For
[karamel](https://fstarlang.github.io/lowstar/html/index.html), python2.7
installation is also needed. If you are on macOS, you can install it using
[Homebrew](https://brew.sh/). The following steps are only for macOS. If you are
on Linux, skip to the F\* karamel installation step.

```bash
#only for macOS
$ brew install make
$ opam var --global make=gmake # make opam use gmake
$ alias make=gmake # create an alias in the current shell
$ make --version # verify
gmake: getcwd: No such file or directory
GNU Make 4.4.1
Built for aarch64-apple-darwin24.0.0
Copyright (C) 1988-2023 Free Software Foundation, Inc.
License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>
This is free software: you are free to change and redistribute it.
There is NO WARRANTY, to the extent permitted by law.
```

Now install `karamel`:

```bash
$ opam pin add fstar --dev-repo #Install F*
$ opam pin add karamel --dev-repo
```

You can verify everything is set up correctly by using the following commands:

```bash
$ coqide #should open Coq IDE
$ fstar.exe --version
F* 2024.09.05~dev
platform=Linux_x86_64
compiler=OCaml 4.14.0
date=2024-10-24 17:40:26 -0700
commit=8b6fce63ca91b16386d8f76e82ea87a3c109a208
$ krml -version
KaRaMeL version: 87384b244a98a0c41a2e14c65b872d885af7c8df
```

You should see similar output, but necessarily the same hashes.

Finally, for F\* editor support, install
[vscode](https://code.visualstudio.com/) and [F* vscode
extension](https://github.com/FStarLang/fstar-vscode-assistant).

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
