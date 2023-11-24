# Verified insertion sort

An introduction to verified programming in Coq and Dafny in 45 minutes, for my
[directed undergraduate reading
group](https://sites.google.com/utexas.edu/dirp/) in the UT Austin computer
science department.

## Setup

We'll assume that you'll be using Visual Studio Code as your editor, if you
want to follow along on your own.

### Coq:

Begin by installing the OCaml compiler, which is the language that Coq is
written in.

```bash
# OSX
$ brew install ocaml opam

# Ubuntu
$ sudo apt-get install ocaml opam
```

Then, install the latest Coq language server, which should pull in
the latest version of Coq (as of this writing, 8.18.0):

```
$ opam install vscoq-language-server
```

### Dafny:

TBD
