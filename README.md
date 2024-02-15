# A Coq Formalization of Robust Mean Estimators

## Meta

- Authors
  - Reynald Affeldt
  - Alessandro Bruni
  - Ieva Daukantas
  - Takafumi Saikawa
- Compatible Coq versions: `>=8.17`
- Additional dependencies:
  - [infotheo](https://github.com/affeldt-aist/infotheo)
  - [mathcomp](https://math-comp.github.io/)
  - [CoqInterval](https://coqinterval.gitlabpages.inria.fr/)
- Related publications:
  - Trimming Data Sets: a Verified Algorithm for Robust Mean Estimation [doi: 10.1145/3479394.3479412](https://doi.org/10.1145/3479394.3479412)

## Documentation

The repository is documented with [coq2html](https://github.com/yoshihiro503/coq2html/) and the statically generated documentation is available at [hoheinzollern.github.io/robustmean](https://hoheinzollern.github.io/robustmean/).

## Setup

The best way to get started with this repository is through [opam](https://opam.ocaml.org/doc/Install.html):

```sh
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-infotheo coq-interval
```

You can then download this repository and compile the sources:

```sh
git clone git@github.com:hoheinzollern/robustmean.git
cd robustmean
make
```
