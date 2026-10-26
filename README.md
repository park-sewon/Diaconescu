# Global Choice without Excluded Middle in Dependent Type Theory

`Model.v` is the Rocq formalization of the paper "Global Choice without Excluded Middle in
Dependent Type Theory".

## Requirements

Rocq 9.1.1 with its standard library.

## Build

```sh
rocq compile -Q . Diaconescu Model.v
```

## Kernel check

```sh
rocqchk -Q . Diaconescu Diaconescu.Model
```

## Axioms

`Print Assumptions natModel` gives exactly `em`, `propext`, `funext` and `choice`, the axioms of
the classical metatheory.
