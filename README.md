# sysl

A system language interpreter using traced monoidal evaluation.

## Overview

`sysl` provides a language with:

- **Commands** — System operations with values
- **Values** — Data and computation with results
- **Terms** — Expressions with fixed-point evaluation
- **Coterms** — Dual structures for bidirectional semantics

The `poly-redo` branch re-implements the interpreter as a `circuits` client:

- SysL types are promoted to `Circuit.Poly` polynomials via the type family
  `SysLTy`.
- Covariable boundaries use `Data.These` from `Circuit.Channel`.
- The traced compilation target is `Loop These (->)`.
- A streaming `Circuit.Process` interpreter is provided.
- `Then` is expressed as a polynomial lens via `Circuit.Poly.lens`.

## Building

```bash
cabal build
cabal run sysl-axioma
```

The `sysl-axioma` executable runs ten oracles (S1–S10) covering each
connective and cross-checking the direct, `Loop These`, and `Process`
interpreters.

## Modules

### SysL

System language with commands, values, terms, and coterms.
Interpretation is now via `Loop These (->)` with `These` covariable
boundaries.

### app/axioma.hs

Oracle executable.  Run with `cabal run sysl-axioma`.

## Version

0.1.0.0 — polynomial redo with `These` boundaries.

## License

BSD-3-Clause
