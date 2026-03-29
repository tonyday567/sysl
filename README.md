# sysl

A system language interpreter using traced monoidal evaluation.

## Overview

`sysl` provides a language with:

- **Commands** - System operations with values
- **Values** - Data and computation with results
- **Terms** - Expressions with fixed-point evaluation
- **Coterms** - Dual structures for bidirectional semantics

All evaluated via the traced monoidal category framework from the `yarn` library.

## Building

```bash
cabal build
```

## Modules

### SysL

System language with commands, values, terms, and coterms.
Interpretation via `TracedA` for compositional evaluation.

## Version

0.1.0.0 - Initial release

## License

BSD-3-Clause
