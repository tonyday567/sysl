⟝ sysl

# System L on Circuit — Polynomial Encoding with These Boundaries

This card describes the `poly-redo` version of SysL (`~/haskell/sysl/`).
The interpreter has been rebuilt as a `circuits` client:

- User-facing types are promoted to `Circuit.Poly` polynomials via `SysLTy`.
- Covariable boundaries use `Data.These`, the inclusive tensor from
  `Circuit.Channel`.
- The traced target is `Loop These (->)` instead of the hand-rolled
  `Loop (,) (->)` plumbing.
- A streaming reading is available via `Circuit.Process`.
- The `sysl-axioma` executable contains oracles S1–S10.

For the core analysis of Circuit vs Lawvere see
[circuits/examples/lawvere.md](https://github.com/tonyday567/circuits/blob/main/examples/lawvere.md).

---

## SysL types as polynomials

The `Ty` ADT is unchanged at the surface, but each constructor now has a
promoted polynomial image:

| SysL `Ty`       | `SysLTy` polynomial                     | `Domain` (closed semantics)               |
|-----------------|-----------------------------------------|-------------------------------------------|
| `One`           | `Const ()`                              | `()`                                      |
| `Times a b`     | `Prod (SysLTy a) (SysLTy b)`            | `(Domain a, Domain b)`                    |
| `Zero`          | `Const Void`                            | `Void`                                    |
| `Plus a b`      | `Sum (SysLTy a) (SysLTy b)`             | `Either (Domain a) (Domain b)`            |
| `Hom a b`       | `Mono (Domain a) (Domain b)`            | `Domain a -> Domain b`                    |
| `GradedHom a bs`| `Sum` of indexed `Mono (Domain a) (Domain b_i)` | `Domain a -> EitherList (Domain b_i)` |
| `Then a b`      | `Mono (Domain a) (Domain b)`            | `Domain a -> Domain b`                    |

`Mono i o` is the polynomial lens `Prod (Const o) (Exp i)` from
`Circuit.Poly`.  Closed finite values (`One`, `Times`, `Plus`, `Zero`) can be
converted between the runtime `Val` representation and the polynomial
`Eval (SysLTy t) v` view via the `PolyVal` class.

The opaque domain value `VEmbed v` is the evaluation variable `x` in `p(x)`;
conceptually it is `EY x` at the polynomial variable `Y`.  Compound values
are otherwise expressed as `Eval (SysLTy t) v` wherever the type is closed.

---

## Boundaries as `These`

The old untagged result `Result v = RVal Int (Val v)` is replaced by the
inclusive tensor boundary:

```haskell
type Output v = (Int, Val v)
type Result v = These (Output v) (Output v)
```

Following the convention in `Circuit.Channel`:

- `This (i, v)`  — residual covariable consumed (slot `i >= 1`).
- `That (0, v)`  — focus consumed (slot 0).
- `These o1 o2`  — both residual and focus consumed.

The direct evaluator (`evalCommand`, `evalValue`, `evalTerm`, `evalCoterm`)
and the `Loop These` compiler both use this boundary.

---

## The `Loop These` compiler

The traced target is now `Loop These (->)`:

```haskell
commandToLoop :: Command v -> Loop These (->) (Env v) (Result v)
termToLoop    :: Term v    -> Loop These (->) (Env v) (These (Output v) (Val v))
cotermToLoop  :: Coterm v  -> Loop These (->) (Env v, Val v) (Result v)
```

Because `Circuit.Channel` did not yet ship a `Traced These (->)` base
instance, SysL supplies the orphan instance needed to interpret `Knot`
bodies: iterate the feedback channel (`This`) until the body produces a
payload (`That` or `These`).

The original regression tests are preserved as `testId` / `testThen`
(direct evaluator) and `testIdLoop` / `testThenLoop` (`Loop These`).

---

## `Then` as polynomial optic

`Then a b` is represented by the same monomial lens as `Hom a b`:
`Mono (Domain a) (Domain b)`.  The helpers

```haskell
thenLens   :: (Val v -> Val v) -> (Val v -> Val v -> Val v)
           -> Morphism (Mono (Val v) (Val v)) (Mono (Val v) (Val v))
applyThen  :: Morphism (Mono (Val v) (Val v)) (Mono (Val v) (Val v))
           -> Val v -> (Val v, Val v -> Val v)
```

wrap `Circuit.Poly.lens` / `applyLens`.  At runtime `VThen fwd bw` still
carries a forward value and a backward continuation, so `ThenCointro` can
thread residuals through the backward map.

---

## Streaming via `Process`

`evalProcess :: Term v -> Process (Env v) (Val v)` gives a Moore-machine
reading of a closed term: each input environment yields the term's focus
value.  This is the entry point for scheduled / stateful semantics.

---

## Oracle suite

`cabal run sysl-axioma` prints `all green` when the following pass:

| Oracle | What it checks |
|--------|----------------|
| S1     | `One` round-trip through `Eval (SysLTy 'One) v` |
| S2     | `Times` round-trip (nested pairs) |
| S3     | `Plus` left / right injections |
| S4     | `Hom` β/η: identity function applied to `VUnit` |
| S5     | `Then` forward/backward round-trip via `thenLens` |
| S6     | `GradedHom` slot dispatch |
| S7     | `Mu` identity on the focus slot |
| S8     | `Comu` corecursion (environment prepend) |
| S9     | Direct evaluator agrees with `Loop These` interpreter |
| S10    | Direct evaluator agrees with `Process` interpreter |

---

## The 2-Cell Ladder (updated)

Across Circuit, Lawvere, and SysL:

| Connective | 2-cell pair | Circuit | Lawvere | SysL |
|---|---|---|---|---|
| **⊗** | pair / unpair | `(,)` tensor | Cone / Proj | `TensorIntro` / `TensorMatch` |
| **⊕** | inject / case | `Either` tensor | CoCone / Inj | `PlusIntroL+R` / `PlusMatch` |
| **trace** | Knot / Mendler | `Knot`, `reify` | `Fix` | `Loop These` `Knot` |
| **⊸** | curry / uncurry | *missing* | Curry / UnCurry | `HomComatch` / `HomCointro` as `Mono` lens |
| **⨟** | then-in / then-out | *missing* | *missing* | `ThenComatch` / `ThenCointro` as `Mono` lens |
| **graded ⊸** | graded pair | *missing* | *missing* | `GradedHomComatch` / `GradedHomCointro` as sum of monomials |

The engine is now the free traced monoidal category `Loop` together with
the `These` inclusive tensor for covariable scheduling.

---

## Build and test

```bash
cabal build
cabal run sysl-axioma
```

Expected output:

```
sysl-axioma oracles
all green
```

---

## References

- [lawvere.md](https://github.com/tonyday567/circuits/blob/main/examples/lawvere.md)
- [SysL source](https://github.com/tonyday567/sysl) (`~/haskell/sysl/src/SysL.hs`)
- `Circuit.Poly`, `Circuit.Channel`, `Circuit.Loop`, `Circuit.Process` in
  `~/haskell/circuits/`.
