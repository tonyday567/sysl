⟝ sysl

# System L on Circuit — Extending the 2-Cell Ladder

For the core analysis of Circuit vs Lawvere see
[circuits/examples/lawvere.md](https://github.com/tonyday567/circuits/blob/main/examples/lawvere.md) —
traced monoidal ≠ cartesian closed, `Knot` and `Curry` as structural
2-cells, the free category engine. This card extends that analysis with
System L — proof that the pattern generalises beyond the Circuit-Lawvere
pair, and a platform for conjectures about what comes next.

---

## System L, in Haskell, on Circuit

SysL (`~/haskell/sysl/`) is a Haskell implementation of System L — the
portion of linear logic expressible as a free category. As of commit
`4c03bc4` it imports Circuit directly:

```haskell
import Circuit (Circuit(..), Wire, reify)
type Traced = Wire
```

SysL's types cover the multiplicative-additive fragment plus graded modalities
and a sequential composition connective:

| Type | Constructor | Categorical meaning |
|---|---|---|
| `One` | `()` | multiplicative unit (I) |
| `Times a b` | `VPair a b` | multiplicative conjunction (⊗) |
| `Zero` | — | additive unit (0) |
| `Plus a b` | `VLeft a \| VRight b` | additive disjunction (⊕) |
| `Hom a b` | `VFun (a → Result b)` | linear implication (⊸) |
| `GradedHom a [b]` | `VGradedFun (a → Result b)` | graded linear implication |
| `Then a b` | `VThen a (a → Result b)` | sequential composition (⨟) |

The syntax follows focused linear logic: `Command = Cut (Term, Coterm)`,
with positive introductions in `Value`/`Term` and negative introductions
in `Coterm`. Each connective has a paired introduction/elimination form:

| Connective | Introduction (positive) | Elimination (negative) |
|---|---|---|
| **⊗** | `TensorIntro v1 v2` | `TensorMatch cmd` |
| **⊕** | `PlusIntroL v` / `PlusIntroR v` | `PlusMatch c1 c2` |
| **⊸** | `HomComatch cmd` | `HomCointro t k` |
| **⨟** | `Lit (VThen …)` / `ThenComatch cmd` | `ThenCointro k1 k2` |
| **graded ⊸** | `GradedHomComatch cmd` | `GradedHomCointro t coterms` |

Every connective compiles to `Circuit (->) (,)` via `Lift` and `Compose`
— no `Knot` needed for the current fragment, though `Knot` is available
when recursion enters. The compilation is direct: `commandToTraced ::
Command v → Traced [Val v] (Int, Val v)` maps the entire language into a
single Circuit arrow.

Tests pass clean:

```
testIdTraced = (0, VUnit)
testThenTraced = (0, VEmbed (1.0))
```

---

## The 2-Cell Ladder

Across Circuit, Lawvere, and SysL:

| Connective | 2-cell pair | Circuit | Lawvere | SysL |
|---|---|---|---|---|
| **⊗** (product) | pair / unpair | `(,)` tensor, Bifunctor | Cone / Proj | TensorIntro / TensorMatch |
| **⊕** (coproduct) | inject / case | `Either` tensor, Bifunctor | CoCone / Inj | PlusIntroL+R / PlusMatch |
| **trace** (feedback) | Knot / Mendler | `Knot`, `reify` Mendler case | `Fix` (ad-hoc mfix) | — (available via Circuit) |
| **⊸** (exponential) | curry / uncurry | *missing* | Curry / UnCurry | HomComatch / HomCointro |
| **⨟** (sequential) | then-in / then-out | *missing* | *missing* | ThenComatch / ThenCointro |
| **graded ⊸** | graded pair | *missing* | *missing* | GradedHomComatch / GradedHomCointro |

`⨟` (sequential composition) is the connective neither Circuit nor
Lawvere has. `VThen fwdA bwCont` carries a forward value and a backward
continuation — a bidirectional wire. `ThenCointro k1 k2` splits this:
runs `k1` on `fwdA`, gets a residual, feeds it to the backward
continuation, runs `k2` on the result. This is `ambient` in Circuit made
first-class — state that slides through a computation, but as a type
constructor rather than a threading combinator.

The graded ⊸ generalises linear implication to multiple continuation
slots — a function that can return to one of several coterms depending
on which slot fires.

---

## Conjectures

### 1. The Engine Does Not Change

Circuit's GADT — `Lift`/`Compose`/`Knot` — interpreted SysL's multiplicative
fragment without modification. Adding `Knot` would bring recursion under
the `Trace` constraint. Adding `Curry`/`UnCurry` (or `Then`) would add
constructors to `reify`, not a new engine. The conjecture: **the free
category GADT with accumulating structural 2-cells is the right engine
for any categorical structure that admits a free construction.**

### 2. Each 2-Cell Comes in a Pair

Every connective in SysL has an introduction and elimination form.
`Knot` has its dual in the Mendler case of `reify`. `Curry` is paired
with `UnCurry`. The conjecture: **structural 2-cells in a free category
always come in adjoint pairs** — introduction and elimination. This is
the same pattern as the profunctor equipment framing: a `Cell f g`
requires both `Strong` and `Costrong` on the hom-profunctor.

### 3. The Role of Then (⨟)

`Then` is a sequential composition *internalised as a type*. It's the
difference between "compose two morphisms" (external, `Compose` in the
GADT) and "have a type whose values carry a forward/backward protocol"
(internal, `Then`/`VThen`/`ThenComatch`/`ThenCointro`). The conjecture:
**⨟ is to composition what exponentials are to evaluation** — it
internalises the category's own composition as a type. This is the
categorical content of lenses/optics: a forward pass and a backward
pass, packaged as a value.

### 4. The Optics Connection

SysL originates from dependent optics research (Riley 2018; Boisseau &
Gibbons 2018; Capucci et al. 2022). Optics are dinatural transformations
in `Prof` — the same substrate as Circuit's `Knot` as a `Cell`. The
conjecture: **the free category with structural 2-cells (Circuit) is the
syntactic side of the optics correspondence** — every optic type (lens,
prism, traversal, glass) corresponds to a 2-cell that can be added to
Circuit. The ladder of missing connectives (⊸, ⨟, graded ⊸) is the
ladder of optic types.

### 5. What's Next

The immediate extension to Circuit: `Then` as a new `Knot`-like
constructor with dual semantics. Then `Curry`/`UnCurry` as the
exponential adjunction. Then the graded forms. Each adds one case to
`reify`. Each requires one constraint. The engine is the same.

---

## Summary

1. SysL implements System L on Circuit — multiplicative-additive linear
   logic plus ⨟ and graded modalities.
2. The 2-cell ladder extends Circuit → Lawvere → SysL: ⊗, ⊕, trace,
   ⊸, ⨟, graded ⊸. The ladder is tested code, not speculation.
3. Conjecture: the free category GADT with accumulating 2-cells is the
   engine for any categorical structure admitting free construction.
4. Conjecture: structural 2-cells come in adjoint pairs (intro/elim).
5. Conjecture: ⨟ internalises composition as a type — the core of optics.
6. Conjecture: the ladder of missing connectives is the ladder of optic
   types (lens, prism, traversal, glass).

---

## References

- [lawvere.md](https://github.com/tonyday567/circuits/blob/main/examples/lawvere.md) —
  the core comparative engineering analysis; traced monoidal vs cartesian closed.
- [proarrow.md](https://github.com/tonyday567/circuits/blob/main/examples/proarrow.md) —
  `Trace` ≅ `Strong + Costrong` under self-action; `Knot` as 2-cell.
- [SysL source](https://github.com/tonyday567/sysl) (`~/haskell/sysl/src/SysL.hs`) —
  System L wired to Circuit. Compiles to `Circuit (->) (,)` via
  `commandToTraced`, `termToTraced`, `cotermToTraced`.
- [Milewski, Profunctor Optics](https://bartoszmilewski.com/2017/07/07/profunctor-optics/) —
  the profunctor encoding of optics.
- [Milewski, Profunctor Equipment](https://bartoszmilewski.com/2026/05/16/profunctor-equipment-in-haskell/) —
  `Cell f g h j` encoding for proarrow equipments.
- [Riley, Categories of Optics](https://arxiv.org/abs/1809.00738) (2018) —
  dependent optics; mixed optics as dinatural transformations.
- [Boisseau & Gibbons, What You Needa Know about Yoneda](https://www.cs.ox.ac.uk/jeremy.gibbons/publications/proyo.pdf) (2018) —
  profunctor optics and Yoneda.
- [Capucci, Gavranović, Hedges, Rischel](https://arxiv.org/abs/2209.09351) (2022) —
  categorical systems theory; optics for open diagrams.
- [nLab: linear logic](https://ncatlab.org/nlab/show/linear+logic)
- [nLab: profunctor optics](https://ncatlab.org/nlab/show/optic+%28in+computer+science%29)
- [nLab: equipment](https://ncatlab.org/nlab/show/equipment)
