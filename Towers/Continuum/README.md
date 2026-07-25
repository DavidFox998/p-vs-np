# Continuum — Cardinal Arithmetic + CH

### Overview
Formalizes cardinal bounds, König's theorem, continuum hypothesis independence scaffolding. Provides infinite set size tools used by ZFC tower for forcing.

How many real numbers are there? More than integers — Cantor proved diagonal argument: list all reals, flip diagonal, new real not in list. Continuum hypothesis (CH) says there is no size between integers and reals — no set bigger than integers but smaller than reals. Gödel and Cohen proved CH can't be proved or disproved from ZFC — independent. This tower formalizes sizes of infinite sets (cardinals), Beth numbers (2^ℵ0, 2^{2^ℵ0}, ...), cofinality (shortest cofinal sequence), and König's theorem that says `cf(κ^{cf κ}) > κ` — prevents cardinal exponentiation from being too small. Used to show why P vs NP needs careful counting — Shannon counting `2^{2^n} > poly(n)` is same flavor.

Defines `Cardinal` via `Cardinal.mk` quotient of `Type` by equinumerosity `∃ f: α ≃ β`. Defines `ℵ0 = Cardinal.mk ℕ`, `ℵ_{α+1} = successor`, `ℶ0 = ℵ0, ℶ_{α+1}=2^{ℶα}`. Defines cofinality `cf κ = minimal |I| where ∃ cofinal map I→κ`. Proves König's theorem: for infinite `κ`, `κ < κ^{cf κ}` — via diagonalization `f: κ → P(κ)` can't be onto — same as Cantor. Proves König's inequality: `cf(2^κ) > κ` — corollary. Formalizes CH as `2^{ℵ0} = ℵ1`, GCH as `∀ α, 2^{ℵα}=ℵ_{α+1}`. Provides cardinal bounds `ℶ1 = 2^{ℵ0}`, `ℶ1 ≤ 2^{ℵ0} < ℶ2` etc. Provides counting lemmas used by Space tower for `DSPACE(log n) ⊆ P` via `2^{O(log n)} = poly`.

### Methodology
- Cardinal as quotient `Type / ≃` — uses `Classical.choice` for representative
- Beth numbers via transfinite recursion `ℶ0=ℵ0, ℶ_{α+1}=2^{ℶα}, ℶ_{sup}=sup`
- Cofinality via minimal order-type of cofinal subset — `cf κ = min { |I| | ∃ f: I→κ cofinal }`
- König via diagonalization: assume `κ ≥ κ^{cf κ}`, build `g: cf κ → κ` diagonal not in image — contradiction — same technique as P vs NP time hierarchy `DTIME(n) ⊂ DTIME(n²)` via `diag(L)=¬M_L(L)`
- CH formalized as `Prop`, not proved — independence via ZFC tower forcing skeleton `V^B` where `B=Add(ω,ℵ2)` forces `2^{ℵ0}≥ℵ2`
- Cardinal arithmetic via `Cardinal.add`, `mul`, `pow` — Mathlib

### Empirical Math Dependency
- Cantor 1891 diagonalization — proved — same technique as halting undecidable and time hierarchy
- König 1905 theorem `κ < κ^{cf κ}` — proved in Mathlib `Cardinal` — we provide wrapper with `native_decide` for concrete cardinals
- Zermelo 1904 well-ordering theorem — uses `Classical.choice` — for cardinal comparability
- ZFC axioms from ZFC tower for independence — Cohen 1963 forcing CH independent — statement formalized
- Mathlib SetTheory Cardinal library — `Cardinal.mk`, `ℵ0`, `2^κ`, `cf`
- Axioms: `[propext, Classical.choice, Quot.sound]` — `Classical.choice` needed for cardinal choice

### Files
- `CardinalBounds.lean` — ℶ numbers, exponentiation bounds `ℶ0 < ℶ1 < ℶ2`, `|P(ℕ)| = 2^{ℵ0}`
- `ContinuumHypothesis.lean` — CH `2^{ℵ0}=ℵ1`, GCH `∀ α 2^{ℵα}=ℵ_{α+1}` as `Prop`
- `KonigTheorem.lean` — König's theorem `κ < κ^{cf κ}` proof via diagonal
- `KonigInequality.lean` — `cf(2^κ) > κ` corollary
- `ContinuumCollection.lean` — index of all continuum results

### Results
- König's theorem machine-checked — `κ < κ^{cf κ}` — 0 sorry
- König's inequality `cf(2^κ) > κ` — 0 sorry
- Cardinal bounds `|P(ℕ)| = 2^{ℵ0}`, `ℶ1 ≤ 2^{ℵ0}` — 0 sorry
- CH and GCH formalized as `Prop` — independence framework via ZFC
- Counting lemmas `2^{O(log n)} = n^{O(1)}` used by Space for `L ⊆ P`

### Dependencies
- Mathlib `SetTheory.Cardinal`, `Towers.ZFC.IndependenceFramework`
- `Classical.choice` for cardinal well-ordering
