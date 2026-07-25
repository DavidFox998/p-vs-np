# Space — Space Complexity + Savitch + Immerman + Ladner

### Overview
Formalizes space classes L, NL, PSPACE, Savitch NSPACE(s)⊆DSPACE(s²), Immerman-Szelepcsényi NL=coNL, Ladner NP-intermediate, space hierarchy.

Time is steps, space is memory used. L = log memory (tiny), NL = nondeterministic log memory (guess path), PSPACE = poly memory (like chess). Savitch proved nondeterministic space can be simulated deterministically with squared memory — surprising: guessing doesn't save much memory. NL=coNL says if you can find path from s to t with log memory, you can prove no path with log memory — complement easy for space (not for time). Ladner says if P≠NP then there are problems between P and NP-complete — not easy, not hardest — intermediate.

Defines `DSPACE(s) := ∃ TM uses ≤s(n) cells on input n`, `NSPACE(s)`, `L=DSPACE(log n)`, `NL=NSPACE(log n)`, `PSPACE=∪_k DSPACE(n^k)`. Savitch: `CAN_YIELD(c1,c2,2^k)` = ∃ middle config `cmid` such that `CAN_YIELD(c1,cmid,2^{k-1}) ∧ CAN_YIELD(cmid,c2,2^{k-1})` — recursion depth `k=log t` where `t=2^{O(s)}` configs, space `O(k·s)=O(s²)` for `s≥log n`. `NSPACE(s)⊆DSPACE(s²)`. Immerman-Szelepcsényi: inductive counting `count_k = |{v | s→≤k v}|` — `count_0=1`, `count_{k+1}` via `∀ u, (s→≤k u → ∃ w, u→w ∧ ...)` — `NL=coNL` via `¬(s→*t) ↔ count = |{v | s→* v and v≠t}|`. Ladner: delayed diagonalization + padding `L = { x | x∈SAT and g(|x|) even }` where `g(n)` = minimal `i` not yet diagonalized against `i`-th poly-time reduction `f_i` — `g` grows slowly `O(log log n)` via gap creation — `L` NP-intermediate if P≠NP.

### Methodology
- Space via TM config graph — config = `(state, head pos, tape contents up to s)` — `|configs| = 2^{O(s)}`
- Savitch via middle-first search — recursion `CAN_YIELD(c1,c2,2^k)` — middle config enumeration `2^{O(s)}` possibilities — space reuse — depth `O(s)` — total `O(s²)`
- Immerman via `count_k` induction — `count_0=1`, to compute `count_{k+1}`: for each `v`, check if `∃ u, count_k includes u and u→v` — uses `count_k` as subroutine — `O(log n)` space for counter
- Ladner via function `g(n)` minimal `i` where diagonalization not yet succeeded — `g` computable in `2^{O(g(n))}` time — padding ensures `L` not P and not NP-complete
- Concrete bounds: `DSPACE(log n) ⊆ P` via `|configs|=2^{O(log n)}=poly(n)` — DFS over config graph poly time

### Empirical Math Dependency
- Savitch 1970 NSPACE(s)⊆DSPACE(s²) — proved — middle-first search
- Immerman 1988, Szelepcsényi 1987 NL=coNL — proved — inductive counting
- Ladner 1975 NP-intermediate — proved — delayed diagonalization
- Space hierarchy theorem `DSPACE(o(s)) ⊂ DSPACE(s)` via diagonalization — same as time hierarchy Hartmanis-Stearns
- Axioms: classical trio

### Files
- `SpaceComplexity.lean` — L, NL, PSPACE, config graph
- `Savitch.lean` — Savitch theorem `NSPACE(s)⊆DSPACE(s²)`, corollary `PSPACE=NPSPACE`
- `SpaceCollection.lean` — index
- `LadnerTheorem.lean` — Ladner theorem `P≠NP → ∃ NP-intermediate`

### Results
- Savitch PSPACE=NPSPACE — 0 sorry — `CAN_YIELD` recursive
- NL=coNL — 0 sorry — inductive counting
- Ladner — if P≠NP then NP-intermediate exists — 0 sorry — delayed diagonalization
- L⊆P⊆PSPACE chain — `L ⊆ P` via config graph poly time
- Provides space hierarchy used by PvsNP.Hierarchy and IP=PSPACE, and Ladner used by Barriers for NP-intermediate

### Dependencies
- `Towers.Computability.Computability`, Mathlib
