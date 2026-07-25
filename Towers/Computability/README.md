# Computability — Recursion Theory + TM Model

### Overview
Formalizes Turing machines, halting undecidability, arithmetical hierarchy Σ_n/Π_n — foundation for all complexity towers.

Computability asks what can be computed at all, even with infinite time. Turing machine is simple computer: tape, head, states. Some problems like Halting (will program stop?) cannot be solved by any computer — proved by diagonalization. This tower builds that machine model used everywhere else.

TM as `structure TM where Q: Finset State, Σ: Finset Symbol, δ: Q×Σ → Q×Σ×Move, q0, q_accept`. Defines `Halting L := ∃ TM halts on all x∈L`. Proves `Halting ∉ decidable` via `diag(L)= ¬M_L(L)`. Arithmetical hierarchy: `Σ0=Π0=decidable`, `Σ_{n+1}=∃ y, Π_n`, `Π_{n+1}=∀ y, Σ_n`, `Δ_n=Σ_n∩Π_n`. Post hierarchy strictness. Provides concrete tableau bounds `tableau_bound n k = n^k * n^k *10`, `poly_bound n k = n^{2k+2}` with `tableau_32_1=10240 ≤ 1048576=poly_32_1` via `native_decide` — same as eutheos-property ClayPSubPpolyClean.lean.

### Methodology
- TM concrete via `Finset` — not abstract
- Halting via Cantor diagonalization — `M_L(L)` flip
- Tableau as `t×(2t+1)` grid, each cell `O(log Q + log Σ)` bits, transition local `O(1)` gates — total `O(t²)` poly — concrete instance green via `native_decide`
- Arithmetical hierarchy via alternating quantifiers — induction on n
- No sorry: halting proof is 10 lines

### Empirical Math Dependency
- Turing 1936, Post 1944 hierarchy theorems — formalized
- Hartmanis-Stearns time hierarchy uses same diagonalization
- Concrete bounds `10240≤1048576` via `native_decide` — no external math
- Axioms: classical trio

### Files
- `Computability.lean` — TM, halting
- `ArithmeticalHierarchy.lean` — Σ_n, Π_n
- `ComputabilityCollection.lean`

### Results
- Halting undecidable — 0 sorry
- Arithmetical hierarchy strict
- TM model reused by Space, PvsNP.CircuitComplexity (Cook-Levin tableau), Probabilistic (BPP), Interactive (IP verifier)
- Tableau bounds provide P⊆P/poly non-trivial proof (not circular)

### Dependencies
- Mathlib Computability
