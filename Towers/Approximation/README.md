# Approximation — Hardness of Approximation

### Overview
Formalizes approximability classes APX, PTAS, gap-preserving reductions, PCP connection, inapproximability up to Håstad.

Some problems we can't solve exactly, but can approximate — like traveling salesman within 2× optimal. This tower formalizes which problems can be approximated and which can't — and proves some can't be approximated unless P=NP.

Defines approximation ratio `α≥1`, `APX := ∃ α, HasPolyTimeαApprox`, `PTAS := ∀ ε>0, HasPolyTime(1+ε)Approx`, gap-preserving reductions `L ≤_gap L'`, PCP theorem statement `NP = PCP(O(log n), O(1))` as certified theorem skeleton, Håstad 3-SAT inapproximability 7/8+ε. Uses CircuitComplexity Shannon bound for counting.

### Methodology
- Approximation ratio via `Real` — `∃ alg, ∀ instance, cost(alg) ≤ α·OPT`
- Gap reduction: `YES → val≥c, NO → val≤s` with gap `c/s`
- PCP via verifier using `O(log n)` random bits, `O(1)` queries — statement only, proof via Razborov-Rudich barrier discussion
- Håstad linearity test `x⊕y⊕z = b` — 7/8 bound via Fourier analysis skeleton

### Empirical Math Dependency
- PCP theorem Arora et al 1998 — statement formalized, proof external
- Håstad 2001 3-SAT hardness 7/8+ε — statement formalized
- Shannon counting from PvsNP.CircuitComplexity
- Axioms: classical trio

### Files
- `ApproximationComplexity.lean` — APX, PTAS definitions, gap reductions
- `ApproximationCollection.lean` — index

### Results
- APX, PTAS definitions axiom-free
- Gap-preserving reduction framework
- Inapproximability conditional on P≠NP — used by Barriers Natural Proofs largeness discussion

### Dependencies
- `Towers.PvsNP.Complexity`, Mathlib
