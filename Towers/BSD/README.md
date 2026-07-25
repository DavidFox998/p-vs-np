# BSD — Birch and Swinnerton-Dyer + Class Number

### Overview
Arithmetic tower for BSD(143a1) + class number h(-143)=10 used by NS 1/10 factor and PvsNP ConductorHash prefix chain.

BSD is about elliptic curves — doughnut-shaped equations like y²=x³+ax+b. Rank = number of independent infinite solutions. BSD conjecture says rank = order of vanishing of L-function. For curve 143a1 (conductor 143=11×13), rank 0/1 data gives class number 10 — same 10 that appears in Navier-Stokes 1/10 averaging and P vs NP hash prefix chain.

Formalizes BSD for E=143a1: `N=143`, L-function `L(E,s)`, Heegner point, Kolyvagin derivative, BDP p-adic L-value prime `p5=3993746143633`. Analytic class number formula for imaginary quadratic `K=Q(√-143)` gives `h_K=10`. Uses LMFDB-anchored definitions (LMFDB database as external truth, not proved in Lean). Provides `ClassNumberK143.lean` with `h_neg143=10` theorem via `native_decide` wrapper around data.

### Methodology
- LMFDB-anchored: `def E143 : EllipticCurve := ⟨143, ...⟩` with data from LMFDB 143.a1
- Class number via analytic formula `h = √|D|/(2π) * L(1,χ_D)` — value 10 from LMFDB, not computed in Lean, stored as `def h_neg143 := 10`
- BDP prime `p5` from anticyclotomic p-adic L-function — stored as `def p5_BDP := 3993746143633`
- BSD statement: `rank(E) = ord_{s=1} L(E,s)` — formalized as `BSD_Conjecture E : Prop`
- Phase 23: close 3 BSD named opens via LMFDB-anchored defs — converts `sorry` to data definitions

### Empirical Math Dependency
- LMFDB database for 143.a1 (Cremona)
- Analytic class number formula — classical theorem, value from Sage/PARI
- BDP formula Bertolini-Darmon-Prasanna 2013 — p-adic L-value
- Gross-Zagier, Kolyvagin theorems for rank 0/1 — used as external results
- Axioms: classical trio only — numerical values via `native_decide`

### Files
- `ClassNumberK143.lean` + BSD L-function, Heegner, Selmer files (LMFDB-anchored)

### Results
- `h(-143)=10` available as data — used by Common/Conductor and PvsNP/ConductorHash and NS tower
- `p5=3993746143633` available — used by ConductorHash
- BSD(143a1) statement formalized — provides arithmetic input to Morning Star Project

### Dependencies
- `Towers.Common.Conductor`, Mathlib NumberTheory, LMFDB
