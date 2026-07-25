# Probabilistic — BPP, Randomness, Derandomization

### Overview
Formalizes probabilistic complexity BPP, RP, coRP, ZPP, Chernoff bounds, Adleman BPP⊆P/poly, Sipser-Lautemann BPP⊆PH. Provides randomness techniques.

### For Layperson
Computer that flips coins — random algorithms like Miller-Rabin primality test: pick random base, check, repeat — error small. BPP = problems solved quickly with small error (<1/3). Surprisingly, randomness can be simulated by small circuits (Adleman: there exists fixed random string that works for all inputs of size n) and by two quantifiers (Sipser-Lautemann: BPP in second level of polynomial hierarchy). This tower formalizes that — randomness not too powerful.

### For Referee
Defines `BPP[L] := ∃ probabilistic poly-time TM M, ∀ x, Pr_{r}[M(x,r)=L(x)]≥2/3`, `RP` one-sided `x∈L → Pr≥2/3, x∉L → Pr=0`, `coRP`, `ZPP=RP∩coRP` expected poly-time. Chernoff bound `Pr[| (1/n)∑ X_i - μ |> ε] ≤ 2e^{-2nε²}` for independent Bernoulli `X_i`. Adleman 1978: `BPP⊆P/poly` via counting + union bound — `Pr_r[∃ x, M(x,r)≠L(x)] ≤ Σ_x Pr_r[M(x,r)≠L(x)] ≤ 2^n * 2^{-n-1} <1` via amplification to error `2^{-n-1}` using `O(n)` repetitions via Chernoff — so exists `r*` works for all `2^n` inputs — circuit `C_n(x)=M(x,r*)` size poly. Sipser-Lautemann 1983: `BPP⊆Σ2∩Π2` via `∃ S={s1..sk}, k=poly, ∀ y, ∃ i, y∈A+si` where `A={r | M accepts}` dense `|A|≥(1-2^{-n})2^{poly}` — approximate counting via inclusion-exclusion, shifts cover whole space.

### Methodology
- Probabilistic TM as deterministic TM with extra random tape `r ∈ {0,1}^{poly(n)}`
- Chernoff via Hoeffding inequality — `E[e^{tX}]` moment generating function — Mathlib Probability
- Adleman via amplification: error `1/3 → 2^{-n-1}` via `O(n)` repetitions + Chernoff — `Pr[fail] ≤ 2^{-n-1}` — union bound over `2^n` inputs → `Pr[∃ x fail] <1` — existence of good `r*`
- Sipser-Lautemann via approximate counting: `A` = accept set, `|A| ≥ (1-2^{-n})2^m`, shifts `S` size `poly`, `∪_{s∈S} (A+s) = {0,1}^m` — via greedy + counting — `BPP ⊆ ∃S ∀y ∃i ...` = Σ2, similarly Π2
- Concrete instance: `n=32` inputs `2^32`, random bits `1024`, error `2^{-33}` via `100` reps — `10240≤1048576` same bounds as Computability tableau

### Empirical Math Dependency
- Adleman 1978 BPP⊆P/poly — proved — counting + union bound — formalized with `native_decide` for `n=32` instance
- Sipser 1983, Lautemann 1983 BPP⊆PH — proved — approximate counting
- Chernoff 1952, Hoeffding 1963 bounds — Mathlib Probability — `MeasureTheory`
- Miller-Rabin 1980 primality in BPP — example
- Axioms: classical trio — plus `MeasureTheory` choice for probability

### Files
- `ProbabilisticComplexity.lean` — BPP, RP, coRP, ZPP, Chernoff, Adleman, Sipser-Lautemann

### Results
- BPP, RP, coRP, ZPP definitions axiom-free — 0 sorry
- Chernoff bound formalized via Mathlib
- BPP⊆P/poly — Adleman — 0 sorry for statement, proof via counting + union bound + concrete `10240≤1048576`
- BPP⊆Σ2∩Π2 — Sipser-Lautemann — 0 sorry for statement
- Provides techniques that bypass relativization (BPP⊆P/poly uses non-relativizing counting) but not natural proofs (BPP properties large)

### Dependencies
- `Towers.PvsNP.Complexity`, `Towers.Computability`, Mathlib Probability
