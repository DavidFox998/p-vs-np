# Interactive — IP = PSPACE

### Overview
Formalizes interactive proofs, sum-check protocol, IP⊆PSPACE, PSPACE⊆IP (LFKN/Shamir). Provides non-relativizing + algebrizing technique example that bypasses BGS but not AW.

Normal proof you write and verifier checks alone. Interactive proof you have conversation: verifier asks random questions, prover answers. Surprisingly, this conversation can prove anything that needs polynomial memory — IP=PSPACE. Example: prove you know Sudoku solution without revealing it — verifier asks random row, you prove row valid without showing whole solution. Sum-check is key trick: to check sum of huge polynomial over 2^n points (2^100 huge), verifier asks prover for univariate polynomial, checks two points, picks random spot, recurses — 100 rounds instead of 2^100 checks.

Defines `IP[L] := ∃ P prover unbounded, ∀ V probabilistic poly-time verifier, completeness Pr[V accepts x∈L] ≥2/3, soundness Pr[V accepts x∉L] ≤1/3`. Defines `PSPACE := ∪_k DSPACE(n^k)`. Sum-check protocol for `∑_{x∈{0,1}^n} g(x)=S` where `g: F^n → F` low-degree `d` per variable, `|F| > 2^n * d`: Round i: prover sends `g_i(X)=∑_{x_{i+1}..x_n} g(r1..r_{i-1}, X, x_{i+1}..)`, degree d univariate, verifier checks `g_i(0)+g_i(1)=S_{i-1}`, picks random `r_i∈F`, sets `S_i=g_i(r_i)`, recurses. Final check `g(r1..rn)=S_n` via direct query. Schwartz-Zippel lemma `Pr_{r∈F}[g(r)=0] ≤ d·n/|F|` for non-zero degree-d polynomial — soundness `d·n/|F|`. LFKN 1990: coNP⊆IP via arithmetization of UNSAT `∀ x ¬φ(x)` → `∑ (1-φ̂)=2^n`. Shamir 1992: PSPACE⊆IP via TQBF `Q1x1...Qnxn φ` → arithmetic `∏_{x} φ̂` for ∀, `∑_{x} φ̂` for ∃ with degree reduction via `∀x P(x) → P(0)·P(1)` trick. IP⊆PSPACE via optimal prover in PSPACE — enumerate all prover strategies `2^{poly}` via recursion.

### Methodology
- Interactive protocol as `List (Challenge × Response)` where `Challenge = F`, `Response = Polynomial`
- Sum-check via induction on `n` — prover sends degree-d poly, verifier checks two points via `eval`
- Schwartz-Zippel via induction on variables — `g≠0 → ∃ variable where coefficient ≠0 → Pr ≤ d/|F| + ...`
- Arithmetization: Boolean `x∧y → x·y`, `¬x → 1-x`, `x∨y → 1-(1-x)(1-y)` over field `F_p` with `p > 2^n`
- TQBF `Q1x1...Qnxn φ` → `Q̂1x1...Q̂nxn φ̂` where `Q̂i = ∑_{x_i∈{0,1}}` if ∃, `∏_{x_i∈{0,1}}` if ∀, with linearization `∀x P(x) → P(0)·P(1)` to keep degree low
- IP⊆PSPACE via game tree evaluation — `∃ prover strategy` = `max_{prover} min_{verifier randomness}` in PSPACE via recursion

### Empirical Math Dependency
- LFKN Lund-Fortnow-Karloff-Nisan 1990 coNP⊆IP — statement formalized, proof skeleton via sum-check
- Shamir 1992 PSPACE⊆IP — TQBF arithmetization — statement formalized
- Schwartz-Zippel lemma 1980 — proved in Mathlib — `Pr[g(r)=0] ≤ deg/|F|`
- QBF PSPACE-complete — from Space tower
- Axioms: classical trio

### Files
- `InteractiveProofs.lean` — IP, PSPACE, completeness/soundness, IP⊆PSPACE, PSPACE⊆IP statements
- `SumCheck.lean` — sum-check protocol, Schwartz-Zippel, arithmetization

### Results
- IP definitions axiom-free — 0 sorry
- Sum-check protocol verified — completeness/soundness via Schwartz-Zippel
- IP=PSPACE theorem statements — 0 sorry for definitions, proofs skeleton
- Provides non-relativizing + algebrizing technique example: IP=PSPACE uses algebraic extension (arithmetization) — shows algebrization barrier (AW) is needed — technique that proves IP=PSPACE cannot separate P vs NP via algebrization

### Dependencies
- `Towers.Space.SpaceComplexity` (PSPACE), `Towers.PvsNP.Complexity`, Mathlib Polynomial
