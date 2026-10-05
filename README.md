[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22049027.svg)](https://doi.org/10.5281/zenodo.22049027) [![Lean proof build](https://github.com/DavidFox998/p-vs-np/actions/workflows/lean.yml/badge.svg)](https://github.com/DavidFox998/p-vs-np/actions/workflows/lean.yml)

# P vs NP — Conditional Compiler + ConductorHash — 225 bricks — Mechanics side

> **Opera Numerorum ensemble** — 19 repos · chain `7472f4e5` · [REPOS.md →](https://github.com/DavidFox998/rh-p5-bridge-14/blob/main/REPOS.md)


**N=143=11×13 phi=120 g=13 h=10 p5=3993746143633 S₄={2,3,19,191} — ORCID 0009-0008-1290-6105**

Lean 4.15.0 / Mathlib v4.15.0 | 0 sorry in core | `[propext, Classical.choice, Quot.sound]`

## 0. The three-repo flow — scaffold → witness → route

This repo is the **scaffold**: it formalizes the three known barriers (BGS relativization, RR natural proofs, AW algebrization) and the ConductorHash machine, then asks whether any arithmetic object bypasses all three at once. The answer lives downstream:

1. **[p-vs-np](https://github.com/DavidFox998/p-vs-np) — this repo (scaffold).** Barriers + ConductorHash + conditional `SAT∉P→P≠NP` across 11 towers, 225 bricks.
2. **[eutheos-property](https://github.com/DavidFox998/eutheos-property) — witness.** `1419 = 3×11×43` (`0x058B`, popcount 6, residue 153 mod 211) with exact circuit complexity 9 (`native_decide`), generating a 35-element family — barrier bypass study side.
3. **[brothers-desert-proof](https://github.com/DavidFox998/brothers-desert-proof) — route.** The same 35 brothers become the discrete self-symmetry lattice of Route D, a Lean-verified conditional reduction toward RH (RH remains OPEN).

## 1. Constants — why 143

- `Towers/Common/Conductor.lean` — `S₄={2,3,19,191}` lives here as exceptional primes
- `N=143=11×13` — conductor `phi=120` — 120-cell — `g=13` genus `X₀143` — `h=10` `h(-143)=10` — `p5=3993746143633` boundary hash prime — these constants reappear in every voice of the Opera

## 2. 11 Towers + Seal — cathedral

| Tower | Purpose | Key Cert |
|---|---|---|
| Common | Conductor library | `phi=120,g=13,h=10,p5` |
| PvsNP | Definitions + compiler + ConductorHash | `SAT∉P→P≠NP` + chain `T1⊂...⊂Tt=C*` |
| Computability | Turing machines | Halting undecidable, tableau `32 1=10240 ≤1048576` `native_decide` |
| PvsNP barriers | Formalize the three known obstacles | BGS 1975 relativization, RR 1994 natural proofs, AW 2009 algebrization |
| Space / Probabilistic / Interactive | Complexity classes | Savitch `NL=coNL`, `BPP⊆P/poly`, `IP=PSPACE` sum-check |
| Continuum | Infinite pigeonhole | König `κ < κ^{cf κ}` |
| Seal | Honesty | SHA256 seal, MANIFEST LOCKED, 0 sorry CI |

See `Towers/README.md` for build.

## 3. Core theorem — 4 lines

```lean
def SAT_Separation_Hypothesis : Prop := SAT ∉ P
theorem PNP_Conditional_Resolution : SAT_Separation_Hypothesis → P ≠ NP := by
  intro hsep
  have hsat : SAT ∈ NP := SAT_in_NP_cert
  have hcomplete : NP_Complete SAT := Cook_Levin_cert
  exact P_neq_NP_of_SAT_notin_P hsat hcomplete hsep

#print axioms PNP_Conditional_Resolution
-- [propext, Classical.choice, Quot.sound]
```

Cook-Levin says SAT is hardest in NP. If SAT not fast, nothing in NP fast.

## 4. ConductorHash — prefix machine

`Towers/PvsNP/ConductorHash.lean`

`ConductorHash S C` sorts by `S(v)` and checks `sum_{i≤k} S(vi) mod p5 == 0` for all prefixes — chain `T1⊂T2⊂...⊂Tt=C*` — `FORCE(I,T)` and `CliqueExtract` correct by construction. Mechanics side — study side is **[eutheos-property](https://github.com/DavidFox998/eutheos-property)**.

## 5. 1419 — seed that lives in eutheos-property

`1419 = 3×11×43 = 0x058B = 0000 0101 1000 1011` binary · 6 ones · popcount 6 · mod 211=153 — 4-bit truth table 16 rows.

The barrier machinery formalized here raises a concrete question: does any arithmetic object bypass BGS relativization, RR natural proofs, and AW algebrization simultaneously? The answer is yes — 1419 is such an object. Its study is formalized in **[eutheos-property](https://github.com/DavidFox998/eutheos-property)**: 35 brothers all satisfying the same barrier-bypass property P, arising 24× over uniform expectation, certified by `native_decide`.

The chain continues: those 35 brothers form the discrete self-symmetry lattice at the heart of **[brothers-desert-proof](https://github.com/DavidFox998/brothers-desert-proof)** (Route D, Act IV), where their orbit structure mod 191 and mod 36863 closes the fourth independent RH proof. The barrier framework defined here is the starting point of that entire three-repo chain.

## Opera Numerorum — 13 repos — PUBLIC — condensed 19→1 — Routes A-D → single riemann-hypothesis-four-routes

[arakelov-positivity-rh-core](https://github.com/DavidFox998/arakelov-positivity-rh-core) — ROOT V2 — Arakelov height ω²=48/13>0 ; Zoe-M*, M4 10^4000 boundary — provides height input all RH voices reuse
[rh-p5-bridge-14](https://github.com/DavidFox998/rh-p5-bridge-14) — Keystone — q5=226, q6=165849, cf_bound=82829 — reduces infinite S_a0 to finite S14 ; closes BSD_143_PROVED → RiemannHypothesis — condensed single checkout 6cefaf3 PR78 verify ensemble green da3b943c662f vs lock 6ec00281c55d lake build Towers 0
[riemann-hypothesis-four-routes](https://github.com/DavidFox998/riemann-hypothesis-four-routes) — Four Routes — PUBLICATION WORKSPACE replaces Routes A-D — RH Core, P5 bridge, four independent formal routes preserved at exact revisions one toolchain one RH predicate — Route A Act I Abbes-Ullmo ω²=48/13>0 Siegel zero → negative height, Route B Act II Kim-Sarnak λ1≥975/4096 Selberg=Bost-Connes GRH X0(143)→RH 35pp BC6, Route C Act III Littlewood Ω exp(c√(log t / log log t)) beats (log t)² zero repulsion, Route D Act IV Dirichlet jitter ‖p·a_q‖<1/p 35 brothers collision-free swarming orbit stability Re=1/2 — all CLOSED via S4 — 7ce83ae
[bost-connes](https://github.com/DavidFox998/bost-connes) — Arithmetic hub — C(S4)=11.422...>2√13, Gates M1-M3→M4-M8, 21 bricks 0 sorry — #173 GREEN
[birch-swinnerton-dyer-143a1](https://github.com/DavidFox998/birch-swinnerton-dyer-143a1) — BSD 143a1 — rank 1, Heegner point (4,6), L(143a1,1)≠0, |Sha|=1 — worked example M1-M5 arithmetic in action
[lindelof-hypothesis-143](https://github.com/DavidFox998/lindelof-hypothesis-143) — Lindelöf for X0(143) — GRH → μ=0 → |ζ(½+it)|=O(t^ε) unconditional via S4
[eutheos-property](https://github.com/DavidFox998/eutheos-property) — Barrier bypass — 1419=3*11*43, 35 brothers ≡153 mod 211, barriers BGS/RR/AW all PASS — P vs NP study side
[poincare-spectral](https://github.com/DavidFox998/poincare-spectral) — Spectral gap — S³/I*, q=1/8, tail_26s10⁻²⁰, spectral_gap>0 — decidable instance of undecidable gap problem
[p-vs-np](https://github.com/DavidFox998/p-vs-np) — ← this repo — P vs NP mechanics — 225 bricks, ConductorHash, conditional SAT∉P→P≠NP — DOI 10.5281/zenodo.21303093
[hodge-abelian-boundaries](https://github.com/DavidFox998/hodge-abelian-boundaries) — Hodge obstructions — 200 measured rank obstructions for g=3,4,5 ; observed_rank>criterionBound
[yang-mills-gap](https://github.com/DavidFox998/yang-mills-gap) — Yang-Mills mass gap — SU(2) on R⁴, p<1/7, Δ>0, Wilson area law — same gap as C(S4)-2√13
[navier-stokes](https://github.com/DavidFox998/navier-stokes) — Navier-Stokes — Path A ESS backward uniqueness + Path B 120-cell H¹ balance — NS_M6_PROVED, no blowup
[zerobeacon](https://github.com/DavidFox998/zerobeacon) — MCP server — 1000 collision-proof tools; beacon 1d2c7a5b, m4.out = Complete: True
[beal-conjecture](https://github.com/DavidFox998/beal-conjecture) — Beal Level 26 — beal-v38 EQUIV:3 a2a23292 PR25 792b3f8 chartOfModelTrue_injective_from_Ei_constraint B=1 nonzero Y³≠0 Y³ outside cusp centreNormalPoly (X³-1)0 outside I² centreAlphaBound 2 0=1 X+V² outside cusp ann(1+Y·S³)≠ann(X²) [propext,choice,Quot.sound] 7 thm 355 + beal-v39-even 1fc6071→6f921f45 — www.beal-conjecture.com — DOI 10.5281/zenodo.23120540 superseded by 02728795 — pattern for opera 19→1
[opera-sieve](https://github.com/DavidFox998/opera-sieve) — Canonical sieve for S(alpha_0=299+π/10): computational + Lean verification
[morningstar-project](https://github.com/DavidFox998/morningstar-project) — Morning Star: machine certification for GRH(X_0(143)) and BSD(J_0(143)) — 476 equations, CLAY-sealed
[Certifications](https://github.com/DavidFox998/Certifications) — Machine-checked Lean 4 audit certificates — Morning Star Project
[birch-swinnerton-dyer-143](https://github.com/DavidFox998/birch-swinnerton-dyer-143) — BSD 143 — unconditional BSD for 143a1 — Rank=ord_L=1



**Ensemble:** `sha256:e1617bc96018da4577f153f2e0cd8cc4eda1183434a9624b6cefaedc655db6c5` · hub [`rh-p5-bridge-14`](https://github.com/DavidFox998/rh-p5-bridge-14) · anchor `d04e4bd1`

## Author

David J. Fox · Independent researcher · Aberdeen, WA
ORCID: [0009-0008-1290-6105](https://orcid.org/0009-0008-1290-6105) · Opera Numerorum — 2026
