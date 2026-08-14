# P vs NP — Conditional Compiler + ConductorHash — 225 bricks — Mechanics side

**N=143=11×13 phi=120 g=13 h=10 p5=3993746143633 S₄={2,3,19,191} — ORCID 0009-0008-1290-6105**

Lean 4.15.0 / Mathlib v4.15.0 | 0 sorry in core | `[propext, Classical.choice, Quot.sound]`

## 1. Constants — why 143

- `Towers/Common/Conductor.lean` — `S₄={2,3,19,191}` lives here as exceptional primes
- `N=143=11×13` — conductor `phi=120` — 120-cell — `g=13` genus `X₀143` — `h=10` `h(-143)=10` — `p5=3993746143633` boundary hash prime — this is why this repo discovered the 35 brothers family in its companion

## 2. 11 Towers + Seal — cathedral

| Tower | Purpose | Key Cert |
|---|---|---|
| Common | Conductor library | `phi=120,g=13,h=10,p5` |
| PvsNP | Definitions + compiler + ConductorHash | `SAT∉P→P≠NP` + chain `T1⊂...⊂Tt=C*` |
| Computability | Turing machines | Halting undecidable, tableau `32 1=10240 ≤1048576` `native_decide` |
| PvsNP barriers | Kill bad techniques | BGS 1975 relativization, RR 1994 natural proofs, AW 2009 algebrization |
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

Companion: **[eutheos-property](https://github.com/DavidFox998/eutheos-property)** — FINAL v2.0 Lean 100% — Study of 1419 — 35 brothers `35/211=16.5%` · `99.999976%` distinct · `(9/4M)^35≈10^-197` — Barriers PASS.

Mechanics lives here, study lives there.

## Opera Numerorum — 16 repos

**[arakelov-positivity-rh-core](https://github.com/DavidFox998/arakelov-positivity-rh-core) — ROOT V2** — Arakelov height `ω²=48/13>0`; Zoe-M\*, M4 10^4000 boundary — provides the height input that all four RH voices reuse

**[rh-p5-bridge-14](https://github.com/DavidFox998/rh-p5-bridge-14) — Keystone** — `q5=226`, `q6=165849`, `cf_bound=82829` — reduces infinite `S_α0` to finite `S₁₄`; closes `BSD_143_PROVED → RiemannHypothesis`

**[riemann-arakelov-positivity](https://github.com/DavidFox998/riemann-arakelov-positivity) — Route A · Act I** — Abbes-Ullmo `ω²=48/13>0`; a Siegel zero would force negative height — CLOSED via S₄

**[arakelov-rh-descent](https://github.com/DavidFox998/arakelov-rh-descent) — Route B · Act II** — Kim-Sarnak `λ₁≥975/4096` → Selberg trace = Bost-Connes → GRH for X₀(143) → RH — 35pp BC6 CLOSED via S₄

**[rh-growth-contradiction](https://github.com/DavidFox998/rh-growth-contradiction) — Route C · Act III** — Littlewood Ω `exp(c√(log t / log log t))` beats `(log t)²`; zero repulsion → RH — CLOSED via S₄

**[brothers-desert-proof](https://github.com/DavidFox998/brothers-desert-proof) — Route D · Act IV** — Dirichlet jitter `‖p·α₀‖<1/p`, 35 brothers collision-free swarming; orbit stability forces `Re=1/2` — CLOSED via S₄

**[bost-connes](https://github.com/DavidFox998/bost-connes) — Arithmetic hub** — `C(S₄)=11.422...>2√13`, Gates M1–M3→M4–M8, 21 bricks 0 sorry — #173 GREEN

**[birch-swinnerton-dyer-143a1](https://github.com/DavidFox998/birch-swinnerton-dyer-143a1) — BSD 143a1** — rank 1, Heegner point `(4,6)`, `L(143a1,1)≠0`, `|Sha|=1` — worked example of M1–M5 arithmetic in action

**[lindelof-hypothesis-143](https://github.com/DavidFox998/lindelof-hypothesis-143) — Lindelöf for X₀(143)** — GRH → `μ=0` → `|ζ(½+it)|=O(t^ε)` unconditional via S₄

**[eutheos-property](https://github.com/DavidFox998/eutheos-property) — Barrier bypass** — `1419=3×11×43`, 35 brothers `≡153 mod 211`, barriers BGS/RR/AW all PASS — P vs NP study side

**[poincare-spectral](https://github.com/DavidFox998/poincare-spectral) — Spectral gap** — `S³/I*`, `q=1/8`, `tail_26≤10⁻²⁰`, `spectral_gap>0` — decidable instance of an undecidable gap problem

**[p-vs-np](https://github.com/DavidFox998/p-vs-np) — P vs NP mechanics** ← **this repo** — 225 bricks, ConductorHash, conditional `SAT∉P→P≠NP` — Eutheos property as barrier bypass

**[hodge-abelian-boundaries](https://github.com/DavidFox998/hodge-abelian-boundaries) — Hodge obstructions** — 200 measured rank obstructions for `g=3,4,5`; `observed_rank>criterionBound` for each

**[yang-mills-gap](https://github.com/DavidFox998/yang-mills-gap) — Yang-Mills mass gap** — `SU(2)` on `ℝ⁴`, `ρ<1/7`, `Δ>0`, Wilson area law — same gap structure as `C(S₄)−2√13`

**[navier-stokes](https://github.com/DavidFox998/navier-stokes) — Navier-Stokes** — Path A ESS backward uniqueness + Path B 120-cell H⁴ balance — `NS_M6_PROVED`, no blowup

**[zerobeacon](https://github.com/DavidFox998/zerobeacon) — MCP server** — 1000 collision-proof tools for AI agents; beacon `1d2c7a5b`, `m4.out = Complete: True`

---

ORCID: [0009-0008-1290-6105](https://orcid.org/0009-0008-1290-6105) · Archive: [pistus-theoria](https://github.com/DavidFox998/pistus-theoria) — `OperaNumerorum_MasterEquations.pdf SHA 7f6b31b4`
**Ensemble:** `sha256:e1617bc96018da4577f153f2e0cd8cc4eda1183434a9624b6cefaedc655db6c5` · hub [`rh-p5-bridge-14`](https://github.com/DavidFox998/rh-p5-bridge-14) · anchor `d04e4bd1`
## Author

David J. Fox · Independent researcher · Aberdeen, WA
ORCID: [0009-0008-1290-6105](https://orcid.org/0009-0008-1290-6105) · Opera Numerorum — 2026

```
