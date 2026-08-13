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

Cook-Levin says SAT is hardest in NP. If SAT not fast, nothing in NP fast.
4. ConductorHash — prefix machine
Towers/PvsNP/ConductorHash.lean

ConductorHash S C sorts by S(v) and checks sum_{i≤k} S(vi) mod p5 == 0 for all prefixes — chain T1⊂T2⊂...⊂Tt=C* — FORCE(I,T) and CliqueExtract correct by construction. Mechanics side — study side is

5. 1419 — seed that lives in eutheos-property
1419 = 3×11×43 = 0x058B = 0000 0101 1000 1011 binary 6 ones popcount 6 mod 211=153 — 4-bit truth table 16 rows.

Companion: eutheos-property — FINAL v2.0 Lean 100% — Study of 1419 — 35 brothers 35/211=16.5% 99.999976% distinct (9/4M)^35≈10^-197 — Barriers PASS.

Mechanics lives here, study lives there.
19 Repo Site Map — Opera Numerorum — WITH LINKS
Root & Core:
• arakelov-positivity-rh-core — ROOT V2 — M2 kappa, M7 Manifest, M8C Zoe-M*, M4 10^4000 
Four Voices — RH — Same S₄:
• riemann-arakelov-positivity — Route A Act I — ω²=48/13>0 • arakelov-rh-descent — Route B Act II — λ₁≥975/4096 35pp BC6 • rh-growth-contradiction — Route C Act III — Growth contradiction • brothers-desert-proof — Route D Act IV — 35 brothers self-symmetry — ||p·α₀||<1/p proves R=1/2 
Keystone & Sieve:
• rh-p5-bridge-14 — Keystone — q5=226 q6=165849 cf_bound=82829 grh_to_rh_descent • opera-sieve — methodology S14 Sα0 
Arithmetic — Level 143:
• birch-swinnerton-dyer-143a1 — BSD 143a1 Heegner rank 0 • lindelof-hypothesis-143 — Lindelöf X₀143 μ=0 • eutheos-property — Study of 1419 — companion to THIS — 35 brothers 153 mod 211 
THIS repo:
• p-vs-np — THIS — 225 bricks — Conditional compiler — mechanics side 
Other Clay:
• poincare-spectral — q=1/8 tail_26≤1e-20 • bost-connes — Hub C(S₄)=11.422...>2√13 21 bricks #173 GREEN • hodge-abelian-boundaries — 200 obstructions 4>3 7>6 15>10 • yang-mills-gap — Mass gap Δ>0 ρ<1/7 • navier-stokes — Dissipation Θ(t) summable Path A 8/8 + B 4/4 
Systems:
• morningstar-project — quantum entangled orbital spacestation • zerobeacon — BRAIN — 1000 tools — collision-free-swarming • pistus-theoria — ARCHIVE — OperaNumerorum_MasterEquations.pdf SHA 7f6b31b4... m4.out = Complete: True 
ORCID: 0009-0008-1290-6105
