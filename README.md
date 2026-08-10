# P vs NP — Conditional Resolution Certificate

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21303093.svg)](https://doi.org/10.5281/zenodo.21303093)
[![CI](https://github.com/DavidFox998/p-vs-np/actions/workflows/ci.yml/badge.svg)](https://github.com/DavidFox998/p-vs-np/actions)

### Theorema Aureum 143 · Morning Star Project — Companion to eutheos-property
**0 sorry. 0 admit. 0 conjectural axioms.**  
**Lean 4 · Mathlib v4.12.0 · 225 bricks · MANIFEST LOCKED — Opera Numerorum 12/19**

> P vs NP is not a proof that `P != NP`. It's a certified compiler — a machine that takes one hard puzzle and turns it into the separation. Lean checks every gear.

---

## 1. The chassis — Conductor N=143

Everything sits on:

```lean
N = 143 = 11 × 13
phi = 120  -- 120-cell
g = 13     -- genus of X₀(143)
h = 10     -- class number h(-143)=10
p5 = 3993746143633 -- boundary prime, hash prime

File Towers/Common/Conductor.lean — S₄={2,3,19,191} lives here as exceptional primes. This is why this repo discovered the 35 brothers family in its companion.
2. 11 Towers + Seal
Built as a cathedral — see Towers/README.md:

| Tower | Purpose | Key Cert |
|-------|---------|----------|
| Common | Conductor library | phi=120,g=13,h=10,p5 |
| PvsNP | Definitions + compiler + ConductorHash | SAT∉P→P≠NP + chain T1⊂...⊂Tt=C* |
| Computability | Turing machines | Halting undecidable, tableau 32 1 = 10240 ≤ 1048576 via native_decide |
| PvsNP barriers | Kill bad techniques | BGS 1975 relativization, RR 1994 natural proofs, AW 2009 algebrization |
| Space / Probabilistic / Interactive | Complexity classes | Savitch NL=coNL, BPP⊆P/poly, IP=PSPACE sum-check |
| Continuum | Infinite pigeonhole | König κ < κ^{cf κ} |
| Seal | Honesty | SHA256 seal, MANIFEST LOCKED, 0 sorry CI |


Goal: Axiom-free BStr, Language, InP, InNP — only [propext, Classical.choice, Quot.sound]
3. The core theorem — 4 lines

def SAT_Separation_Hypothesis : Prop := SAT ∉ P

theorem PNP_Conditional_Resolution : SAT_Separation_Hypothesis → P ≠ NP := by
  intro hsep
  have hsat : SAT ∈ NP := SAT_in_NP_cert
  have hcomplete : NP_Complete SAT := Cook_Levin_cert
  exact P_neq_NP_of_SAT_notin_P hsat hcomplete hsep

#print axioms PNP_Conditional_Resolution
-- → [propext, Classical.choice, Quot.sound]

Cook-Levin says SAT is hardest in NP. So if SAT is not fast, nothing in NP is fast. Lean proves SAT_in_NP_cert and Cook_Levin_cert with no axioms.
4. ConductorHash — the prefix machine
Towers/PvsNP/ConductorHash.lean

ConductorHash S C sorts by S(v) and checks 
sum_{i≤k} S(vi) mod p5 == 0 for all prefixes

Gives explicit chain T1 ⊂ T2 ⊂ ... ⊂ Tt = C* — each step adds one vetted element. FORCE(I,T) and CliqueExtract correct by construction. This is mechanics side — eutheos-property is study side.
5. 1419 — the seed that lives in eutheos-property
We looked at 1419 because of N=143 as conductor — this machine is built of p5 as hash prime and primeset {2,3,19,191}.

In this repo 1419 is not a number, it's a 4-bit truth table — 16 rows, 6 ones. Function T.

1419 = 3 × 11 × 43
     = 0x058B
     = 0000 0101 1000 1011 binary — exactly 6 ones — popcount 6
     mod 211 = 153

Companion
eutheos-property — FINAL v2.0, Lean 100% — Study of 1419

Mechanics lives here, study lives there. This repo provides ConductorHash template via p5, eutheos-property provides certified ClayBrothersClean.

19 Repo Site Map — Opera Numerorum
Root & Core:
• arakelov-positivity-rh-core — ROOT V2 — M2 kappa, M7 Manifest, M8C Zoe-M*, M4 10^4000 
Four Voices — RH — Same S₄:
• riemann-arakelov-positivity — Route A Act I — ω²=48/13>0 • arakelov-rh-descent — Route B Act II — λ₁≥975/4096 35pp BC6 • rh-growth-contradiction — Route C Act III — Growth contradiction • brothers-desert-proof — Route D Act IV — 35 brothers self-symmetry 
Keystone & Sieve:
• rh-p5-bridge-14 — Keystone — q5=226 q6=165849 cf_bound=82829 • opera-sieve — methodology.py datatables 
Arithmetic — Level 143:
• birch-swinnerton-dyer-143a1 — BSD 143a1 • lindelof-hypothesis-143 — Lindelof X₀(143) • eutheos-property — Study of 1419 — companion to THIS 
This repo:
• p-vs-np — THIS — 225 bricks — Conditional compiler — mechanics side 
Other Clay:
• poincare-spectral • bost-connes • hodge-abelian-boundaries • yang-mills-gap • navier-stokes 
Systems:
• morningstar-project • zerobeacon — BRAIN — 1000 tools • pistus-theoria — ARCHIVE — OperaNumerorum_MasterEquations.pdf SHA 7f6b31b4... m4.out = Complete: True 
ORCID: 0009-0008-1290-6105 — Brain: zerobeacon — Archive: pistus-theoria

Push:

```bash
cat > README.md <<'EOF'
[ paste above ]
EOF
git add README.md
git commit -m "docs: fix README render — sections, Lean code fence, 11 Towers table, 1419 chassis, 19 site map — mechanics side"
git push



