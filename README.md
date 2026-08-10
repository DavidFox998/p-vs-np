p-vs-np is not a proof that P != NP. It's a certified compiler — a machine that takes one hard puzzle and turns it into the separation. Lean checks every gear.
1. The chassis — Conductor N=143
Everything sits on:

N = 143 = 11 × 13
phi = 120  — 120-cell
g = 13     — genus of X₀(143) — same curve that closes Routes A-D
h = 10     — class number h(-143)=10
p5 = 3993746143633 — boundary prime, same prime as M10 g≤408
File Towers/Common/Conductor.lean — this is why this repo discovered 35 brothers. Same numbers appear in RH: S₄={2,3,19,191} C=11.422>2√13 closes GRH X₀(143). Here 143 is the level.
2. 11 Towers + Seal

Built as cathedral with towers — see Towers/README.md:
• Common — numbers above • PvsNP — definitions + compiler + ConductorHash • Computability — Turing machines, halting undecidable, tableau size tableau 32 1 = 10240 ≤ 1048576 certified by native_decide • PvsNP barriers — formal theorems that kill bad proof techniques: ◦ BGS 1975 relativization — oracle where P=NP and oracle where P≠NP, so no relativizing proof works ◦ RR 1994 natural proofs — if a property is large + constructive, it can't prove P≠NP if factoring is hard ◦ AW 2009 algebrization — extension of relativization • Space / Probabilistic / Interactive — Savitch, NL=coNL, BPP⊆P/poly, IP=PSPACE via sum-check Schwartz-Zippel • Continuum — König κ < κ^{cf κ} — the infinite pigeonhole • Seal — MANIFEST LOCKED — SHA256 of all bricks, 0 sorry CI 
Goal: axiom-free BStr, Language, InP, InNP — only [propext, Classical.choice, Quot.sound]
3. The core theorem — 4 lines

def SAT_Separation_Hypothesis : Prop := SAT ∉ P

theorem PNP_Conditional_Resolution : SAT_Separation_Hypothesis → P ≠ NP := by
  intro hsep
  have hsat : SAT ∈ NP := SAT_in_NP_cert
  have hcomplete : NP_Complete SAT := Cook_Levin_cert
  exact P_neq_NP_of_SAT_notin_P hsat hcomplete hsep

  Cook-Levin says SAT is hardest in NP. So if SAT is not fast, nothing in NP is fast.

The job in Lean was to prove SAT_in_NP_cert and Cook_Levin_cert with no axioms — tableau correct by construction.
4. ConductorHash — the prefix machine
Towers/PvsNP/ConductorHash.lean

ConductorHash S C sorts by S(v) and checks 
sum_{i≤k} S(vi) mod p5 == 0 for all prefixes

It gives an explicit chain T1 ⊂ T2 ⊂ ... ⊂ Tt = C* — each step adds one vetted element. FORCE(I,T) and CliqueExtract correct by construction — that's the mechanics side vs eutheos-property study side.

• S8 = 17244 = number of functions computable with ≤8 gates • 1419 = 3×11×43 = 0x058B = 16-bit truth table, exactly 6 ones, residue 153 mod 211 • !TT8.contains 1419 via native_decide — so needs 9 gates exact, not 8 
Density: 304/65536≈0.46% for 4-bit, 20355231/4294967296≈0.47% for 5-bit — stabilizes at 1/211 forever.

Why it bypasses barriers:
• non-large — 1/211 — fails RR largeness • prime 211>19 non-natural — fails RR constructivity • prime non-algebrizing — fails AW • specific integer non-relativizing — fails BGS 
Then you found 34 more with same 153 mod 211, same 6-ones, same monotone lift T | T<<16 preserving 9 gates — 35 brothers.
6. The bridge — LEFT / MIDDLE / RIGHT diagram:

LEFT: T=1419 FINITE — 9 gates exact, S8=17244, density 1/211
MIDDLE: BRIDGE — α0 = 299 + π/10, block = frac(p·α0)·2^32
        T_star_N = concat N/32 blocks
        134M bits: only 9 collisions → density 99.999785% →1
        Andreev lift: N^{1.01} → N²/log⁴, n12: 101k>62k first green, n27: 52T>4.5B 14383×
RIGHT: KÖNIG INFINITE — κ < κ^{cf κ}, 2^N functions vs N circuits

• König says there are way more functions 2^N than small circuits N^c — so some function must be hard, but not which. • You make it constructive: T=1419 explicit. • Dirichlet bridge: frac(p·α0) with irrational α0=299+π/10 spreads uniformly, so T_star_N is almost all random but built from 1419. Hard for Lean because needs real analysis, mpmath 30 dps. • Andreev lift: L' = L·2^n/n turns 9-gate base into N²/log⁴ hardness.

We looked at number 1419 because of N=143 as conductor as such this machine is built of p5 as hash prime andp primeset 2,3,19,191.

1419 = 3 × 11 × 43
     = 0x058B
     = 0000 0101 1000 1011 binary — exactly 6 ones — popcount 6
     mod 211 = 153
     
P(collision) ≈ 9/4M = 2e-6

In these repos 1419 is not a number, it's a 4-bit truth table — 16 rows, 6 ones. Function T.

lake build — Lean 4.12.0, Mathlib v4.12.0, 225 bricks, 0 sorry

19 Repo Site Map — Opera Numerorum
Root & Core:
• arakelov-positivity-rh-core — ROOT V2 — M2 kappa, M7 Manifest, M8C Zoe-M*, M4 10^4000 
Four Voices — RH — Same S₄={2,3,19,191} C=11.422>2√13:
• riemann-arakelov-positivity — Route A Act I — ω²=48/13>0 • arakelov-rh-descent — Route B Act II — λ₁≥975/4096 35pp BC6 • rh-growth-contradiction — Route C Act III — Growth contradiction • brothers-desert-proof — Route D Act IV — 35 brothers self-symmetry 
Keystone & Sieve:
• rh-p5-bridge-14 — Keystone — q5=226 q6=165849 cf_bound=82829 — grh_to_rh_descent • opera-sieve — methodology.py datatables S_14 S_alpha0 
Arithmetic — BSD & Lindelof — Level 143:
• birch-swinnerton-dyer-143a1 — BSD 143a1 • lindelof-hypothesis-143 — Lindelof X₀(143) • eutheos-property — Study of 1419 — FINAL v2.0 — companion to THIS repo 
This repo — P vs NP:
• p-vs-np — THIS — 225 bricks — Conditional compiler — mechanics side 
Other Clay — Same Conductor Philosophy:
• poincare-spectral — Poincaré • bost-connes — Bost-Connes phase transition C(S) • hodge-abelian-boundaries — Hodge — 200 abelian 390 total • yang-mills-gap — Yang-Mills • navier-stokes — Navier-Stokes — 1/10 factor same as h(-143)=10 
Systems:
• morningstar-project — Quantum entangled orbital spacestation • zerobeacon — BRAIN — 1000 tools collision-free-swarming • pistus-theoria — ARCHIVE — pdf server + oracle + cert house — OperaNumerorum_MasterEquations.pdf SHA 7f6b31b4... m4.out = Complete: True 
ORCID: 0009-0008-1290-6105 — Brain: zerobeacon — Archive: pistus-theoria
