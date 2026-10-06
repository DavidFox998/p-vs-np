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

## Opera Numerorum — ensemble map

**[arakelov-positivity-rh-core](https://github.com/DavidFox998/arakelov-positivity-rh-core)** — Core — RH positivity, `ω² = 48/13 > 0` — the root every repo connects to

*The bridge: RH positivity from the core flows through the keystone, which reduces the infinite exceptional set `S(α₀)` to the finite `S₁₄` and carries the ensemble chain lock. Every repo below works from the bridge.*

**[rh-p5-bridge-14](https://github.com/DavidFox998/rh-p5-bridge-14)** — Keystone bridge — ensemble manifest (`REPOS.md`) and chain lock

**[riemann-hypothesis-four-routes](https://github.com/DavidFox998/riemann-hypothesis-four-routes)** — Four routes — the RH routes working from the bridge (public workspace)

**[birch-swinnerton-dyer-143](https://github.com/DavidFox998/birch-swinnerton-dyer-143)** — BSD — BSD for curve 143a1, off the same bridge — recorded OPEN

**[poincare-spectral](https://github.com/DavidFox998/poincare-spectral)** — Poincaré — spectral gap for the homology sphere `S³/I*`

**[lindelof-hypothesis-143](https://github.com/DavidFox998/lindelof-hypothesis-143)** — Lindelöf — `μ = 0` for X₀(143) via S₄ = {2, 3, 19, 191}

**[navier-stokes](https://github.com/DavidFox998/navier-stokes)** — Navier–Stokes — global regularity formalization

**[yang-mills-gap](https://github.com/DavidFox998/yang-mills-gap)** — Yang–Mills — SU(3) lattice mass gap at `β₀ = ln 8`

**[p-vs-np](https://github.com/DavidFox998/p-vs-np)** — P vs NP — **This Repo** — mechanics; conditional `SAT ∉ P → P ≠ NP`

**[eutheos-property](https://github.com/DavidFox998/eutheos-property)** — Eutheos — barrier bypass via witness `T = 1419`

**[bost-connes](https://github.com/DavidFox998/bost-connes)** — Bost–Connes — arithmetic hub; `C(S₄) = 11.422 > 2√13`

**[zerobeacon](https://github.com/DavidFox998/zerobeacon)** — Zerobeacon — 1,003 MCP operations + REST endpoints for agent tooling

**[beal-conjecture](https://github.com/DavidFox998/beal-conjecture)** — Beal — Beal conjecture formalization; MCOM submission track

**[birch-swinnerton-dyer-143a1](https://github.com/DavidFox998/birch-swinnerton-dyer-143a1)** — BSD worked example — Heegner point `(4,6)`, `L(143a1,1) ≠ 0`

**[hodge-abelian-boundaries](https://github.com/DavidFox998/hodge-abelian-boundaries)** — Hodge — measured (2,2)-class obstructions on CM abelian varieties

**[morningstar-project](https://github.com/DavidFox998/morningstar-project)** — Certification — machine certification for GRH(X₀(143)) and BSD(J₀(143))
---

**Ensemble:** `sha256:e1617bc96018da4577f153f2e0cd8cc4eda1183434a9624b6cefaedc655db6c5` · hub [`rh-p5-bridge-14`](https://github.com/DavidFox998/rh-p5-bridge-14) · anchor `d04e4bd1`

## Author

David J. Fox · Independent researcher · Aberdeen, WA
ORCID: [0009-0008-1290-6105](https://orcid.org/0009-0008-1290-6105) · Opera Numerorum — 2026
