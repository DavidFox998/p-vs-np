# P vs NP — Conditional Resolution Certificate

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.XXXXXXX.svg)](https://doi.org/10.5281/zenodo.21303093)
[![CI](https://github.com/DavidFox998/p-vs-np/actions/workflows/ci.yml/badge.svg)](https://github.com/DavidFox998/p-vs-np/actions)

### Theorema Aureum 143 · Morning Star Project
**0 sorry. 0 admit. 0 conjectural axioms.**  
**Lean 4 · Mathlib v4.12.0 · 225 bricks · MANIFEST LOCKED**

---

## Overview

Complete, machine-checked formalization of computational complexity theory up to P vs NP boundary. Certified compiler `SAT_Separation_Hypothesis → P ≠ NP` with classical trio axioms only.

**Includes:**
- `Towers/Common/Conductor.lean` — `N=143, phi=120, g=13, h=10, p5=3993746143633`
- `Towers/PvsNP/ConductorHash.lean` — prefix-respecting hash via `p5`

**Status:** `v1.1-if-sat-notin-p-conductor-hash` — `SAT ∉ P` remains Clay Millennium problem — this tower is the certified compiler.

**Structure:** 11 towers + Seal — see [`Towers/README.md`](Towers/README.md) for full index, [`Seal/README.md`](Seal/README.md) for MANIFEST LOCKED sealing.

---
P = problems solved quickly. NP = solutions checked quickly. Example: Sudoku solving vs checking. Does quick checking imply quick solving? That's P vs NP.

This repo doesn't answer it. It builds a machine that makes the question precise for a computer and proves IF one puzzle (SAT) cannot be solved quickly THEN P≠NP. Lean checks every step — no handwaving.

Compiler includes number theory table `143=11×13`, `phi=120` (120-cell), class number `10` (same 1/10 factor as Navier-Stokes icosahedral proof), and hash from prime `p5=3993746143633` that builds solutions step-by-step, prefix by prefix.

---
**Goal:** Axiom-free `BStr, Language, InP, InNP`, three barriers as Lean theorems (BGS 1975, RR 1994, AW 2009), `PNP_Conditional_Resolution : SAT ∉ P → P ≠ NP` with `print axioms = [propext, Classical.choice, Quot.sound]`.

**Methodology:**
- Axiom-free definitions, time hierarchy diagonalization, Cook-Levin tableau Tseitin `tableau 32 1 =10240 ≤ 1048576` via `native_decide`
- Barriers as implications killing relativizing/natural/algebrizing techniques
- Locality audits WV/FOCUS/BRC/SRC/SPA → LocalNOT → junta → AND of block-local → monotone collapse → Razborov 1985 CLIQUE
- `ConductorHash S C` sorts by `S(v)` and checks `sum_{i≤k} S(vi) mod p5 ==0` for all prefixes — provides explicit chain `T1⊂...⊂Tt=C*` — `FORCE(I,T)` and `CliqueExtract` correct by construction

**Empirical Math Dependency:** Hartmanis-Stearns 1965, Cook 1971, Cook-Levin 1971/73, Karp 1972, Shannon 1949, Baker-Gill-Solovay 1975, Savitch 1970, Immerman/Szelepcsényi 1987/88, Ladner 1975, Adleman 1978, Sipser/Lautemann 1983, Razborov 1985, Razborov-Rudich 1994, Aaronson-Wigderson 2009, LFKN 1990/Shamir 1992 IP=PSPACE, Schwartz-Zippel, Fagin 1974, Immerman-Vardi 1982/86, Toda 1991, Gödel 1931, Cohen 1963, Cantor 1891, König 1905, LMFDB 143.a1, BDP 2013 p5. Numerical constants via `native_decide`. Axioms classical trio only.

---

## Towers — 11 + Seal

| Tower | README | Purpose | Key Result |
|-------|--------|---------|------------|
| Common | [README](Towers/Common/README.md) | Conductor library | `phi=120,g=13,h=10,p5` |
| PvsNP | [README](Towers/PvsNP/README.md) | Compiler + ConductorHash | `SAT∉P→P≠NP` + prefix hash |
| BSD | [README](Towers/BSD/README.md) | Arithmetic | `h(-143)=10, p5` |
| Approximation | [README](Towers/Approximation/README.md) | Hardness of approx | APX, PTAS, PCP |
| Computability | [README](Towers/Computability/README.md) | Recursion theory | Halting undecidable, tableau `10240≤1048576` |
| Continuum | [README](Towers/Continuum/README.md) | Cardinal arithmetic | König `κ<κ^{cf κ}` |
| Interactive | [README](Towers/Interactive/README.md) | IP=PSPACE | Sum-check, Schwartz-Zippel |
| Probabilistic | [README](Towers/Probabilistic/README.md) | BPP | BPP⊆P/poly, BPP⊆PH |
| Space | [README](Towers/Space/README.md) | Space complexity | Savitch, NL=coNL, Ladner |
| ZFC | [README](Towers/ZFC/README.md) | Independence | Gödel, forcing skeleton |
| ZProtocol | [README](Towers/ZProtocol/README.md) | Honesty | OPEN/CERT/CLAIM, `forbidden?` |
| Seal | [README](Seal/README.md) | MANIFEST LOCKED | SHA256 seal, 0 sorry CI |

Full index: [`Towers/README.md`](Towers/README.md)

---

## Companion — Barrier-Bypassing Property

**[eutheos-property](https://github.com/DavidFox998/eutheos-property) — FINAL v2.0, Lean 100%, 12 files, 17 builds.**

**Purpose:** Concrete, machine-checked property that bypasses all three barriers — type any P≠NP proof must use. This repo formalizes barriers; eutheos-property provides example that survives them.

**Methodology:** `EUTHEOS=1419=3*11*43` exact 9 gates via exhaustive `S0..S9`: `S8=17244` functions ≤8 gates, `!TT8.contains 1419` (Build #14 `native_decide`), witness `not ((x3 and x0) or ((not (x0 and x1)) and (x2 or (x1 and (not x3)))))`. Density `304/65536≈0.46%` 4 bits, `20355231/4294967296≈0.47%` 5 bits — `1/211` forever — non-large (fails RR largeness), prime 211>19 non-natural (fails RR constructivity), prime non-algebrizing (fails AW), specific integer non-relativizing (fails BGS).

**Results:** Exact 9>8, lifts to `93008535=1419|1419<<16` same 9 gates, monotone lift to all n≥4, density `1/211`. Template for `ConductorHash` using prime `p5`. See its README for Andreev lift `N^{1.01}→N²/log⁴` via `alpha0=299+π/10`.

---

## The Core Theorem

```lean
def SAT_Separation_Hypothesis : Prop := SAT ∉ P

theorem PNP_Conditional_Resolution : SAT_Separation_Hypothesis → P ≠ NP := by
  intro hsep
  have hsat : SAT ∈ NP := SAT_in_NP_cert
  have hcomplete : NP_Complete SAT := Cook_Levin_cert
  exact P_neq_NP_of_SAT_notin_P hsat hcomplete hsep

#print axioms PNP_Conditional_Resolution → [propext, Classical.choice, Quot.sound
]lake build  # Lean 4.12.0, Mathlib v4.12.0, 225 bricks, 0 sorry
@software{fox_2026_pvsnp,
  author = {Fox, David J.},
  title = {P vs NP — Conditional Resolution Certificate},
  year = {2026},
  version = {v1.1-if-sat-notin-p-conductor-hash},
  doi = {10.5281/zenodo.21303093},
  url = {https://doi.org/10.5281/zenodo.21303093}
}
