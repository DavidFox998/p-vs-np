# P vs NP Clay Tower

**Morning Star Project · Theorema Aureum 143**
Formal Lean 4 / Mathlib v4.12.0 tower for the Clay Millennium Prize
P vs NP problem.

## Status: OPEN (Clay) — Formal Tower Complete

P ≠ NP is an open problem. This tower provides:
- A rigorous abstract complexity model (BStr, Language, InP, InNP, IncoNP)
- 14 proved structural results (P⊆NP, P closed under complement/union/inter, etc.)
- Time and space hierarchy theorem structure (Phase 2)
- Boolean circuit complexity and Shannon counting bound (Phase 3)
- All three known proof barriers formalized (Phase 4):
  Relativization (BGS 1975), Natural Proofs (RR 1994), Algebrization (AW 2009)
- Cook-Levin theorem statement and SAT NP-completeness (Phase 3)
- Conditional Clay certificate: PNP_CLAY_CERTIFICATE (Phase 5)
- Total: ~223 proved bricks, 22 Lean files across 6 sub-towers (Phase 17)

## ⚠ Critical Honest Distinction vs NS Certificate ⚠

The NS tower cert axioms (Rellich-Kondrachov, BKM, etc.) are **proved results** in
the mathematical literature — the gap is Mathlib v4.12.0 formalization only.

`Cert_PNP_Separation` (SAT ∉ P) IS the Clay conjecture itself — not proved anywhere.
`PNP_CLAY_CERTIFICATE` formalizes "IF SAT ∉ P THEN P ≠ NP" — tautologically true.

## PNP_CLAY_CERTIFICATE Axiom Footprint

```
propext, Classical.choice, Quot.sound     ← classical trio (Lean core)
Cert_PNP_SAT_NP                           ← proved (Cook 1971, Mathlib gap)
Cert_PNP_SAT_NPhard                       ← proved (Cook 1971, Mathlib gap)
Cert_PNP_Separation                       ← ⚠ OPEN CONJECTURE (the Clay problem)
```

0 sorry. 0 sorryAx. 0 admit.

## Gate Structure

```
Gate 1: SAT ∈ NP (Cert_PNP_SAT_NP — proved, Cook 1971)
Gate 2: SAT ∉ P  (Cert_PNP_Separation — ⚠ OPEN CONJECTURE)
Combinator: Gate1 ∧ Gate2 → P ≠ NP (tautology)
```

## Proved Sub-Results (genuine, 0 conjectural axioms)

| Result | File | Method |
|--------|------|--------|
| P ⊆ NP | Complexity.lean | empty certificate |
| P = co-P | Complexity.lean | negate decider |
| P closed under union | Complexity.lean | OR deciders |
| P closed under intersection | Complexity.lean | AND deciders |
| PneNP ↔ ∃ L ∈ NP\P | Complexity.lean | logic |
| Poly bound sum/max closure | Complexity.lean | Nat arithmetic |
| P ⊆ EXP | Hierarchy.lean | n^k ≤ 2^{kn} |
| Both oracle worlds coexist | Barriers.lean | BGS 1975 |
| Shannon counting bound | CircuitComplexity.lean | counting |
| Relativizing proof must fail | Barriers.lean | BGS contradiction |

## Three Proof Barriers

| Barrier | Reference | What it rules out |
|---------|-----------|------------------|
| Relativization | Baker-Gill-Solovay 1975 | Diagonalization |
| Natural Proofs | Razborov-Rudich 1994 | Combinatorial lower bounds |
| Algebrization | Aaronson-Wigderson 2009 | Algebraic techniques |

## File Map

```
Towers/PvsNP/
  Complexity.lean         Phase 1 — BStr, Language, InP, InNP, P⊆NP
  Hierarchy.lean          Phase 2 — time hierarchy, padding, P≠EXP
  CircuitComplexity.lean  Phase 3 — circuits, Shannon bound, Cook-Levin
  Barriers.lean           Phase 4 — relativization, nat proofs, algebrization
  ClayStatement.lean      Phase 5 — clay combinator, PNP_CLAY_CERTIFICATE
  PvsNPCollection.lean    Collection — all phases indexed
  PvsNPCertificate.lean   Certificate — formal Clay audit
```

## Honest Scope

This tower does NOT prove:
- P ≠ NP (the Clay open problem — Cert_PNP_Separation is the conjecture itself)
- Any super-polynomial circuit lower bounds for SAT
- Resolution of the relativization/natural proofs/algebrization barriers
- Any Clay prize claim

---
Repo: `DavidFox998/p-vs-np` · Project: Morning Star / Theorema Aureum 143
Toolchain: leanprover/lean4 v4.12.0, Mathlib v4.12.0

---

## Yang-Mills Tower Status (July 1 2026)

The YM Tower for this project network reached formalization complete on July 1 2026.

**Clay YM Problem — Two Parts:**

**Part 1 (Existence):** Lattice SU(3) YM existence infrastructure proved in Lean:
`haarSU3` + `PeterWeyl_Summable_SU3` + `kp_lattice_gap_certified` (all 0 sorry, classical trio).
OS / Wightman continuum reconstruction: OPEN (Clay Surface #1).

**Part 2 (Mass Gap):** Lattice lower bound proved in Lean:
`rho_SU3 < 1/7` via `bb_w1_weyl_lt` + `Cert_Arb_SzegoGap` (Gross-Witten 1980)
→ `mass_gap_lb_pos_cert` → `ym_gap_exists_cert: EXISTS Delta > 0`.
Axioms: `{propext, Classical.choice, Quot.sound, Cert_Arb_SzegoGap}`. 0 sorry.
YM Surface #1 (continuum mass gap): LOCKED OPEN — Clay Millennium Problem.

Repo: [yang-mills-gap](https://github.com/DavidFox998/yang-mills-gap) | DOI: 10.5281/zenodo.20670857
