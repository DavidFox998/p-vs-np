# PvsNP — Conditional Compiler + ConductorHash + Barriers — Core Tower

The tower the repo is named for: the complexity-class model, the three barrier formalizations, the ConductorHash machine, and the conditional resolution certificate.

## Overview

Everything here speaks one language, defined in `Complexity.lean`: languages are sets of boolean strings (`BStr := List Bool`), `InP` means a polynomial-time decider exists, `InNP` means a polynomial-time verifier `V w c` exists, and `PeqNP := ∀ L, InNP L → InP L`. On top of that model the tower builds four things:

1. **The separation model** — `P_subset_NP`, `PneNP_iff`, closure properties, and the conditional resolution `PNP_Conditional_Resolution : SAT ∉ P → P ≠ NP` (Cook-Levin + verifier certificates).
2. **The hierarchy scaffolding** — time/space hierarchy, padding argument, the polynomial hierarchy (`PH.PHSigma/PHPi/PHDelta`), Karp-Lipton fully graduated (`karp_lipton_main`), counting classes (#P, PP), descriptive complexity (∃SO, Fagin witnesses), EF games.
3. **The barriers** — `Barriers.lean` formalizes the three known obstacles: BGS relativization (oracle worlds `RelativePeqNP A` and its negation both consistent — `barrier_relativization_consistency`), RR natural proofs (`Cert_PNP_NaturalProofs`), AW algebrization (`algebrization_both_worlds`). Conclusion: **`relativizing_proof_must_fail`** — a relativizing proof of P≠NP cannot exist.
4. **The ConductorHash machine** — sorts blocks by seed `S`, checks `sum_{i≤k} S(vi) mod p5 == 0` for every prefix (`IsPrefixRespecting`), with `FORCE`/`CliqueExtract` and the collapse conditional `conditional_collapse_becomes_unconditional`. This is the machine that asked the question answered by the companion repo [eutheos-property](https://github.com/DavidFox998/eutheos-property): witness 1419 = 3×11×43, exact 9-gate complexity, bypasses all three barriers.

## Files

| File | Role |
|---|---|
| `Complexity.lean` | Core model: `BStr`, `Language`, `InP`, `InNP`, `PeqNP`, `PneNP`, closure theorems |
| `Hierarchy.lean` | Time/space hierarchy axioms, padding `PeqNP ↔ EXP=NEXP` |
| `CircuitComplexity.lean` | `PolyCircuitFamily`, Shannon counting `num_bool_funs`, `SATLanguage`, Cook-Levin cert axiom |
| `Barriers.lean` | BGS oracle axioms, RR natural proofs, AW algebrization — `relativizing_proof_must_fail` |
| `ClayStatement.lean` | `PNP_ClayStatement := PneNP`, gates, `PNP_CLAY_CERTIFICATE` (conditional on `Cert_PNP_Separation`) |
| `ConductorHash.lean` | `ConductorHash`, `IsPrefixRespecting`, `FORCE`, collapse conditional — 4 marked open points |
| `PolynomialHierarchy.lean` | `PHSigma/PHPi/PHDelta`, collapse under PeqNP |
| `KarpLipton.lean` | **Fully graduated** — `karp_lipton_main`, 0 axioms 0 sorry |
| `PHStructure.lean` | Pure PH structure — 0 axioms 0 sorry |
| `CountingComplexity.lean` | #P, PP, ParityP; Valiant/Toda cert axioms |
| `DescriptiveComplexity.lean` | ∃SO sentences, `StructLangInNP`, Fagin/Immerman-Vardi cert axioms |
| `FaginFragment.lean` | Genuine 3-COLOR Fagin witness — 0 axioms 0 sorry |
| `ImmermanVardi.lean` | Knaster–Tarski least fixed points |
| `EFGames.lean` | EF-game scaffold (unregistered, flagged in-file) |
| `PvsNPCertificate.lean` | Audit re-exports + `PNP_CLAY_CERTIFICATE_FORMAL` |
| `PvsNPCollection.lean` | Single-import collection + tower metadata |

## Results

- **Proved (0 sorry, 0 axiom):** `P_subset_NP`, `PneNP_iff`, `Cert_PNP_NP_union/inter`, `Cert_PNP_poly_le_exp`, `shannon_counting_argument`, `fagin_witness_iff_colorable`, `LFP_is_fixed_point`, `karp_lipton_main`, `PHDelta_self_complement_succ`, EF-game equivalence basics.
- **Conditional (cert axioms, classical trio + documented certs):** `PNP_CLAY_CERTIFICATE : PneNP` via `pnp_clay_combinator ⟨Cert_PNP_SAT_NP, Cert_PNP_SAT_NPhard⟩ Cert_PNP_Separation` — `Cert_PNP_Separation : ¬InP SATLanguage` **is the Clay conjecture itself**, stated as an axiom, labeled as such.
- **Open (4 marked sorries in `ConductorHash.lean`):** `conductorHash_prefix_respecting`, `hash_extendability_by_construction`, `cliqueExtract_correct_with_conductorHash`, `conditional_collapse_becomes_unconditional` — each carries an in-file note on the intended closure lemma.

## Methodology

- Definitions-first: every class is an existential over deciders/verifiers, nothing is named into existence.
- Cert axioms (`Cert_PNP_*`) are labeled empirical-math dependencies: literature theorems imported as data, each with a citation comment. The one conjecture-shaped axiom, `Cert_PNP_Separation`, is the open problem — deliberately visible, not hidden.
- No `native_decide` in this tower — everything is combinatorial over finite strings or existsentially structured.

## Empirical Math Dependency

- Cook–Levin (1971) — `Cert_PNP_CookLevin`
- BGS relativization (Baker–Gill–Solovay 1975) — `Cert_PNP_Oracle_PeqNP/PneqNP`
- RR natural proofs (Razborov–Rudich 1994) — `Cert_PNP_NaturalProofs`
- AW algebrization (Aaronson–Wigderson 2009) — `Cert_PNP_Algebrization`
- Karp–Lipton (1980), Hartmanis–Stearns, Valiant (1979), Toda (1991), Fagin (1974), Immerman–Vardi (1982)
- Axioms: classical trio `[propext, Classical.choice, Quot.sound]` plus the `Cert_PNP_*` cert axioms above

## Dependencies

`Towers/Common/Conductor.lean` (p5, h_class data), Mathlib v4.15.0. Companion study side: [eutheos-property](https://github.com/DavidFox998/eutheos-property) — the concrete barrier-bypassing witness 1419 (exact 9 gates via `native_decide`, density 1/211, residue 153, 35 brothers), template for the ConductorHash bypass.
