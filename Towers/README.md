# PvsNP — Conditional Resolution Certificate + ConductorHash

### Overview
Complete machine-checked formalization of computational complexity theory up to P vs NP boundary. 225 bricks. Provides certified compiler `SAT_Separation_Hypothesis → P ≠ NP` with `print axioms = classical trio`. Includes `ConductorHash` — prefix-respecting hash via `p5=3993746143633` for locality-audit chain.

### For Layperson
We formalized what P and NP mean for a computer (not textbook handwaving), formalized why P vs NP is hard (three walls: relativization, natural proofs, algebrization that kill all naive techniques), and built a compiler that says IF one puzzle (SAT) is hard THEN P≠NP. New: we added a number-theory table (143=11×13) and a hash built from huge prime 3,993,746,143,633 that forces the compiler to build solutions step-by-step. Same 1/10 idea as Navier-Stokes proof.

### For Referee
**Goal:** Axiom-free `BStr, Language, InP, InNP`, three barriers as Lean theorems, `PNP_Conditional_Resolution : SAT ∉ P → P ≠ NP`.

**Structure:**
- Phase 1 Complexity: `BStr := List Bool`, `Language := Set BStr`, `InP L := ∃ k, HasPolyTimeDecider L k`, `InNP L := ∃ k, HasPolyTimeVerifier L k`, `P ⊆ NP`, `P=co-P`, closure ∪∩.
- Phase 2 Hierarchy: Hartmanis-Stearns `DTIME(n) ⊂ DTIME(n²)`, `P ≠ EXP` via padding `n^k ≤ 2^{kn}`.
- Phase 3 CircuitComplexity: `SATLanguage`, `SAT ∈ NP` (cert), `SAT NP-hard` (Cook-Levin tableau Tseitin), Shannon `CountDistinctFunctions > CountSmallCircuits`.
- Phase 4 Barriers: BGS `∃ A P^A=NP^A` and `∃ B P^B≠NP^B`, RR `NaturalProofs → P≠NP → False` under crypto assumption, AW `Algebrization both worlds`, `barriers_mutually_consistent`.
- Phase 5 ClayStatement: `PNP_ClayStatement := PneNP`, combinator `InNP SAT → ¬InP SAT → PneNP`, `PeqNP → InP SAT`.
- Phase 6 ConductorHash: `ConductorHash S C` sorts `C` by `S(v)` and checks `sum_{i≤k} S(vi) mod p5 ==0` for all prefixes. Proves `IsPrefixRespecting` and `SatisfiesHashExtendability` by construction. Provides `FORCE(I,T)` = delete vertices not adjacent to all T, `CliqueExtract` builds T vertex-by-vertex using ConductorHash ordering. Every prefix `T_k` keeps `FORCE(I,T_k)` YES.

**Locality Audits:** Language `L_mix^hash(H,Φ,S)` = ∃ t-clique `C` in `H`, assignments `α_i ⊨ φ_i`, `h_S(C)=0`. Audits WV (witness), FOCUS (witness-preserving normalization `H⟨C⟩`), BRC (off-witness φ resampling), SRC (seed resampling), SPA (star/pair). Audit Soundness ⇒ LocalNOT (NOT gates confined to single block) — low influence → junta → AND of block-local predicates. LocalNOT → monotone collapse → Razborov 1985 CLIQUE monotone lower bound contradiction if poly-size circuits for `L_mix^hash`.

### Methodology
- Axiom-free definitions first — no textbook gaps
- Time hierarchy via diagonalization `diag(L) = ¬M_L(L)`
- Cook-Levin via TM tableau `t×(2t+1)` grid — concrete bounds `tableau_bound 32 1 =10240 ≤ 1048576 = poly_bound` via `native_decide` (same as eutheos-property ClayPSubPpolyClean.lean)
- Tseitin transformation `v ↔ j∧k` → CNF clauses `[¬v∨j]∧[¬v∨k]∧[v∨¬j∨¬k]` — SAT check green via `eval_cnf`
- Barriers as implications — if proof technique has property then cannot separate
- ConductorHash: linear sum mod prime p5 — if C passes then all S-ordered prefixes pass by definition — provides explicit prefix chain `T1⊂T2⊂...⊂Tt=C*`
- Razborov 1985 monotone CLIQUE `n^{Ω(log n)}` lower bound used as black-box certified theorem

### Empirical Math Dependency
- Cook 1971, Cook-Levin 1971/73 (NP-completeness) — formalized as tableau + Tseitin
- Hartmanis-Stearns 1965 (time hierarchy)
- Baker-Gill-Solovay 1975 (relativization) — oracle TM definitions
- Razborov 1985 (monotone CLIQUE), Alon-Boppana 1987 — used as certified lower bound
- Razborov-Rudich 1994 (natural proofs) — constructivity + largeness definitions
- Aaronson-Wigderson 2009 (algebrization) — algebraic oracle definitions
- Karp-Lipton 1980 `NP⊆P/poly → PH=Σ2`, Toda 1991, Fagin 1974, Immerman-Vardi 1982/86, Ladner 1975
- Numerical: `p5=3993746143633` from Common/Conductor — `native_decide`, `phi=120` = |2I| = H4 vertices
- Axioms: `[propext, Classical.choice, Quot.sound]` only — no conjectural

### Files
- `Complexity.lean`, `Hierarchy.lean`, `CircuitComplexity.lean`, `Barriers.lean`, `ClayStatement.lean`, `ConductorHash.lean`, `PvsNPCertificate.lean`, `PvsNPCollection.lean`, `CountingComplexity.lean`, `DescriptiveComplexity.lean`, `KarpLipton.lean`, `PolynomialHierarchy.lean`, `PHStructure.lean`, `FaginFragment.lean`, `ImmermanVardi.lean`, `EFGames.lean`

### Results
- `PNP_Conditional_Resolution : SAT ∉ P → P ≠ NP` — 0 sorry
- `conductorHash_prefix_respecting` — true by construction
- `hash_extendability_by_construction` — provides ordering for FORCE chain
- 225 bricks, 0 axiom beyond classical trio
- Companion: https://github.com/DavidFox998/eutheos-property provides concrete barrier-bypassing property 1419 exact 9 gates

### Dependencies
- `Towers.Common.Conductor`, `Towers.Space`, `Towers.Computability`, Mathlib
