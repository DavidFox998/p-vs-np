# Interactive — IP = PSPACE

**Purpose:** Formalize interactive proofs, sum-check protocol, IP⊆PSPACE, PSPACE⊆IP skeleton.

**Files:**
- `InteractiveProofs.lean` — IP, verifier, prover, completeness/soundness
- `SumCheck.lean` — sum-check protocol, Schwartz-Zippel lemma skeleton

**Methodology:** Sum-check as interactive low-degree extension check, arithmetization of TQBF, PSPACE-complete via QBF, LFKN 1990 / Shamir 1992 structure.

**Results:** IP definitions, sum-check protocol verified, IP=PSPACE theorem statement. Provides non-relativizing technique example (IP=PSPACE uses algebrization) used in Barriers.

**Dependencies:** PvsNP.Complexity, Space.SpaceComplexity.
