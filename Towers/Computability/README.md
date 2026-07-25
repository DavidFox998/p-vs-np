# Computability — Recursion Theory

**Purpose:** Formalize Turing machines, undecidability, arithmetical hierarchy — foundation for Complexity Phase 1.

**Files:**
- `Computability.lean` — TM definition, halting, reducibility
- `ArithmeticalHierarchy.lean` — Σ_n, Π_n, Δ_n, Post hierarchy
- `ComputabilityCollection.lean`

**Methodology:** TM as `structure Q Sigma q0`, tableau `t×(2t+1)` concrete bounds (same as P⊆P/poly proof in eutheos-property ClayPSubPpolyClean.lean — 10240≤1048576 native_decide), halting undecidable via diagonalization, hierarchy via oracle quantification.

**Results:** Halting ∉ decidable, Σ1-complete, arithmetical hierarchy strict. Provides TM model used by Space and PvsNP.

**Dependencies:** Mathlib Computability.
