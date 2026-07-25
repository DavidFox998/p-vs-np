# Continuum — Cardinal Arithmetic

**Purpose:** Formalize cardinal bounds, König's theorem, CH independence scaffolding.

**Files:**
- `CardinalBounds.lean`
- `ContinuumHypothesis.lean`
- `KonigTheorem.lean`
- `KonigInequality.lean`
- `ContinuumCollection.lean`

**Methodology:** Cardinal as `Cardinal.mk`, Beth numbers, König's inequality `cf(κ^cf κ) > κ`, cardinal exponentiation bounds, CH as `2^ℵ0 = ℵ1`.

**Results:** Cardinal inequalities, König's theorem machine-checked, CH statement formalized. Used by ZFC tower for independence.

**Dependencies:** Mathlib SetTheory Cardinal.
