# Space — Space Complexity

**Purpose:** Formalize space classes, Savitch, Immerman-Szelepcsényi, Ladner.

**Files:**
- `SpaceComplexity.lean` — L, NL, PSPACE
- `Savitch.lean` — NSPACE(s)⊆DSPACE(s²)
- `SpaceCollection.lean`
- `LadnerTheorem.lean` — If P≠NP then NP-intermediate exists

**Methodology:** Savitch via middle-first search `CAN_YIELD`, Immerman-Szelepcsényi via inductive counting, Ladner via delayed diagonalization + padding.

**Results:** Savitch theorem PSPACE=NPSPACE, NL⊆P, Ladner theorem. Provides space hierarchy used by Hierarchy.lean and IP=PSPACE.

**Dependencies:** Computability.Computability, Mathlib.
