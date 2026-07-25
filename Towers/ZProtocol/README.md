# ZProtocol — Honesty Framework

**Purpose:** Formalize OPEN/CERT/CLAIM distinction — the Z-Protocol that prevents false P vs NP claims.

**Files:**
- `ZProtocolFramework.lean`
- `ZProtocolCollection.lean`

**Methodology:** Define `Status := OPEN | CERT | CLAIM`, `AxiomFree` checker via `#print axioms`, `SorryFree` checker via forbidden keywords, MANIFEST LOCKED CI workflow enforces 0 sorry/admit.

**Results:** `Z-Protocol` theorem — if `print axioms` = [propext, Classical.choice, Quot.sound] and `forbidden? False` then certificate depends only on Lean core. Used by all towers to enforce 0 sorry. This repo passes.

**Dependencies:** Lean core only.
