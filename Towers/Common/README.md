# Common — Conductor Library

**Purpose:** Single source of truth for arithmetic constants that all towers reuse — kills N loop.

**Files:**
- `Conductor.lean` — `N_143=143`, `phi_143=120` (totient = |2I| = H4 vertices), `g_X0_143=13`, `h_neg143=10` (class number Q(√-143) = 1/10 factor), `p5_BDP=3993746143633` (BDP prime). Theorem `Nat.totient 143 = 120` by `native_decide`. Table `ConductorRow`.

**Methodology:** Table lookup via `native_decide`, not reconstruction. 200 abelian varieties = 200 rows of (N, phi, g, h, p5). List-based `conductor_table` with `find?`.

**Results:** `N=143` workhorse defined once. All towers import `Towers.Common.Conductor` instead of rebuilding X0(143). `p5` used by `PvsNP.ConductorHash` for prefix-respecting hash.

**Dependencies:** Mathlib only — `Nat.totient`, `List.find?`.
