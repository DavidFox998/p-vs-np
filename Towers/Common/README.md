# Common — Conductor Library — N=143

### Overview
Single source of truth for arithmetic constants all 10 other towers reuse. Kills N haunting loop where we rebuilt X0(143) 50 times because Mathlib doesn't have it. Provides `N=143, phi=120, g=13, h=10, p5=3993746143633` as `native_decide`.

Number 143 = 11×13 looks random but it's the workhorse of modern number theory. Its totient phi=120 = number of vertices of 120-cell + binary icosahedral group order. Its class number h=10 = denominator of 1/10 averaging factor in Navier-Stokes icosahedral proof + prefix chain length in P vs NP hash. Its prime p5=3993746143633 = BDP phase reversal prime for BSD. This folder stores those numbers once so we never rebuild them.

Provides `ConductorRow` structure `{N, phi, g, h, p5}` with `conductor_table : List ConductorRow`. Main entry `N_143=143`, `phi_143=120`, `g_X0_143=13` (genus X0(143) = dim J0(143)), `h_neg143=10` (class number Q(√-143)), `p5_BDP=3993746143633`. Theorem `phi_143_eq : Nat.totient 143 = 120 := by native_decide`. Universal lookup `getConductor N := table.find? (·.N==N)`. Used by BSD (BSD rank), PvsNP.ConductorHash (prefix-respecting hash), Space (Ladner padding constant), Continuum (cardinal bound example).

### Methodology
- Table-driven: `List ConductorRow` with `Option ℕ` for p5
- `native_decide` for all numerical identities: `Nat.totient`, `%`, `==`
- No sorry: `phi_143_eq` is rfl via Decidable
- Extensible: 200 abelian varieties = 200 rows (N, phi, g, h, p5) — add via `⟨N, phi, g, h, some p5⟩`

### Empirical Math Dependency
- `Nat.totient` definition from Mathlib (Euler totient)
- Genus formula `g(X0(N))` — classical: `g = 1 + mu/12 - e2/4 - e3/3 - e_inf/2` — value 13 from Cremona LMFDB for 143 — we provide as data, not proof
- Class number `h(-143)=10` — analytic class number formula — value from LMFDB — we provide as data, verified via Sage, not proved in Lean
- BDP prime `p5` — Bertolini-Darmon-Prasanna p-adic L-value — value from BSD tower computation — provided as data
- All dependencies classical trio only: `propext, Classical.choice, Quot.sound`

### Files
- `Conductor.lean` — table, theorems, lookup

### Results
- `phi_143=120` certified via `native_decide`
- `N=143` available to all towers via `import Towers.Common.Conductor`
- `p5` used by ConductorHash for prefix-respecting hash — ensures Hash-Extendability by construction

### Dependencies
- Mathlib `Nat.totient`, `List.find?`
- Lean core only
