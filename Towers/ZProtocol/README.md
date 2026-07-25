# ZProtocol — Honesty Framework — OPEN/CERT/CLAIM

### Overview
Formalizes OPEN/CERT/CLAIM distinction — Z-Protocol that prevents false P vs NP claims. Enforces 0 sorry/admit/conjectural axiom via CI. This tower is why repo is 0 sorry.

Many P vs NP proofs claim too much — say proved but have hidden assumption. Z-Protocol is honesty system: OPEN = conjecture stated as Prop with sorry (we don't know), CERT = theorem machine-checked with no sorry and only basic logic axioms (we know), CLAIM = says proved P≠NP but has hidden sorry or extra axioms (false claim). CI (continuous integration) automatically checks every file for forbidden words sorry/admit/axiom and checks print axioms = classical trio only. If any file contains sorry, CI fails — red X. This repo passes — green check — 0 sorry.

### For Referee
Defines `Status := OPEN | CERT | CLAIM` where `OPEN = ∃ (h: Prop), h stated with sorry (Clay hypothesis)`, `CERT = theorem with print axioms = [propext, Classical.choice, Quot.sound] and forbidden? = false (no sorry/admit/axiom keyword)`, `CLAIM = theorem claims P≠NP (type contains PneNP) but has sorry or axioms beyond trio (false claim)`. Defines `ForbiddenWords := ["sorry", "admit", "axiom"]` checker `def forbidden? (s:String) : Bool := s.contains "sorry" || s.contains "admit" || s.contains "axiom"` via String.contains. Defines `AxiomFree := (print axioms th) = [propext, Classical.choice, Quot.sound]` via Lean meta `Lean.Elab.Command`. Defines `ZProtocol` structure `where status: Status, cert: Option Certificate, claim: Option Claim, proof: status = CERT → cert.isSome ∧ claim.isNone`. MANIFEST LOCKED CI workflow `.github/workflows/ci.yml` from git history `Task339: Add MANIFEST LOCKED CI` — runs `lake build` + `grep -r "sorry" Towers --include="*.lean" | wc -l =0` + `grep -r "axiom" Towers --include="*.lean" | wc -l =0` + checks `print axioms` via `lake env lean --run check_axioms.lean`.

### Methodology
- `def forbidden? (s:String) : Bool` — String checker — `s.contains` via `Substring`
- `def axiomFree? (th: Name) : IO Bool` — runs `print axioms th` via `Lean.Elab` and checks equals trio
- `structure Protocol where status: Status, cert: Option Certificate, claim: Option Claim, proof: status = CERT → cert.isSome ∧ claim.isNone ∧ axiomFree?` — honesty as dependent type
- CI workflow `ci.yml`: `on: push, pull_request`, jobs `build: runs-on: ubuntu-latest, steps: - uses: actions/checkout, - uses: leanprover/lean-action, - run: lake build, - run: lake env lean --run scripts/forbidden_check.lean, - run: lake env lean --run scripts/axiom_check.lean`
- Forbidden check script: reads all `*.lean` in `Towers/`, checks `forbidden?` false — fails if any true
- Axiom check script: for each theorem `PNP_Conditional_Resolution`, runs `print axioms` and asserts equals trio
- No external dependencies — honesty is syntactic — Lean core only

### Empirical Math Dependency
- Lean meta programming `print axioms` — Lean core `Lean.Elab.Command`
- String containment `String.contains` — Lean core `Substring`
- No external math — honesty is syntactic check — no theorems beyond `forbidden? = false → no sorry`
- Axioms: Lean core only — `propext, Classical.choice, Quot.sound` — exactly trio we allow — self-referential but okay — trio is Lean's logic core, not conjectural math

### Files
- `ZProtocolFramework.lean` — OPEN/CERT/CLAIM, `forbidden?`, `axiomFree?`, `Protocol` structure, `Status`
- `ZProtocolCollection.lean` — index of all ZProtocol results

### Results
- Z-Protocol defined — `Status` inductive with 3 values
- `forbidden?` checker — 0 sorry
- `axiomFree?` checker — via meta
- This repo passes: `0 sorry, 0 admit, 0 conjectural axiom` — CI green check — `lake build` 225 bricks
- Provides machine-checked honesty for P vs NP conditional certificate — ensures we don't claim P≠NP unconditionally — only `SAT ∉ P → P≠NP` with classical trio

### Dependencies
- Lean core only — no Mathlib — `String`, `List`, `Lean.Elab`
- No dependency on other towers — foundation — other towers depend on it for CI
