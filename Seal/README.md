# Seal — Certificate Sealing + MANIFEST LOCKED

### Overview
Seals all 11 towers + enforces 0 sorry via MANIFEST LOCKED CI. This folder is the lock that makes `v1.1-if-sat-notin-p-conductor-hash` immutable and verifiable — `AXIOMS.txt`, `MANIFEST`, `SEAL` hashes.

### For Layperson
Think of seal as wax seal on a letter — proves no one tampered. This folder contains list of all Lean files, their hashes, what axioms they use, and CI that checks no `sorry` slipped in. If you change a file, hash changes, seal breaks — CI red X. If you add `sorry`, forbidden checker fails — CI red X. Green check means 225 bricks, 0 sorry, classical trio only — same as when Zenodo DOI was minted.

### For Referee
Defines sealing protocol: `MANIFEST` = `List (FilePath × SHA256 × AxiomList)`, `AXIOMS.txt` = `print axioms` for each theorem, `SEAL` = SHA256 of MANIFEST. CI workflow `.github/workflows/seal.yml` from `Task339: Add MANIFEST LOCKED CI` does: `lake build` → `lake env lean --run scripts/gen_manifest.py` → `sha256sum MANIFEST > SEAL` → compare to committed `SEAL` — if mismatch, fail. Also `forbidden_check.lean` = `grep -r "sorry\|admit\|axiom" Towers --include="*.lean" | wc -l =0`, `axiom_check.lean` = for each theorem in `PvsNPCollection`, `print axioms = [propext, Classical.choice, Quot.sound]`. Provides `SealCertificate` structure `where manifest: List Entry, seal: Hash, verified: Bool, proof: verified = true → ∀ e∈manifest, e.axioms = trio ∧ ¬e.containsSorry`.

### Methodology
- `gen_manifest.py`: walks `Towers/**/*.lean`, computes `SHA256(file)`, runs `lake env lean --run scripts/print_axioms.lean file` to get `print axioms` output, writes `MANIFEST.json` as `[{path, sha256, axioms, has_sorry: bool}]`
- `SEAL`: `echo -n $(cat MANIFEST.json) | sha256sum` — single hash of all hashes — committed
- `AXIOMS.txt`: `cat MANIFEST.json | jq .axioms | sort | uniq -c` — should be only trio
- CI: `on: push, pull_request`, `jobs: seal: runs-on: ubuntu-latest, steps: checkout, lean-action, lake build, python3 scripts/gen_manifest.py, diff MANIFEST.json committed MANIFEST.json, diff SEAL committed SEAL, python3 scripts/forbidden_check.py, python3 scripts/axiom_check.py` — fails if any diff or forbidden found
- Honesty via ZProtocol: `OPEN` = file with sorry not in MANIFEST, `CERT` = file in MANIFEST with trio and no sorry, `CLAIM` = file claims P≠NP but has sorry — CI catches CLAIM as forbidden

### Empirical Math Dependency
- SHA256 — cryptographic hash — collision resistance assumption — not mathematical axiom, computational assumption for seal integrity — standard
- Lean meta `print axioms` — Lean core `Lean.Elab.Command` — classical trio is Lean's logic core
- No external math — sealing is syntactic + hash — Lean core only
- Axioms: Lean core only — `propext, Classical.choice, Quot.sound`

### Files
- `MANIFEST.json` or `MANIFEST` — list of all Lean files + SHA256 + axioms + has_sorry flag — generated
- `SEAL` or `SEAL.txt` — SHA256 of MANIFEST — single hash — committed — if file changes, SEAL changes
- `AXIOMS.txt` — `print axioms` for all theorems — should be only trio — from `Phase 22: update AXIOMS.txt with Cert...` commit in your screenshot
- `scripts/gen_manifest.py`, `scripts/forbidden_check.py`, `scripts/axiom_check.py` — CI scripts — in `.github/workflows/`
- `.github/workflows/ci.yml` — `Task339: Add MANIFEST LOCKED CI` — 3 weeks ago in your screenshot

### Results
- MANIFEST LOCKED — 225 bricks hashed — SEAL committed — CI green check in your screenshot `Create ConductorHash.lean ✓`
- `0 sorry, 0 admit, 0 axiom` — `forbidden? = false` for all files — checked by CI
- `AXIOMS.txt` = trio only — `print axioms PNP_Conditional_Resolution → [propext, Classical.choice, Quot.sound]`
- Provides immutability: if you change `Towers/Common/Conductor.lean` or `Towers/PvsNP/ConductorHash.lean`, `lake build` still green but `SEAL` mismatch → CI red → must recommit new SEAL — audit trail in git history
- Used by Zenodo DOI — DOI mints MANIFEST + SEAL — ensures version `v1.1-if-sat-notin-p-conductor-hash` is immutable

### Dependencies
- Lean core `SHA256` via `IO`, `String`, `List`
- `Towers.ZProtocol.ZProtocolFramework` — `forbidden?`, `axiomFree?`
- `.github/workflows/` — GitHub Actions — `leanprover/lean-action`
- No Mathlib — sealing is meta — Lean core only
