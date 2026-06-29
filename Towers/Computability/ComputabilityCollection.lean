/-
================================================================
Towers/Computability/ComputabilityCollection.lean

Morning Star Project · Theorema Aureum 143

Computability Theory Sub-Tower — collection and summary.

This sub-tower formalizes the foundational results of computability
theory using the Cantor-Russell diagonal argument as the core genuine
content.

Sub-tower structure:
  Computability.lean         — diagonal argument, decidable closure (7 genuine)
  ArithmeticalHierarchy.lean — AH classes, structural results (5 genuine)

Key genuine theorem: diagonal_not_in_range (Cantor-Russell 1891/1901/1936):
  For ANY function recognize : BStr → Language,
  the diagonal language {w | w ∉ recognize w} is NOT in the range.
  This is the pure logical core of Turing undecidability, Cantor's
  uncountability proof, and Russell's set-theoretic paradox.

Key cert axioms:
  Cert_Halt_RE            — HaltingSet ∈ RE (Turing 1936)
  Cert_Halt_Not_coRE      — HaltingSetᶜ ∉ RE (Turing 1936)
  Cert_Rice_Theorem       — Rice's theorem (Rice 1953)
  Cert_AH_PostTheorem     — Δ₁ = Decidable (Post 1944)
  Cert_AH_Strict          — AH hierarchy is strict

Total bricks: 12 (7 genuine + 5 cert axioms + 4 named opens)

Status: Diagonal argument PROVED. Halting problem OPEN.
No Clay claim. P vs NP remains OPEN.
================================================================
-/

import Towers.Computability.Computability
import Towers.Computability.ArithmeticalHierarchy

namespace TheoremaAureum.Towers.Computability

/-- Collection summary: all computability results. -/
def ComputabilityTowerSummary : String :=
  "Computability Tower: 12 bricks (7 genuine + 5 cert). " ++
  "Core: diagonal_not_in_range (Cantor-Russell). " ++
  "AH: Sigma0 closed under Bool ops. " ++
  "Open: TM formalization (~12-24 mo). Status: OPEN."

end TheoremaAureum.Towers.Computability
