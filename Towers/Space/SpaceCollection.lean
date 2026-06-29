/-
================================================================
Towers/Space/SpaceCollection.lean — Space Complexity Sub-Tower

Morning Star Project · Theorema Aureum 143

Space complexity sub-tower — collection and summary.
Files:
  SpaceComplexity.lean — class definitions + closure properties (5 genuine)
  Savitch.lean         — path squaring + REACH recursion (7 genuine)

Genuine core: reaches_in_trans + savitch_squaring — the abstract
Savitch squaring: m+n step reachability ↔ ∃ midpoint with m-path ∧ n-path.
This is the mathematical heart of why NPSPACE ⊆ PSPACE.

Cert axioms: Cert_Savitch_NPSPACE_eq_PSPACE, Cert_P_subset_PSPACE,
             Cert_NP_subset_PSPACE, Cert_Immerman_Szelepcsényi,
             Cert_Savitch_theorem.

Status: Abstract path squaring PROVED. Formal NPSPACE=PSPACE CERT.
No Clay claim. L≠PSPACE OPEN. NL=L OPEN.
================================================================
-/

import Towers.Space.SpaceComplexity
import Towers.Space.Savitch

namespace TheoremaAureum.Towers.Space

/-- Space complexity sub-tower summary. -/
def SpaceTowerSummary : String :=
  "Space Tower: 12 bricks (11 genuine + 5 cert). " ++
  "Core: reaches_in_trans + savitch_squaring (Savitch path-squaring). " ++
  "PSPACE closed under comp/inter/union. L⊆NL. " ++
  "Open: L≠PSPACE, NL=L. Status: OPEN."

end TheoremaAureum.Towers.Space
