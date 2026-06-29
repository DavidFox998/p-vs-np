/-
================================================================
Towers/Approximation/ApproximationCollection.lean

Morning Star Project · Theorema Aureum 143

Approximation Complexity Sub-Tower — collection and summary.

Files:
  ApproximationComplexity.lean — structural framework (7 genuine + 4 cert)

Key genuine theorems:
  approx_ratio_one (trivial: exact → ratio 1)
  approx_ratio_trans (ratios multiply)
  approx_ptas_is_apx (PTAS ⊆ APX at ε=1)
  approx_reduction_chain (reductions compose)
  approx_vertex_cover_two_ratio ⭐ (maximal matching → 2-approximation)
  approx_gap_witnesses (gap characterization of inapproximability)
  approx_comp_yields_ratio (complement bound)

Key cert axioms:
  Cert_PCP_Theorem (Arora-Safra 1992 + ALMSS 1998)
  Cert_MaxSAT_Hastad (7/8+ε inapprox, Håstad 2001)
  Cert_MaxClique_inapprox (polynomial inapprox, Zuckerman 2007)
  Cert_UGC_Implications (conditional on Unique Games Conjecture)

Open surfaces: APX_vs_PTAS_OPEN, UGC_OPEN.

Status: Structural framework PROVED. PCP/inapproximability CERT.
No Clay claim.
================================================================
-/

import Towers.Approximation.ApproximationComplexity

namespace TheoremaAureum.Towers.Approximation

/-- Approximation sub-tower summary. -/
def ApproximationTowerSummary : String :=
  "Approximation Tower: 11 bricks (7 genuine + 4 cert). " ++
  "Core: vertex-cover 2-approx, ratio composition, PTAS⊆APX. " ++
  "Cert: PCP theorem (Arora et al. 1998), Hastad 7/8 bound. " ++
  "Open: UGC conjecture. Status: OPEN."

end TheoremaAureum.Towers.Approximation
