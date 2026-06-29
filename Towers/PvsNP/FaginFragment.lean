/-
================================================================
Towers/PvsNP/FaginFragment.lean — Fagin's Theorem Genuine Fragment

Morning Star Project · Theorema Aureum 143

Three-colorability has an explicit ∃SO definition.
This file formalizes the concrete Fagin witness for 3-colorability:

  Φ₃COLOR := ∃C: V→Fin 3. ∀v∀w. Edge(v,w) → C(v)≠C(w)

This is genuinely an existential second-order sentence:
  — "∃C: unary function V→Fin 3" is a SECOND-ORDER quantifier
  — "∀v∀w. Edge(v,w) → C(v)≠C(w)" is FIRST-ORDER

We do not need full finite model theory (Fagin 1974) to formalize this
instance. The explicit witness structure is provably correct.

BRICKS (5 genuine):
  threeColorable_of_le          — monotone in subgraph order
  fagin_exso_quantifier_structure — the ∃SO quantifier structure is exact
  fagin_witness_iff_colorable   — FaginThreeColorWitness ↔ ThreeColorable
  threeColorable_complete4_false — K₄ not 3-colorable (pigeonhole)
  threeColorable_of_two_colorable — 2-colorable → 3-colorable

CERT: Cert_ThreeColor_NPcomplete (Karp 1972 — needs TM reduction model)
      Cert_ThreeColor_Fagin (Fagin scaffold wiring — needs Satisfies semantics)
OPEN: ThreeColor_vs_TwoColor_OPEN

Clay status: P ≠ NP LOCKED OPEN. No Clay claim.
================================================================
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Towers.PvsNP.Complexity

open TheoremaAureum.Towers.PvsNP.Complexity

namespace TheoremaAureum.Towers.PvsNP.Fagin

-- ================================================================
-- §1  Three-colorability — the explicit ∃SO sentence
-- ================================================================

/-- A graph G is 3-colorable if there exists c: V→{0,1,2} such that
    adjacent vertices receive distinct colors.

    This is LITERALLY the ∃SO sentence Φ₃COLOR:
      ∃C: V→Fin 3. ∀v. ∀w. Edge(v,w) → C(v) ≠ C(w)
    The quantifier "∃C: V→Fin 3" is **second-order** (quantification
    over a function); the body is first-order. -/
def ThreeColorable {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ c : V → Fin 3, ∀ ⦃v w : V⦄, G.Adj v w → c v ≠ c w

/-- A graph G is 2-colorable (admits a proper 2-coloring; equivalent to
    being bipartite for connected graphs). -/
def TwoColorable {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ c : V → Fin 2, ∀ ⦃v w : V⦄, G.Adj v w → c v ≠ c w

-- ================================================================
-- §2  The Fagin ∃SO witness struct
-- ================================================================

/-- The explicit Fagin ∃SO witness for 3-colorability: packages the
    coloring function and its validity proof. This is the *certificate*
    structure — in NP, the witness is polynomial-size (|V| · log 3 bits)
    and polynomial-time checkable (scan each edge, compare colors). -/
structure FaginThreeColorWitness {V : Type*} (G : SimpleGraph V) where
  coloring  : V → Fin 3
  valid     : ∀ ⦃v w : V⦄, G.Adj v w → coloring v ≠ coloring w

-- ================================================================
-- §3  Genuine theorems
-- ================================================================

/-- **GENUINE**: Three-colorability is monotone — a subgraph of a
    3-colorable graph is 3-colorable (same coloring remains valid
    since we have fewer edge constraints). -/
theorem threeColorable_of_le {V : Type*} {G₁ G₂ : SimpleGraph V}
    (h : G₁ ≤ G₂) (hG₂ : ThreeColorable G₂) : ThreeColorable G₁ :=
  let ⟨c, hc⟩ := hG₂
  ⟨c, fun _ _ hadj => hc (h hadj)⟩

/-- **GENUINE**: The ∃SO quantifier structure is exact.
    ThreeColorable G is definitionally equal to the ∃SO formula shape:
      ∃(second-order c : V→Fin 3). ∀(first-order v w). Adj v w → c v ≠ c w.
    No model theory is needed — the Lean definition IS the formula. -/
theorem fagin_exso_quantifier_structure {V : Type*} (G : SimpleGraph V) :
    ThreeColorable G ↔
    ∃ (c : V → Fin 3), ∀ (v w : V), G.Adj v w → c v ≠ c w :=
  ⟨fun ⟨c, hc⟩ => ⟨c, fun v w h => hc h⟩,
   fun ⟨c, hc⟩ => ⟨c, fun h => hc _ _ h⟩⟩

/-- **GENUINE**: A FaginThreeColorWitness exists iff the graph is 3-colorable.
    The struct packages the ∃SO witness explicitly. -/
theorem fagin_witness_iff_colorable {V : Type*} (G : SimpleGraph V) :
    Nonempty (FaginThreeColorWitness G) ↔ ThreeColorable G :=
  ⟨fun ⟨⟨c, hc⟩⟩ => ⟨c, hc⟩, fun ⟨c, hc⟩ => ⟨⟨c, hc⟩⟩⟩

/-- **GENUINE ⭐**: The complete graph K₄ (all 4 vertices mutually adjacent)
    is NOT 3-colorable.

    Proof: any such coloring c: Fin 4 → Fin 3 must be injective
    (since every pair of distinct vertices is adjacent, c v = c w → v = w).
    But injective Fin 4 → Fin 3 contradicts |Fin 4| = 4 > 3 = |Fin 3|
    via Fintype.card_le_of_injective. -/
theorem threeColorable_complete4_false :
    ¬ThreeColorable (⊤ : SimpleGraph (Fin 4)) := by
  rintro ⟨c, hc⟩
  have hinj : Function.Injective c := by
    intro v w hvw
    by_contra hne
    exact hc (SimpleGraph.top_adj.mpr hne) hvw
  have hcard := Fintype.card_le_of_injective c hinj
  simp [Fintype.card_fin] at hcard

/-- **GENUINE**: A 2-colorable graph is 3-colorable.
    Proof: embed Fin 2 ↪ Fin 3 via the natural inclusion (preserve val),
    then the adjacency constraint is preserved since the embedding is injective. -/
theorem threeColorable_of_two_colorable {V : Type*} {G : SimpleGraph V}
    (h : TwoColorable G) : ThreeColorable G := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun v => ⟨(c v).val, Nat.lt_trans (c v).isLt (by norm_num)⟩,
          fun v w hadj heq => ?_⟩
  apply hc hadj
  have hval : (c v).val = (c w).val := congr_arg Fin.val heq
  exact Fin.ext hval

-- ================================================================
-- §4  Named open surfaces
-- ================================================================

/-- **OPEN (FALSE in general)**: Not every 3-colorable graph is 2-colorable.
    Odd cycles (C₃, C₅, ...) are 3-colorable but NOT 2-colorable.
    We name this surface to make the gap explicit. -/
def ThreeColor_vs_TwoColor_OPEN : Prop :=
  ∀ {V : Type*} (G : SimpleGraph V), ThreeColorable G → TwoColorable G

-- ================================================================
-- §5  Cert axioms (proved in literature; Mathlib v4.12.0 gap)
-- ================================================================

/-- **CERT**: 3-COLOR is NP-complete (Karp 1972).
    NP-membership is witnessed by FaginThreeColorWitness (genuine above).
    NP-hardness requires a polynomial-time reduction from 3-SAT to 3-COLOR
    using a formal Turing machine model absent from Mathlib v4.12.0. -/
axiom Cert_ThreeColor_NPcomplete : True

/-- **CERT**: The concrete Fagin ∃SO scaffold connection.
    Φ₃COLOR above is an ∃SO sentence in the DescriptiveComplexity.lean scaffold;
    wiring it through the opaque Satisfies API to the concrete coloring semantics
    requires extending the model-theory scaffold beyond its current depth. -/
axiom Cert_ThreeColor_Fagin : True

end TheoremaAureum.Towers.PvsNP.Fagin
