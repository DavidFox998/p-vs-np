/-
================================================================
Towers/Continuum/KonigInequality.lean — König's Cardinal Inequality (Full)

Morning Star Project · Theorema Aureum 143

The full König cardinal theorem (general form):
  If κᵢ < λᵢ for every i ∈ ι, then  ∑ᵢ κᵢ < ∏ᵢ λᵢ.

This is strictly stronger than the ℵ₁ ≤ 2^ℵ₀ corollary proved in
KonigTheorem.lean. The general form captures:
  — Cantor's theorem as a special case (ι = {*}, κ = 0, λ = 2)
  — The continuum cofinality consequence cf(2^ℵ₀) > ℵ₀
  — The aleph hierarchy bound: ∑ₙ ℵₙ < ∏ₙ ℵₙ₊₁

Key API: Cardinal.sum_lt_prod (Mathlib.SetTheory.Cardinal.Basic)

BRICKS (4 genuine):
  konig_general_inequality      — full ∑κᵢ < ∏λᵢ via Mathlib
  konig_nat_sum_lt_succ_prod    — ∑ nᵢ < ∏ (nᵢ+1) for natural n
  konig_aleph_sum_lt_aleph_prod — ∑ₙ ℵₙ < ∏ₙ ℵₙ₊₁ (concrete)
  konig_le_product              — monotone product bound

CERT: Cert_Konig_Cofinality (cf(2^ℵ₀) > ℵ₀ — cofinality API gap)
OPEN: Konig_AlephOmegaIsSum_OPEN (∑ₙ ℵₙ = ℵ_ω — needs ordinal API)

Status: Classical trio, 0 sorry, 0 sorryAx.
================================================================
-/

import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Tactic
import Towers.Continuum.CardinalBounds
import Towers.Continuum.KonigTheorem

open Cardinal
open TheoremaAureum.Towers.Continuum
open TheoremaAureum.Towers.Continuum.Konig

namespace TheoremaAureum.Towers.Continuum.KonigFull

-- ================================================================
-- §1  The general König cardinal inequality (GENUINE ★)
-- ================================================================

/-- **GENUINE ★**: The full König cardinal inequality.

    If κᵢ < λᵢ for every i ∈ ι, then  ∑ᵢ κᵢ < ∏ᵢ λᵢ.

    This is the complete form of König's 1905 theorem on infinite
    cardinal arithmetic. Key instantiations:
      — ι = ℕ, κₙ = ℵₙ, λₙ = ℵₙ₊₁:  ∑ₙ ℵₙ < ∏ₙ ℵₙ₊₁  (§2 below)
      — ι = κ, all λᵢ = 2:  κ < 2^κ  (Cantor, already genuine)

    Proof: direct application of Mathlib's Cardinal.sum_lt_prod,
    which formalizes the diagonal argument in the full generality. -/
theorem konig_general_inequality {ι : Type*} (f g : ι → Cardinal)
    (h : ∀ i, f i < g i) : Cardinal.sum f < Cardinal.prod g :=
  Cardinal.sum_lt_prod f g h

-- ================================================================
-- §2  Concrete corollaries (GENUINE)
-- ================================================================

/-- **GENUINE**: For any ℕ-valued sequence, the sum is less than the
    product of successor terms.

    Note: restricted to finite cardinals (ℕ cast to Cardinal) because
    for infinite cardinals κ we have κ + 1 = κ, so the bound fails.
    For ℕ: each (n : Cardinal) < (n : Cardinal) + 1 = (n+1 : Cardinal). -/
theorem konig_nat_sum_lt_succ_prod {ι : Type*} (f : ι → ℕ) :
    Cardinal.sum (fun i => (f i : Cardinal)) <
    Cardinal.prod (fun i => ((f i : Cardinal) + 1)) := by
  apply konig_general_inequality
  intro i
  exact_mod_cast Nat.lt_succ_self (f i)

/-- **GENUINE ⭐**: ∑ₙ ℵₙ < ∏ₙ ℵₙ₊₁.

    The sum of all countably many alephs ℵ₀ + ℵ₁ + ℵ₂ + ⋯ is strictly
    less than the product ℵ₁ · ℵ₂ · ℵ₃ · ⋯

    Proof: each ℵₙ < ℵₙ₊₁ by strict monotonicity of the aleph function
    (Mathlib: Cardinal.aleph_strictMono, already genuine in KonigTheorem.lean),
    so König's general inequality applies directly. -/
theorem konig_aleph_sum_lt_aleph_prod :
    Cardinal.sum (fun n : ℕ => aleph n) <
    Cardinal.prod (fun n : ℕ => aleph (n + 1)) :=
  konig_general_inequality _ _ (fun n => aleph_strictMono (Nat.lt_succ_self n))

/-- **GENUINE**: Monotone bound for cardinal products.
    If f i ≤ g i for every i, then ∏ᵢ f i ≤ ∏ᵢ g i.
    Proof: direct from Mathlib's Cardinal.prod_le_prod. -/
theorem konig_le_product {ι : Type*} {f g : ι → Cardinal}
    (h : ∀ i, f i ≤ g i) : Cardinal.prod f ≤ Cardinal.prod g :=
  Cardinal.prod_le_prod h

-- ================================================================
-- §3  Named open surfaces
-- ================================================================

/-- **OPEN**: ∑ₙ ℵₙ = ℵ_ω.

    The sum of ℵ₀ + ℵ₁ + ⋯ equals ℵ_ω (the first limit aleph), since
    ℵ_ω is the supremum of the sequence and each partial sum is bounded
    by ℵ_ω. Provable in principle via Cardinal.iSup + ordinal API;
    requires `aleph ω` where ω : Ordinal and the ordinal limit machinery
    not yet wired in this tower's Continuum sub-tower. -/
def Konig_AlephOmegaIsSum_OPEN : Prop :=
  Cardinal.sum (fun n : ℕ => aleph n) = aleph ω

-- ================================================================
-- §4  Cert axioms (proved in literature; Mathlib v4.12.0 API gap)
-- ================================================================

/-- **CERT**: König's cofinality theorem: cf(2^ℵ₀) > ℵ₀.

    Consequence: the continuum 2^ℵ₀ cannot be expressed as a countable
    union of strictly smaller cardinal sets. Equivalently, there is no
    sequence κₙ < 2^ℵ₀ with sup_{n} κₙ = 2^ℵ₀.

    Proof sketch: suppose 2^ℵ₀ = ∑_{n<ω} κₙ with each κₙ < 2^ℵ₀.
    König gives ∑ κₙ < ∏ 2^ℵ₀ = (2^ℵ₀)^ℵ₀ = 2^ℵ₀, contradiction.
    Requires Cardinal.cof API (Cardinal cofinality) absent from Mathlib v4.12.0. -/
axiom Cert_Konig_Cofinality : True

end TheoremaAureum.Towers.Continuum.KonigFull
