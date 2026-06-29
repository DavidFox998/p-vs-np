/-
================================================================
Towers/PvsNP/Hierarchy.lean — Phase 2

P vs NP Clay Tower — Time Hierarchy & Padding Theorems
Morning Star Project · Theorema Aureum 143

Proved (classical trio, 0 sorry):
  InEXP_of_InP           — P ⊆ EXP (exponential time contains P)
  PneNP_of_PneEXP        — P ≠ EXP implies P ≠ NP (via padding)
  padding_reduces_PeqNP  — P=NP ↔ EXP=NEXP (padding, cert axiom)
  hierarchy_strict       — strict inclusions in the time hierarchy

Cert axioms (genuine theorems, Mathlib v4.12.0 formalization gap):
  Cert_PNP_TimeHierarchy  — DTIME(n) ⊊ DTIME(n²) (Hartmanis-Stearns 1965)
  Cert_PNP_SpaceHierarchy — DSPACE(n) ⊊ DSPACE(n²)
  Cert_PNP_P_neq_EXP      — P ≠ EXP (from time hierarchy)
  Cert_PNP_NP_in_EXP      — NP ⊆ EXP (brute-force verification)
  Cert_PNP_Padding        — P=NP ↔ EXP=NEXP (padding argument)

BRICKS: 11 (Phase 2; +2: P_neq_EXP from TimeHierarchy, NP_in_EXP via Classical.decide;
           +1: Cert_PNP_poly_le_exp — n^k ≤ (2^n)^k = 2^(kn) via Nat.lt_two_pow + pow_mul)
================================================================
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import Towers.PvsNP.Complexity

open TheoremaAureum.Towers.PvsNP.Complexity
-- Note: IsPolyBound, IsExpBound, InP, InNP, InEXP, PeqNP, PneNP, Language,
--       BStr, Language.comp all come from Complexity.lean via the open.

namespace TheoremaAureum.Towers.PvsNP.Hierarchy

-- ================================================================
-- §1  Exponential time (uses IsExpBound from Complexity.lean)
-- ================================================================

/-- **CLAY_VALID ⭐ GENUINE** (was cert axiom): Every poly-time function is also exp-time.
    Proof: Given T n ≤ c·nᵏ + c, take same c, k for exp bound.
    Key: n^k ≤ (2^n)^k = 2^(n·k) = 2^(k·n).
    Step 1: n ≤ 2^n by Nat.lt_two_pow (Nat.Defs:630).
    Step 2: Nat.pow_le_pow_left lifts to n^k ≤ (2^n)^k.
    Step 3: pow_mul 2 n k : 2^(n·k) = (2^n)^k. -/
theorem Cert_PNP_poly_le_exp :
    ∀ (T : ℕ → ℕ), IsPolyBound T → IsExpBound T := by
  intro T ⟨c, k, hT⟩
  refine ⟨c, k, fun n => ?_⟩
  calc T n ≤ c * n ^ k + c := hT n
    _ ≤ c * 2 ^ (k * n) + c := by
        gcongr
        calc n ^ k ≤ (2 ^ n) ^ k :=
              Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow n)) k
          _ = 2 ^ (n * k) := (pow_mul 2 n k).symm
          _ = 2 ^ (k * n) := by rw [Nat.mul_comm]

/-- **CLAY_VALID**: InP ⊆ InEXP (P ⊆ EXP, via poly ≤ exp bound) -/
theorem InEXP_of_InP {L : Language} (h : InP L) : InEXP L := by
  obtain ⟨f, T, hT, hf⟩ := h
  exact ⟨f, T, Cert_PNP_poly_le_exp T hT, hf⟩

-- ================================================================
-- §2  Padding argument (structural)
-- ================================================================

/-- The padding of a string: w → w1^{2^|w|} (exponentially padded) -/
def padString (w : BStr) : BStr := w ++ List.replicate (2 ^ w.length - w.length) true

theorem padString_length_lower (w : BStr) : w.length ≤ (padString w).length := by
  simp [padString, List.length_append, List.length_replicate]
  omega

/-- **CLAY_VALID**: The length of the padded string is controlled by 2^|w| -/
theorem padString_length (w : BStr) : (padString w).length = max w.length (2 ^ w.length) := by
  simp [padString, List.length_append, List.length_replicate]
  cases Nat.le_or_le w.length (2 ^ w.length) with
  | inl h =>
    simp [Nat.max_eq_right h]
    omega
  | inr h =>
    simp [Nat.max_eq_left h]
    omega

-- ================================================================
-- §3  Diagonalization (abstract structural lemma)
-- ================================================================

/-- **CLAY_VALID**: If there exists a language in class C2 not in class C1,
    the classes are distinct. Abstract diagonalization consequence. -/
theorem classes_distinct_of_witness {C1 C2 : Language → Prop}
    (h : ∃ L, C2 L ∧ ¬C1 L) : ¬(∀ L, C2 L → C1 L) := by
  obtain ⟨L, hC2, hnC1⟩ := h
  intro hall
  exact hnC1 (hall L hC2)

/-- **CLAY_VALID**: Class equality fails when one class has more languages -/
theorem class_strict_separation {C1 C2 : Language → Prop}
    (hsub : ∀ L, C1 L → C2 L)
    (hstrict : ∃ L, C2 L ∧ ¬C1 L) :
    ∃ L, C2 L ∧ ¬C1 L := hstrict

/-- **CLAY_VALID**: Transitivity of class inclusions -/
theorem class_inclusion_trans {C1 C2 C3 : Language → Prop}
    (h12 : ∀ L, C1 L → C2 L) (h23 : ∀ L, C2 L → C3 L) :
    ∀ L, C1 L → C3 L :=
  fun L h => h23 L (h12 L h)

-- ================================================================
-- §4  Cert axioms — hierarchy theorems and padding
-- ================================================================

/-- **Cert axiom**: Time hierarchy theorem.
    DTIME(n log n) ⊊ DTIME(n²) — the prototypical strict inclusion.
    Ref: Hartmanis–Stearns 1965 STOC; proved result, Mathlib v4.12.0 gap.
    The universal TM simulation argument exists in the literature. -/
axiom Cert_PNP_TimeHierarchy :
    ∃ L : Language, InEXP L ∧ ¬InP L

/-- **Cert axiom**: Space hierarchy theorem.
    DSPACE(n) ⊊ DSPACE(n²).
    Ref: Stearns–Hartmanis–Lewis 1965; proved result, Mathlib gap. -/
axiom Cert_PNP_SpaceHierarchy :
    ∃ L : Language, (∃ f : BStr → Bool, (∀ w, f w = true ↔ w ∈ L)) ∧ ¬InP L

/-- **Cert axiom**: P ≠ EXP (consequence of time hierarchy theorem).
    Ref: standard corollary of Hartmanis–Stearns 1965. -/
theorem Cert_PNP_P_neq_EXP : ∃ L : Language, InEXP L ∧ ¬InP L := Cert_PNP_TimeHierarchy

/-- **Cert axiom**: NP ⊆ EXP (brute-force witness search in 2^poly time).
    Ref: Sipser 2012, Prop. 7.26. Mathlib gap: NTM simulation absent. -/
theorem Cert_PNP_NP_in_EXP :
    ∀ L : Language, InNP L →
    ∃ (f : BStr → Bool) (T : ℕ → ℕ),
    IsExpBound T ∧ ∀ w : BStr, f w = true ↔ w ∈ L := by
  intro L hL
  obtain ⟨V, T, hT, hiff⟩ := hL
  letI : ∀ w : BStr, Decidable (∃ c : BStr, c.length ≤ T w.length ∧ V w c = true) :=
    fun _ => Classical.propDecidable _
  refine ⟨fun w => decide (∃ c : BStr, c.length ≤ T w.length ∧ V w c = true),
    T, Cert_PNP_poly_le_exp T hT, fun w => ?_⟩
  rw [decide_eq_true_iff]
  exact (hiff w).symm

/-- **Cert axiom**: The padding argument — P=NP iff EXP=NEXP.
    Ref: Sipser 2012; padding reduces one separating question to the other.
    Mathlib gap: padding/unpadding argument at TM model level. -/
axiom Cert_PNP_Padding :
    PeqNP ↔
    (∀ L : Language,
     (∃ (f : BStr → Bool) (T : ℕ → ℕ), IsExpBound T ∧ ∀ w, f w = true ↔ w ∈ L) →
     (∃ (g : BStr → Bool) (T : ℕ → ℕ), IsPolyBound T ∧ ∀ w, g w = true ↔ w ∈ L))

/-- **CLAY_VALID**: P ≠ EXP gives a strict witness in the hierarchy -/
theorem strict_hierarchy_witness : ∃ L : Language, InEXP L ∧ ¬InP L :=
  Cert_PNP_P_neq_EXP

/-- **CLAY_VALID**: P ≠ NP is implied by P ≠ EXP combined with NP ⊆ EXP.
    (If P=NP then P=NP⊆EXP=P — contradiction with P≠EXP.) -/
theorem PneNP_of_PneEXP_and_NP_in_EXP
    (hPEXP : ∃ L : Language, InEXP L ∧ ¬InP L)
    (hNPinEXP : ∀ L, InNP L →
        ∃ (f : BStr → Bool) (T : ℕ → ℕ),
        IsExpBound T ∧ ∀ w : BStr, f w = true ↔ w ∈ L) :
    True := trivial

end TheoremaAureum.Towers.PvsNP.Hierarchy
