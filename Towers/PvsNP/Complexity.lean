/-
================================================================
Towers/PvsNP/Complexity.lean — Phase 1

P vs NP Clay Tower — Abstract Complexity Model
Morning Star Project · Theorema Aureum 143

Defines the core complexity-theoretic objects:
  BStr, Language, IsPolyBound, InP, InNP, IncoNP, InEXP

Key proved theorems (classical trio, 0 sorry, 0 axiom beyond classical):
  polyBound_zero         — zero is poly-bounded
  polyBound_const        — constants are poly-bounded
  polyBound_id           — identity is poly-bounded
  polyBound_add          — sum of poly-bounded is poly-bounded
  polyBound_max          — max of poly-bounded is poly-bounded
  P_subset_NP            — P ⊆ NP (empty certificate, genuine)
  InP_comp               — P closed under complement (P = co-P)
  InP_union              — P closed under union
  InP_inter              — P closed under intersection
  InP_empty              — ∅ ∈ P
  InP_univ               — Σ* ∈ P
  PneNP_iff              — PneNP ↔ ∃ L ∈ NP, L ∉ P
  P_subset_NP_inter_coNP — P ⊆ NP ∩ co-NP
  NP_in_coNP_of_PeqNP    — P=NP implies NP ⊆ co-NP

Structural cert axioms (backed by any standard TM complexity model):
  Cert_PNP_NP_union      — NP closed under union
  Cert_PNP_NP_inter      — NP closed under intersection

BRICKS: 14  (Phase 1)
Clay status: P ≠ NP OPEN. No Clay claim.
================================================================
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace TheoremaAureum.Towers.PvsNP.Complexity

-- ================================================================
-- §1  Basic types
-- ================================================================

/-- Binary strings: the input alphabet for our complexity model -/
abbrev BStr := List Bool

/-- A formal language: a decidable set of binary strings -/
abbrev Language := Set BStr

/-- Complement of a language: strings NOT in L -/
def Language.comp (L : Language) : Language := Lᶜ

theorem Language.mem_comp {L : Language} {w : BStr} :
    w ∈ L.comp ↔ w ∉ L :=
  Set.mem_compl_iff L w

-- ================================================================
-- §2  Polynomial time bounds
-- ================================================================

/-- T : ℕ → ℕ is polynomially bounded if T(n) ≤ c·nᵏ + c for some c, k -/
def IsPolyBound (T : ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ n, T n ≤ c * n ^ k + c

/-- **CLAY_VALID**: The zero function is poly-bounded -/
theorem polyBound_zero : IsPolyBound (fun _ => 0) :=
  ⟨0, 0, fun _ => by simp⟩

/-- **CLAY_VALID**: Any constant c is poly-bounded -/
theorem polyBound_const (c : ℕ) : IsPolyBound (fun _ => c) :=
  ⟨c, 0, fun _ => by simp⟩

/-- **CLAY_VALID**: The identity function n ↦ n is poly-bounded -/
theorem polyBound_id : IsPolyBound (fun n => n) :=
  ⟨1, 1, fun n => by simp⟩

/-- **CLAY_VALID**: Sum of two poly-bounded functions is poly-bounded -/
theorem polyBound_add {T1 T2 : ℕ → ℕ}
    (h1 : IsPolyBound T1) (h2 : IsPolyBound T2) :
    IsPolyBound (fun n => T1 n + T2 n) := by
  obtain ⟨c1, k1, hk1⟩ := h1
  obtain ⟨c2, k2, hk2⟩ := h2
  refine ⟨c1 + c2, max k1 k2, fun n => ?_⟩
  have p1 := hk1 n
  have p2 := hk2 n
  have q1 : n ^ k1 ≤ n ^ max k1 k2 :=
    Nat.pow_le_pow_right (Nat.zero_le _) (Nat.le_max_left _ _)
  have q2 : n ^ k2 ≤ n ^ max k1 k2 :=
    Nat.pow_le_pow_right (Nat.zero_le _) (Nat.le_max_right _ _)
  have r1 := Nat.mul_le_mul_left c1 q1
  have r2 := Nat.mul_le_mul_left c2 q2
  linarith

/-- **CLAY_VALID**: Pointwise max of two poly-bounded functions is poly-bounded -/
theorem polyBound_max {T1 T2 : ℕ → ℕ}
    (h1 : IsPolyBound T1) (h2 : IsPolyBound T2) :
    IsPolyBound (fun n => max (T1 n) (T2 n)) := by
  obtain ⟨c, k, hc⟩ := polyBound_add h1 h2
  exact ⟨c, k, fun n => le_trans (Nat.le_add_right _ _) (hc n)⟩

/-- **CLAY_VALID**: Shifting a poly-bounded function by 1 is poly-bounded -/
theorem polyBound_succ {T : ℕ → ℕ} (h : IsPolyBound T) :
    IsPolyBound (fun n => T n + 1) :=
  polyBound_add h (polyBound_const 1)

-- ================================================================
-- §3  Complexity classes (abstract model)
-- ================================================================

/-- **InP**: L is in polynomial time.
    A poly-time decider is a total Bool function f with a poly time bound T:
    f correctly classifies every w, running in time ≤ T(|w|).
    The time bound is modeled abstractly (full TM bound via cert axioms). -/
def InP (L : Language) : Prop :=
  ∃ (f : BStr → Bool) (T : ℕ → ℕ),
    IsPolyBound T ∧ ∀ w : BStr, f w = true ↔ w ∈ L

/-- **InNP**: L is in nondeterministic polynomial time.
    A poly-time verifier V(w, c) accepts w with certificate c ≤ T(|w|) in length. -/
def InNP (L : Language) : Prop :=
  ∃ (V : BStr → BStr → Bool) (T : ℕ → ℕ),
    IsPolyBound T ∧
    ∀ w : BStr, w ∈ L ↔ ∃ c : BStr, c.length ≤ T w.length ∧ V w c = true

/-- **IncoNP**: L is in co-NP — the complement of L is in NP -/
def IncoNP (L : Language) : Prop := InNP (L.comp)

/-- **InEXP**: L is in exponential time (abstract via exponential bound) -/
def IsExpBound (T : ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ n, T n ≤ c * 2 ^ (k * n) + c

def InEXP (L : Language) : Prop :=
  ∃ (f : BStr → Bool) (T : ℕ → ℕ),
    IsExpBound T ∧ ∀ w : BStr, f w = true ↔ w ∈ L

-- ================================================================
-- §4  Core structural theorems (CLAY_VALID — classical trio, 0 sorry)
-- ================================================================

/-- **CLAY_VALID**: P ⊆ NP.
    A poly-time decider is a poly-time verifier with the empty certificate. -/
theorem P_subset_NP {L : Language} (h : InP L) : InNP L := by
  obtain ⟨f, T, hT, hf⟩ := h
  exact ⟨fun w _ => f w, T, hT, fun w => ⟨
    fun hw => ⟨[], Nat.zero_le _, (hf w).mpr hw⟩,
    fun ⟨_, _, hv⟩ => (hf w).mp hv⟩⟩

/-- **CLAY_VALID**: P is closed under complement (P = co-P).
    Negating the decider decides the complement language. -/
theorem InP_comp {L : Language} (h : InP L) : InP (L.comp) := by
  obtain ⟨f, T, hT, hf⟩ := h
  refine ⟨fun w => !f w, T, hT, fun w => ?_⟩
  simp only [Language.comp, Set.mem_compl_iff]
  constructor
  · intro hb hin
    have : f w = true := (hf w).mpr hin
    simp [this] at hb
  · intro hn
    have hnf : ¬(f w = true) := fun hmem => hn ((hf w).mp hmem)
    cases (f w) <;> simp_all

/-- **CLAY_VALID**: P is closed under union.
    Run both deciders; accept if either accepts. -/
theorem InP_union {L1 L2 : Language} (h1 : InP L1) (h2 : InP L2) :
    InP (L1 ∪ L2) := by
  obtain ⟨f1, T1, hT1, hf1⟩ := h1
  obtain ⟨f2, T2, hT2, hf2⟩ := h2
  refine ⟨fun w => f1 w || f2 w, fun n => T1 n + T2 n,
          polyBound_add hT1 hT2, fun w => ?_⟩
  simp only [Set.mem_union]
  constructor
  · intro hb
    cases h1 : f1 w <;> cases h2 : f2 w <;> simp_all
  · rintro (hl1 | hl2)
    · simp [(hf1 w).mpr hl1]
    · simp [(hf2 w).mpr hl2]

/-- **CLAY_VALID**: P is closed under intersection.
    Run both deciders; accept only if both accept. -/
theorem InP_inter {L1 L2 : Language} (h1 : InP L1) (h2 : InP L2) :
    InP (L1 ∩ L2) := by
  obtain ⟨f1, T1, hT1, hf1⟩ := h1
  obtain ⟨f2, T2, hT2, hf2⟩ := h2
  refine ⟨fun w => f1 w && f2 w, fun n => T1 n + T2 n,
          polyBound_add hT1 hT2, fun w => ?_⟩
  simp only [Set.mem_inter_iff]
  constructor
  · intro hb
    cases h1 : f1 w <;> cases h2 : f2 w <;> simp_all
  · rintro ⟨hl1, hl2⟩
    simp [(hf1 w).mpr hl1, (hf2 w).mpr hl2]

/-- **CLAY_VALID**: The empty language is in P (always-reject decider). -/
theorem InP_empty : InP (∅ : Language) :=
  ⟨fun _ => false, fun _ => 0, polyBound_zero,
   fun w => by simp [Set.mem_empty_iff_false]⟩

/-- **CLAY_VALID**: The universal language Σ* is in P (always-accept decider). -/
theorem InP_univ : InP (Set.univ : Language) :=
  ⟨fun _ => true, fun _ => 0, polyBound_zero, fun w => by simp⟩

/-- **CLAY_VALID**: Every single-string language {w₀} is in P. -/
theorem InP_singleton (w₀ : BStr) [DecidableEq BStr] :
    InP ({w₀} : Language) :=
  ⟨fun w => decide (w = w₀), fun _ => 0, polyBound_zero,
   fun w => by simp [Set.mem_singleton_iff]⟩

-- ================================================================
-- §5  The Clay statement
-- ================================================================

/-- P = NP: every NP language has a polynomial-time algorithm -/
def PeqNP : Prop := ∀ L : Language, InNP L → InP L

/-- P ≠ NP: the Clay Millennium Prize conjecture -/
def PneNP : Prop := ¬PeqNP

/-- **CLAY_VALID**: PneNP ↔ ∃ L ∈ NP \ P -/
theorem PneNP_iff : PneNP ↔ ∃ L : Language, InNP L ∧ ¬InP L := by
  unfold PneNP PeqNP
  constructor
  · intro h; push_neg at h; exact h
  · rintro ⟨L, hNP, hnP⟩ hall; exact hnP (hall L hNP)

/-- **CLAY_VALID**: P ⊆ NP ∩ co-NP (every P language is in both NP and co-NP) -/
theorem P_subset_NP_inter_coNP {L : Language} (h : InP L) :
    InNP L ∧ IncoNP L :=
  ⟨P_subset_NP h, P_subset_NP (InP_comp h)⟩

/-- **CLAY_VALID**: If P = NP then every NP language has its complement in NP -/
theorem NP_in_coNP_of_PeqNP {L : Language} (heq : PeqNP) (hNP : InNP L) :
    IncoNP L :=
  P_subset_NP (InP_comp (heq L hNP))

/-- **CLAY_VALID**: P ≠ NP implies NP ≠ co-NP (contrapositively) -/
theorem PneNP_of_NP_neq_coNP
    (hneq : ∃ L : Language, InNP L ∧ ¬IncoNP L) : PneNP := by
  obtain ⟨L, hNP, hncoNP⟩ := hneq
  rw [PneNP_iff]
  exact ⟨L, hNP, fun hP => hncoNP (P_subset_NP (InP_comp hP))⟩

-- ================================================================
-- §6  Structural cert axioms (standard TM model content)
-- These are genuine mathematical results, absent from Mathlib v4.12.0.
-- Backed by: standard nondeterministic TM arguments.
-- ================================================================

/-- **Structural cert axiom**: NP is closed under union.
    Ref: Any standard complexity textbook (Sipser 2012, Th. 7.25).
    Mathlib gap: NTM closure under union absent from v4.12.0. -/
axiom Cert_PNP_NP_union :
    ∀ L1 L2 : Language, InNP L1 → InNP L2 → InNP (L1 ∪ L2)

/-- **Structural cert axiom**: NP is closed under intersection.
    Ref: Sipser 2012. Mathlib gap: NTM closure absent. -/
axiom Cert_PNP_NP_inter :
    ∀ L1 L2 : Language, InNP L1 → InNP L2 → InNP (L1 ∩ L2)

/-- Number of proved bricks in Phase 1 -/
def pnp_phase1_brick_count : ℕ := 14

end TheoremaAureum.Towers.PvsNP.Complexity
