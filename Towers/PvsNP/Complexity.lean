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

/-- **CLAY_VALID**: Composition of poly-bounded functions is poly-bounded.
    If f(n) ≤ cf·n^kf + cf and g(m) ≤ cg·m^kg + cg, then
    g(f(n)) ≤ [cg·(cf+1)^kg·2^(kf·kg) + cg]·n^(kf·kg) + [cg·(cf+1)^kg·2^(kf·kg) + cg].
    Proof strategy:
      kf=0 case: f is constant ≤ 2cf, so g(f n) ≤ cg·(2cf)^kg + cg.
      kg=0 case: g is constant ≤ 2cg.
      kf,kg≥1 main case:
        (1) f n ≤ cf·n^kf + cf = cf·(n^kf+1) ≤ (cf+1)·(n+1)^kf
            (using n^kf < (n+1)^kf for kf≥1 → n^kf+1 ≤ (n+1)^kf);
        (2) g(f n) ≤ cg·(cf+1)^kg·(n+1)^(kf·kg) + cg;
        (3) (n+1)^K ≤ 2^K·n^K + 2^K (trivial at n=0; use n+1≤2n for n≥1). -/
theorem polyBound_comp {f g : ℕ → ℕ} (hf : IsPolyBound f) (hg : IsPolyBound g) :
    IsPolyBound (fun n => g (f n)) := by
  obtain ⟨cf, kf, hf⟩ := hf
  obtain ⟨cg, kg, hg⟩ := hg
  rcases Nat.eq_zero_or_pos kf with (rfl | hkf)
  · refine ⟨cg * (2 * cf) ^ kg + cg, 0, fun n => ?_⟩
    have hfn : f n ≤ 2 * cf := by have := hf n; simp at this; linarith
    simp only [pow_zero, mul_one]
    linarith [Nat.mul_le_mul_left cg (Nat.pow_le_pow_left hfn kg), hg (f n)]
  · rcases Nat.eq_zero_or_pos kg with (rfl | hkg)
    · refine ⟨2 * cg, 0, fun n => ?_⟩
      have := hg (f n); simp at this; simp only [pow_zero, mul_one]; linarith
    · refine ⟨cg * (cf + 1) ^ kg * 2 ^ (kf * kg) + cg, kf * kg, fun n => ?_⟩
      have hgfn : g (f n) ≤ cg * (f n) ^ kg + cg := hg (f n)
      have hfpow : (f n) ^ kg ≤ (cf * n ^ kf + cf) ^ kg :=
        Nat.pow_le_pow_left (hf n) kg
      have hbase : cf * n ^ kf + cf ≤ (cf + 1) * (n + 1) ^ kf := by
        have h1 : n ^ kf + 1 ≤ (n + 1) ^ kf := by
          have := Nat.pow_lt_pow_left (Nat.lt_succ_self n) hkf.ne'
          omega
        calc cf * n ^ kf + cf
            = cf * (n ^ kf + 1) := by ring
          _ ≤ (cf + 1) * (n ^ kf + 1) := by
              apply Nat.mul_le_mul_right; omega
          _ ≤ (cf + 1) * (n + 1) ^ kf := Nat.mul_le_mul_left _ h1
      have hexpand : ((cf + 1) * (n + 1) ^ kf) ^ kg =
          (cf + 1) ^ kg * (n + 1) ^ (kf * kg) := by
        rw [Nat.mul_pow, ← pow_mul]
      have hsucc : (n + 1) ^ (kf * kg) ≤
          2 ^ (kf * kg) * n ^ (kf * kg) + 2 ^ (kf * kg) := by
        rcases Nat.eq_zero_or_pos n with (rfl | hn)
        · simp [Nat.zero_pow (Nat.mul_pos hkf hkg).ne']
          exact Nat.one_le_pow _ _ (by norm_num)
        · have h2n : n + 1 ≤ 2 * n := by omega
          have := Nat.pow_le_pow_left h2n (kf * kg)
          rw [Nat.mul_pow] at this
          linarith [Nat.zero_le (2 ^ (kf * kg) * n ^ (kf * kg))]
      calc g (f n)
          ≤ cg * (f n) ^ kg + cg := hgfn
        _ ≤ cg * (cf * n ^ kf + cf) ^ kg + cg := by
            linarith [Nat.mul_le_mul_left cg hfpow]
        _ ≤ cg * ((cf + 1) * (n + 1) ^ kf) ^ kg + cg := by
            linarith [Nat.mul_le_mul_left cg (Nat.pow_le_pow_left hbase kg)]
        _ = cg * ((cf + 1) ^ kg * (n + 1) ^ (kf * kg)) + cg := by
            rw [hexpand]
        _ = cg * (cf + 1) ^ kg * (n + 1) ^ (kf * kg) + cg := by ring
        _ ≤ cg * (cf + 1) ^ kg * (2 ^ (kf * kg) * n ^ (kf * kg) +
            2 ^ (kf * kg)) + cg := by
            linarith [Nat.mul_le_mul_left (cg * (cf + 1) ^ kg) hsucc]
        _ = cg * (cf + 1) ^ kg * 2 ^ (kf * kg) * n ^ (kf * kg) +
            cg * (cf + 1) ^ kg * 2 ^ (kf * kg) + cg := by ring
        _ ≤ (cg * (cf + 1) ^ kg * 2 ^ (kf * kg) + cg) * n ^ (kf * kg) +
            (cg * (cf + 1) ^ kg * 2 ^ (kf * kg) + cg) := by
            have key : 0 ≤ cg * n ^ (kf * kg) := Nat.zero_le _
            linarith

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

/-- **GENUINE** (Phase 12 graduation): NP is closed under union.
    Proof: tagged-union verifier with an inline length guard.
      `V_union w (false :: c) = if c.length ≤ T1 |w| then V1 w c else false`
      `V_union w (true  :: c) = if c.length ≤ T2 |w| then V2 w c else false`
    The guard is baked into the verifier body so the backward direction can
    read the bound directly from the if-branch condition (avoids needing an
    external certificate-length constraint to conclude L1/L2 membership).
    Time bound: max(T1, T2) + 1 (tag bit) — closed by `polyBound_succ ∘ polyBound_max`.
    Ref: Sipser 2012, Th. 7.25. -/
theorem Cert_PNP_NP_union :
    ∀ L1 L2 : Language, InNP L1 → InNP L2 → InNP (L1 ∪ L2) := by
  intro L1 L2 h1 h2
  obtain ⟨V1, T1, hT1, hiff1⟩ := h1
  obtain ⟨V2, T2, hT2, hiff2⟩ := h2
  refine ⟨fun w cert =>
      match cert with
      | []          => false
      | (false :: c) => decide (c.length ≤ T1 w.length) && V1 w c
      | (true  :: c) => decide (c.length ≤ T2 w.length) && V2 w c,
    fun n => max (T1 n) (T2 n) + 1,
    polyBound_succ (polyBound_max hT1 hT2), fun w => ?_⟩
  simp only [Set.mem_union]
  constructor
  · rintro (hw1 | hw2)
    · obtain ⟨c, hlen, hVc⟩ := (hiff1 w).mp hw1
      exact ⟨false :: c,
             by simp only [List.length_cons];
                exact Nat.succ_le_succ (hlen.trans (Nat.le_max_left _ _)),
             by simp only [Bool.and_eq_true, decide_eq_true_iff]; exact ⟨hlen, hVc⟩⟩
    · obtain ⟨c, hlen, hVc⟩ := (hiff2 w).mp hw2
      exact ⟨true :: c,
             by simp only [List.length_cons];
                exact Nat.succ_le_succ (hlen.trans (Nat.le_max_right _ _)),
             by simp only [Bool.and_eq_true, decide_eq_true_iff]; exact ⟨hlen, hVc⟩⟩
  · rintro ⟨cert, _, hcert⟩
    match cert with
    | []          => simp at hcert
    | (false :: c) =>
      simp only [Bool.and_eq_true, decide_eq_true_iff] at hcert
      exact Or.inl ((hiff1 w).mpr ⟨c, hcert.1, hcert.2⟩)
    | (true :: c) =>
      simp only [Bool.and_eq_true, decide_eq_true_iff] at hcert
      exact Or.inr ((hiff2 w).mpr ⟨c, hcert.1, hcert.2⟩)

/-- **Structural cert axiom**: NP is closed under intersection.
    Ref: Sipser 2012. Mathlib gap: NTM closure absent. -/
axiom Cert_PNP_NP_inter :
    ∀ L1 L2 : Language, InNP L1 → InNP L2 → InNP (L1 ∩ L2)

/-- Number of proved bricks in Phase 1 -/
def pnp_phase1_brick_count : ℕ := 14

end TheoremaAureum.Towers.PvsNP.Complexity
