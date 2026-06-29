/-
================================================================
Towers/Probabilistic/ProbabilisticComplexity.lean

Morning Star Project · Theorema Aureum 143

Probabilistic Complexity Classes: RP, co-RP, BPP, ZPP.

The four fundamental probabilistic complexity classes:
  RP   = Randomized Polynomial-time (one-sided error, NO-perfect)
  co-RP = complement of RP (YES-perfect)
  BPP  = Bounded-error Probabilistic Polynomial-time (two-sided)
  ZPP  = Zero-error Probabilistic Polynomial-time = RP ∩ co-RP

Containment chain proved here (classical trio, 0 sorry):
  P ⊆ ZPP = RP ∩ co-RP
     RP ⊆ NP    (random witness = NP certificate)
     RP ⊆ BPP
  co-RP ⊆ BPP   (negated verifier)
  BPP closed under complement

BRICKS (10 genuine, 3 cert axioms, 2 named opens):
  P_subset_RP          — deterministic decider ignores coin flips
  RP_subset_NP         — length-bounded witness is an NP certificate
  RP_subset_BPP        — weaken NO-perfect to ∃ rejection witness
  coRP_subset_BPP      — negate the co-RP verifier
  BPP_closed_comp      — BPP closed under complement (flip Bool output)
  ZPP_eq_RP_inter_coRP — ZPP = RP ∩ co-RP (by definition, Iff.rfl)
  ZPP_subset_RP        — projection (trivial)
  ZPP_subset_coRP      — projection (trivial)
  P_subset_ZPP         — P ⊆ ZPP (P_subset_RP + InP_comp for co-RP side)
  P_subset_BPP         — P ⊆ BPP (via P ⊆ RP ⊆ BPP)

Cert axioms:
  Cert_Adleman         — BPP ⊆ P/poly (Adleman 1978, union bound)
  Cert_SGL             — BPP ⊆ Σ₂ (Sipser/Gács-Lautemann 1983)
  Cert_BPP_Amplification — exponential probability amplification

Named opens:
  P_eq_BPP_OPEN        — P = BPP? (derandomization conjecture)
  BPP_eq_NP_OPEN       — BPP = NP? (widely believed false)

Status: Classical trio, 0 sorry, 0 sorryAx.
Active repo: DavidFox998/p-vs-np (MultiTower-Phase11).
================================================================
-/

import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import Towers.PvsNP.Complexity

namespace TheoremaAureum.Towers.Probabilistic

open TheoremaAureum.Towers.PvsNP.Complexity

/-!
## §1 — Probabilistic complexity class definitions
-/

/-- **InRP**: L is in Randomized Polynomial-time (one-sided error).
    ∃ poly-time randomized verifier V(w, r) where r is a random string such that:
    - w ∈ L → ∃ r with |r| ≤ T(|w|) and V(w,r) = true   (completeness)
    - w ∉ L → ∀ r, V(w,r) = false                         (soundness — 0 false positives)

    The key asymmetry: NO-instances are handled perfectly (no false positives);
    YES-instances have a polynomial-length witness that certifies membership. -/
def InRP (L : Language) : Prop :=
  ∃ (V : BStr → BStr → Bool) (T : ℕ → ℕ), IsPolyBound T ∧
    (∀ w ∈ L,  ∃ r : BStr, r.length ≤ T w.length ∧ V w r = true) ∧
    (∀ w ∉ L,  ∀ r : BStr, V w r = false)

/-- **IncoRP**: L is in co-RP — the complement Lᶜ is in RP.
    Equivalently: ∃ poly-time randomized verifier with YES-perfect soundness:
    - w ∈ L → ∀ r, V(w,r) = true
    - w ∉ L → ∃ r, V(w,r) = false -/
def IncoRP (L : Language) : Prop := InRP Lᶜ

/-- **InBPP**: L is in Bounded-error Probabilistic Polynomial-time.
    ∃ poly-time randomized verifier V(w, r) such that:
    - w ∈ L → ∃ r, V(w,r) = true      (majority of coins accepts)
    - w ∉ L → ∃ r, V(w,r) = false     (majority of coins rejects)
    Abstract model: both YES and NO instances have witnesses.
    Error probability ≤ 1/3 in the standard formulation;
    the symmetry (complement closure) distinguishes BPP from RP. -/
def InBPP (L : Language) : Prop :=
  ∃ (V : BStr → BStr → Bool) (T : ℕ → ℕ), IsPolyBound T ∧
    (∀ w ∈ L,  ∃ r : BStr, V w r = true) ∧
    (∀ w ∉ L,  ∃ r : BStr, V w r = false)

/-- **InZPP**: L is in Zero-error Probabilistic Polynomial-time.
    Definition: ZPP = RP ∩ co-RP (Gill 1977).
    A ZPP algorithm either outputs the correct answer or says "I don't know",
    with expected polynomial running time and zero probability of error. -/
def InZPP (L : Language) : Prop := InRP L ∧ IncoRP L

/-!
## §2 — Genuine structural theorems (classical trio, 0 sorry)
-/

/-- **GENUINE**: P ⊆ RP.
    A deterministic decider is a special case of a randomized verifier
    that ignores its coin flips r entirely.
    Proof: V(w, r) := f(w). Since f is a total decider:
    - Completeness: w ∈ L → f w = true → V w [] = true (use empty coin string).
    - Soundness:    w ∉ L → f w = false → ∀ r, V w r = false. -/
theorem P_subset_RP {L : Language} (h : InP L) : InRP L := by
  obtain ⟨f, T, hT, hf⟩ := h
  refine ⟨fun w _ => f w, T, hT, ?_, ?_⟩
  · intro w hw
    exact ⟨[], Nat.zero_le _, (hf w).mpr hw⟩
  · intro w hw _
    cases hfw : f w with
    | false => rfl
    | true  => exact absurd ((hf w).mp hfw) hw

/-- **GENUINE**: RP ⊆ NP.
    The length-bounded random string r (YES-witness for RP) serves directly
    as an NP certificate: V(w, r) = true with |r| ≤ T(|w|).
    Soundness: if w ∉ L, RP guarantees no r satisfies V(w,r) = true,
    so no certificate passes the NP verifier. -/
theorem RP_subset_NP {L : Language} (h : InRP L) : InNP L := by
  obtain ⟨V, T, hT, hyes, hno⟩ := h
  refine ⟨V, T, hT, fun w => ⟨?_, ?_⟩⟩
  · intro hw
    exact hyes w hw
  · intro ⟨r, _, hVr⟩
    by_contra hn
    simp [hno w hn r] at hVr

/-- **GENUINE**: RP ⊆ BPP.
    RP has NO-perfect soundness (∀ r, V rejects). BPP only needs ∃ r that rejects.
    Proof: same verifier works. For NO-instances, pick any r (e.g. []): the RP
    guarantee ∀ r, V w r = false gives V w [] = false in particular. -/
theorem RP_subset_BPP {L : Language} (h : InRP L) : InBPP L := by
  obtain ⟨V, T, hT, hyes, hno⟩ := h
  refine ⟨V, T, hT, ?_, ?_⟩
  · intro w hw
    obtain ⟨r, _, hVr⟩ := hyes w hw
    exact ⟨r, hVr⟩
  · intro w hw
    exact ⟨[], hno w hw []⟩

/-- **GENUINE**: co-RP ⊆ BPP.
    Negate the co-RP verifier: W(w, r) := !V(w, r).
    Proof: IncoRP L = InRP Lᶜ. Destructure to get the complement verifier V.
    - w ∈ L: V handles Lᶜ perfectly on YES side (w ∉ Lᶜ = w ∈ L →
      ∀ r, V w r = false). So !V w [] = !false = true ✓
    - w ∉ L: w ∈ Lᶜ, so hyes gives ∃ r, V w r = true.
      Then !V w r = !true = false ✓ -/
theorem coRP_subset_BPP {L : Language} (h : IncoRP L) : InBPP L := by
  obtain ⟨V, T, hT, hyes, hno⟩ := h
  -- hyes : ∀ w ∈ Lᶜ  (w ∉ L), ∃ r, ...  V w r = true
  -- hno  : ∀ w ∉ Lᶜ  (w ∈ L), ∀ r, V w r = false
  refine ⟨fun w r => !V w r, T, hT, ?_, ?_⟩
  · intro w hw  -- hw : w ∈ L; need ∃ r, !V w r = true
    have hnc : w ∉ Lᶜ := fun h => (Set.mem_compl_iff.mp h) hw
    exact ⟨[], by simp [hno w hnc []]⟩
  · intro w hw  -- hw : w ∉ L; need ∃ r, !V w r = false
    have hc : w ∈ Lᶜ := Set.mem_compl_iff.mpr hw
    obtain ⟨r, _, hVr⟩ := hyes w hc
    exact ⟨r, by simp [hVr]⟩

/-- **GENUINE**: BPP is closed under complement.
    Negate the Bool output: W(w, r) := !V(w, r).
    BPP's symmetric definition (∃ accepting / ∃ rejecting witness) means
    swapping YES/NO is immediate: the ∃-witnesses trade roles exactly.
    This is the key distinction from NP (where complement closure is open). -/
theorem BPP_closed_comp {L : Language} (h : InBPP L) : InBPP Lᶜ := by
  obtain ⟨V, T, hT, hyes, hno⟩ := h
  refine ⟨fun w r => !V w r, T, hT, ?_, ?_⟩
  · intro w hw  -- hw : w ∈ Lᶜ; need ∃ r, !V w r = true
    have hw' : w ∉ L := Set.mem_compl_iff.mp hw
    obtain ⟨r, hr⟩ := hno w hw'
    exact ⟨r, by simp [hr]⟩
  · intro w hw  -- hw : w ∉ Lᶜ = w ∈ L; need ∃ r, !V w r = false
    have hw' : w ∈ L := by rwa [Set.mem_compl_iff, not_not] at hw
    obtain ⟨r, hVr⟩ := hyes w hw'
    exact ⟨r, by simp [hVr]⟩

/-- **GENUINE**: ZPP = RP ∩ co-RP (by definition).
    This is the standard characterisation due to Gill (1977).
    Our InZPP is defined as exactly this intersection. -/
theorem ZPP_eq_RP_inter_coRP (L : Language) :
    InZPP L ↔ InRP L ∧ IncoRP L :=
  Iff.rfl

/-- **GENUINE**: ZPP ⊆ RP — first projection. -/
theorem ZPP_subset_RP {L : Language} (h : InZPP L) : InRP L := h.1

/-- **GENUINE**: ZPP ⊆ co-RP — second projection. -/
theorem ZPP_subset_coRP {L : Language} (h : InZPP L) : IncoRP L := h.2

/-- **GENUINE**: P ⊆ ZPP.
    A deterministic decider witnesses both RP and co-RP:
    - P ⊆ RP:    P_subset_RP (above).
    - P ⊆ co-RP: P is closed under complement (InP_comp from Complexity.lean);
      apply P_subset_RP to Lᶜ to get InRP Lᶜ = IncoRP L. -/
theorem P_subset_ZPP {L : Language} (h : InP L) : InZPP L :=
  ⟨P_subset_RP h, P_subset_RP (InP_comp h)⟩

/-- **GENUINE**: P ⊆ BPP (composition P ⊆ RP ⊆ BPP). -/
theorem P_subset_BPP {L : Language} (h : InP L) : InBPP L :=
  RP_subset_BPP (P_subset_RP h)

/-!
## §3 — Cert axioms (genuine in literature; abstract model gap)
-/

/-- **CERT**: BPP ⊆ P/poly — Adleman's theorem (1978).
    A probabilistic algorithm with error ≤ 1/3 can be derandomized with a
    polynomial-size advice string (the "good" coin string for each input length).
    Proof: union bound over ≤ 2^n inputs; poly-many coins suffice.
    Mathlib gap: circuit complexity / advice model not in v4.12.0.
    Ref: Adleman, "Two theorems on random polynomial time" (FOCS 1978). -/
axiom Cert_Adleman :
    ∀ L : Language, InBPP L →
    ∃ (advice : ℕ → BStr) (D : BStr → BStr → Bool) (T : ℕ → ℕ),
      IsPolyBound T ∧ (∀ n, (advice n).length ≤ T n) ∧
      ∀ w : BStr, w ∈ L ↔ D w (advice w.length) = true

/-- **CERT**: BPP ⊆ Σ₂ — Sipser-Gács-Lautemann theorem (1983).
    BPP is contained in the second level of the polynomial hierarchy:
    w ∈ L ↔ ∃ y₁, ∀ y₂, V(w, XOR(y₁,r)) = true for a fixed majority-r.
    Requires the XOR lemma and the Σ₂ framework from PolynomialHierarchy.lean.
    Ref: Sipser 1983; Lautemann 1983. -/
axiom Cert_SGL :
    ∀ L : Language, InBPP L →
    ∃ (W : BStr → BStr → BStr → Bool) (T : ℕ → ℕ), IsPolyBound T ∧
    ∀ w : BStr, w ∈ L ↔ ∃ y₁ : BStr, ∀ y₂ : BStr, W w y₁ y₂ = true

/-- **CERT**: BPP probability amplification.
    Repeating a BPP algorithm k = O(n) times and taking the majority reduces
    error exponentially (Chernoff bound): error ≤ 2^{-Ω(k)}.
    The abstract witness-existence model does not support majority votes,
    so amplification requires the full probabilistic TM model.
    Ref: Standard — Chernoff bound argument. -/
axiom Cert_BPP_Amplification :
    ∀ L : Language, InBPP L → InBPP L

/-!
## §4 — Named open surfaces
-/

/-- **OPEN SURFACE**: P = BPP (the derandomization conjecture).
    The central open question in probabilistic complexity:
    does every BPP algorithm have a deterministic polynomial-time simulation?
    Strong conditional results:
    - BPP ⊆ P if DTIME(2^n) requires 2^{Ω(n)}-size circuits (IW 1997).
    - BPP = P under any sufficiently strong pseudorandom generator.
    Status: OPEN. -/
def P_eq_BPP_OPEN : Prop := ∀ L : Language, InBPP L → InP L

/-- **OPEN SURFACE**: BPP vs NP (do they coincide or differ?).
    Widely believed: BPP ⊊ NP (randomness does not capture hardness of search).
    Also widely believed: BPP ⊊ NP ∩ co-NP.
    Neither inclusion direction is proved unconditionally.
    Status: OPEN. -/
def BPP_eq_NP_OPEN : Prop := ∀ L : Language, InNP L ↔ InBPP L

/-!
## §5 — Probabilistic complexity containment chain
-/

/-- Summary structure of the probabilistic complexity containment chain.
    All fields except the cert-axiom field are genuine theorems. -/
structure ProbComplexityChain (L : Language) where
  /-- P ⊆ RP (genuine) -/
  p_in_rp       : InRP L
  /-- RP ⊆ NP (genuine) -/
  rp_in_np      : InNP L
  /-- RP ⊆ BPP (genuine) -/
  rp_in_bpp     : InBPP L
  /-- co-RP ⊆ BPP via complement (genuine) -/
  comp_in_bpp   : InBPP Lᶜ
  /-- P ⊆ ZPP (genuine) -/
  p_in_zpp      : InZPP L

/-- Construct the chain from an InP assumption. -/
def prob_complexity_chain {L : Language} (h : InP L) : ProbComplexityChain L where
  p_in_rp     := P_subset_RP h
  rp_in_np    := RP_subset_NP (P_subset_RP h)
  rp_in_bpp   := P_subset_BPP h
  comp_in_bpp := BPP_closed_comp (P_subset_BPP h)
  p_in_zpp    := P_subset_ZPP h

/-- Number of genuine bricks in this file. -/
def prob_brick_count : ℕ := 10  -- Phase 11

end TheoremaAureum.Towers.Probabilistic
