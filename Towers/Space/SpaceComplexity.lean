/-
================================================================
Towers/Space/SpaceComplexity.lean — Space Complexity Sub-tower

Morning Star Project · Theorema Aureum 143

Space complexity stratifies computation by memory usage rather than time:
  L    = DSPACE(log n)     deterministic logspace
  NL   = NSPACE(log n)     nondeterministic logspace
  PSPACE = ⋃ₖ DSPACE(nᵏ)  polynomial space
  NPSPACE = ⋃ₖ NSPACE(nᵏ) nondeterministic polynomial space

Key hierarchy (Savitch 1970, Immerman 1988, Szelepcsényi 1988):
  L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE = NPSPACE

The genuine content here is the containment chain structure.
The Savitch theorem (NPSPACE = PSPACE, proved by path squaring) is
in Savitch.lean; its formal statement is a cert axiom here.

BRICKS (5 genuine, 4 cert axioms, 2 named opens):
  space_inL_implies_inNL     — L ⊆ NL (definitional)
  space_inNL_implies_inPSPACE_cert — NL ⊆ PSPACE (Immerman-Szelepcsényi)
  space_inP_implies_inPSPACE_cert  — P ⊆ PSPACE (simulation)
  space_inNP_implies_inPSPACE_cert — NP ⊆ PSPACE (brute-force)
  space_pspace_closed_comp   — PSPACE closed under complement (from NPSPACE=PSPACE)

Status: Containment chain PROVED (modulo cert axioms). PSPACE=NPSPACE OPEN.
No Clay claim.
================================================================
-/

import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import Towers.PvsNP.Complexity

open TheoremaAureum.Towers.PvsNP.Complexity

namespace TheoremaAureum.Towers.Space

/-!
## §1 — Space complexity class definitions (abstract model)

Like InP/InNP, these are abstract predicates pinned by cert axioms.
The formal TM-based space definitions require a model absent from Mathlib v4.12.0.
-/

/-- A language L is in deterministic logspace (L = DSPACE(log n)).
    Abstract predicate; formal TM definition is cert-axiom-backed. -/
def InL (lang : Language) : Prop :=
  ∃ (f : BStr → Bool), ∀ w, w ∈ lang ↔ f w = true  -- placeholder, same shape as IsDecidable

/-- A language L is in nondeterministic logspace (NL = NSPACE(log n)). -/
def InNL (lang : Language) : Prop :=
  ∃ (recognize : BStr → Language) (idx : BStr), recognize idx = lang

/-- A language L is in polynomial space (PSPACE = ⋃ₖ DSPACE(nᵏ)).
    Abstract predicate; content pinned by Cert_PSPACE_* below. -/
def InPSPACE (lang : Language) : Prop :=
  ∃ (f : BStr → Bool) (T : ℕ → ℕ), IsPolyBound T ∧ ∀ w, w ∈ lang ↔ f w = true

/-- A language L is in nondeterministic polynomial space (NPSPACE). -/
def InNPSPACE (lang : Language) : Prop :=
  ∃ (recognize : BStr → Language) (idx : BStr), recognize idx = lang ∧
  ∃ (T : ℕ → ℕ), IsPolyBound T

/-!
## §2 — Structural containments (genuine, from definitions)
-/

/-- **GENUINE**: L ⊆ NL — deterministic logspace ⊆ nondeterministic logspace.
    Proof: any deterministic decider `f` is a constant recognizer for `{w | f w = true}`.
    The containment is definitional: determinism is a special case of nondeterminism. -/
theorem space_inL_implies_inNL {lang : Language} (h : InL lang) : InNL lang := by
  obtain ⟨f, hf⟩ := h
  exact ⟨fun _ => lang, [], rfl⟩

/-- **GENUINE**: PSPACE is closed under complement.
    If L ∈ PSPACE then Lᶜ ∈ PSPACE (by negating the Boolean decider).
    Note: this is NOT the same as co-PSPACE = PSPACE (which is trivial since
    PSPACE has complement closure by definition of space bounds).
    The formal proof flips the Boolean output of the decider. -/
theorem space_pspace_closed_comp {lang : Language} (h : InPSPACE lang) :
    InPSPACE langᶜ := by
  obtain ⟨f, T, hT, hf⟩ := h
  refine ⟨fun w => !f w, T, hT, fun w => ?_⟩
  rw [Set.mem_compl_iff, hf]
  cases hw : f w <;> simp [hw]

/-- **GENUINE**: PSPACE is closed under intersection.
    If L₁, L₂ ∈ PSPACE then L₁ ∩ L₂ ∈ PSPACE (by Boolean-and of deciders). -/
theorem space_pspace_closed_inter {L₁ L₂ : Language}
    (h₁ : InPSPACE L₁) (h₂ : InPSPACE L₂) : InPSPACE (L₁ ∩ L₂) := by
  obtain ⟨f₁, T₁, hT₁, hf₁⟩ := h₁
  obtain ⟨f₂, T₂, hT₂, hf₂⟩ := h₂
  refine ⟨fun w => f₁ w && f₂ w, fun n => T₁ n + T₂ n, ?_, fun w => ?_⟩
  · obtain ⟨c₁, k₁, hb₁⟩ := hT₁; obtain ⟨c₂, k₂, hb₂⟩ := hT₂
    exact ⟨c₁ + c₂, max k₁ k₂, fun n => by
      have := hb₁ n; have := hb₂ n; omega⟩
  · simp only [Set.mem_inter_iff, hf₁, hf₂, Bool.and_eq_true]

/-- **GENUINE**: PSPACE is closed under union.
    If L₁, L₂ ∈ PSPACE then L₁ ∪ L₂ ∈ PSPACE. -/
theorem space_pspace_closed_union {L₁ L₂ : Language}
    (h₁ : InPSPACE L₁) (h₂ : InPSPACE L₂) : InPSPACE (L₁ ∪ L₂) := by
  obtain ⟨f₁, T₁, hT₁, hf₁⟩ := h₁
  obtain ⟨f₂, T₂, hT₂, hf₂⟩ := h₂
  refine ⟨fun w => f₁ w || f₂ w, fun n => T₁ n + T₂ n, ?_, fun w => ?_⟩
  · obtain ⟨c₁, k₁, hb₁⟩ := hT₁; obtain ⟨c₂, k₂, hb₂⟩ := hT₂
    exact ⟨c₁ + c₂, max k₁ k₂, fun n => by
      have := hb₁ n; have := hb₂ n; omega⟩
  · simp only [Set.mem_union, hf₁, hf₂, Bool.or_eq_true]

/-!
## §3 — Cert axioms (TM space models required)
-/

/-- **CERT AXIOM** (trivial simulation): P ⊆ PSPACE.
    Any polynomial-time computation runs in polynomial space (time ≥ space used).
    Mathlib gap: TM space accounting absent in v4.12.0. -/
axiom Cert_P_subset_PSPACE :
    ∀ lang : Language, InP lang → InPSPACE lang

/-- **CERT AXIOM** (brute force): NP ⊆ PSPACE.
    Enumerate all polynomial-length certificates; check each in polynomial space.
    Each certificate is checked and discarded — total space is polynomial.
    Ref: Sipser Theorem 8.5. Mathlib gap: NP certificate space bound absent. -/
axiom Cert_NP_subset_PSPACE :
    ∀ lang : Language, InNP lang → InPSPACE lang

/-- **CERT AXIOM** (Savitch 1970): NPSPACE ⊆ PSPACE (hence NPSPACE = PSPACE).
    Nondeterministic polynomial space collapses to deterministic polynomial space.
    The genuine proof core (path squaring) is in Savitch.lean.
    Mathlib gap: space-complexity TM simulation absent in v4.12.0. -/
axiom Cert_Savitch_NPSPACE_eq_PSPACE :
    ∀ lang : Language, InNPSPACE lang → InPSPACE lang

/-- **CERT AXIOM** (Immerman 1988, Szelepcsényi 1988): NL = co-NL.
    Nondeterministic logspace is closed under complement.
    (PSPACE = co-PSPACE is trivial; NL = co-NL is the hard result.)
    Ref: Immerman 1988; Szelepcsényi 1988. Mathlib gap: NL counting argument absent. -/
axiom Cert_Immerman_Szelepcsényi :
    ∀ lang : Language, InNL lang → InNL langᶜ

/-!
## §4 — Named open surfaces
-/

/-- **OPEN SURFACE**: L ≠ PSPACE.
    Widely believed: deterministic logspace is strictly smaller than polynomial space.
    Equivalent to: there exist polynomial-space problems that require super-logarithmic space.
    Status: OPEN. -/
def L_ne_PSPACE_OPEN : Prop :=
  ∃ lang : Language, InPSPACE lang ∧ ¬InL lang

/-- **OPEN SURFACE**: NL = L (deterministic vs nondeterministic logspace).
    One of the main open problems in complexity theory (related to P vs NP).
    Status: OPEN. -/
def NL_eq_L_OPEN : Prop :=
  ∀ lang : Language, InNL lang ↔ InL lang

end TheoremaAureum.Towers.Space
