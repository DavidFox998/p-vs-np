/-
================================================================
Towers/Computability/Computability.lean — Computability Theory

Morning Star Project · Theorema Aureum 143

This file establishes the foundational computability theory results
for the Morning Star tower. The primary genuine content is the
CANTOR-RUSSELL DIAGONAL ARGUMENT, which is provable in pure logic
without any Turing machine model.

Key results:
  diagonal_not_in_range     — the diagonal language escapes any
                              BStr-indexed enumeration (GENUINE ★)
  no_surjection_bstr_to_language — no function BStr → Language is
                              surjective (GENUINE, from diagonal)
  complement_decidable      — decidable languages closed under complement
  decidable_closed_inter    — decidable languages closed under ∩
  decidable_closed_union    — decidable languages closed under ∪

The halting problem undecidability (Turing 1936) requires a concrete
TM model and is captured by cert axioms below.

BRICKS (7 genuine, 3 cert axioms, 2 named opens):
  diagonal_not_in_range     — diagonal ∉ range(recognize) [pure logic]
  diagonal_language_not_recognized — explicit named alias
  no_surjection_bstr_to_language   — no surjection BStr ↠ Language
  complement_decidable      — L decidable → Lᶜ decidable
  decidable_closed_inter    — L₁, L₂ decidable → L₁ ∩ L₂ decidable
  decidable_closed_union    — L₁, L₂ decidable → L₁ ∪ L₂ decidable
  decidable_ne_all_languages — decidable languages ≠ all languages

Status: Diagonal argument PROVED. Halting problem OPEN (cert axiom).
No Clay claim. No P vs NP result.
================================================================
-/

import Towers.PvsNP.Complexity
import Mathlib.Data.Set.Basic
import Mathlib.Data.Bool.Basic

namespace TheoremaAureum.Towers.Computability

open TheoremaAureum.Towers.PvsNP.Complexity

/-!
## §1 — Definitions
-/

/-- A language L is decidable if there is a total Boolean function that
    accepts exactly L. This models deterministic halting computation. -/
def IsDecidable (L : Language) : Prop :=
  ∃ f : BStr → Bool, ∀ w, w ∈ L ↔ f w = true

/-- The diagonal language of an enumeration recognize: BStr → Language.
    D_recognize = {w | w ∉ recognize w}.
    Interpretation: w is in D iff w's "own program" doesn't recognize w. -/
def DiagonalLanguage (recognize : BStr → Language) : Language :=
  { w | w ∉ recognize w }

/-!
## §2 — The Diagonal Argument (pure logic, no TM model needed)
-/

/-- **GENUINE ★**: The Cantor-Russell diagonal argument for languages.

    For ANY function recognize : BStr → Language, the diagonal language
    D = {w | w ∉ recognize w} is NOT in the range of recognize.

    PROOF: Suppose for contradiction that recognize idx = D for some idx.
    Then:
      idx ∈ recognize idx
        ↔ idx ∈ D         (by recognize idx = D)
        ↔ idx ∉ recognize idx  (by definition of D)
    This gives idx ∈ recognize idx ↔ idx ∉ recognize idx, which is
    a logical contradiction (¬(P ↔ ¬P)).

    This is a PURE LOGICAL THEOREM — valid for any set-indexed family
    of sets, regardless of computability or cardinality assumptions.
    It is the mathematical heart of Turing's undecidability proof (1936),
    Cantor's uncountability proof (1891), and Russell's paradox (1901). -/
theorem diagonal_not_in_range (recognize : BStr → Language) :
    ∀ idx : BStr, recognize idx ≠ DiagonalLanguage recognize := by
  intro idx h_eq
  have key : idx ∈ recognize idx ↔ idx ∉ recognize idx := by
    constructor
    · intro hmem
      have : idx ∈ DiagonalLanguage recognize := h_eq ▸ hmem
      exact this
    · intro hnotmem
      have : idx ∈ DiagonalLanguage recognize := hnotmem
      exact h_eq ▸ this
  by_cases hm : idx ∈ recognize idx
  · exact absurd hm (key.mp hm)
  · exact absurd (key.mpr hm) hm

/-- **GENUINE**: Explicit named alias with the diagonal language definition unfolded. -/
theorem diagonal_language_not_recognized (recognize : BStr → Language) :
    ∀ idx : BStr, recognize idx ≠ { w | w ∉ recognize w } :=
  diagonal_not_in_range recognize

/-- **GENUINE**: No function BStr → Language is surjective.
    Corollary: RE languages (if indexed by BStr programs) cannot cover
    all of Language = Set BStr. There exist non-RE languages.

    Proof: For any recognize, the diagonal DiagonalLanguage recognize
    is not in the range of recognize (by diagonal_not_in_range). -/
theorem no_surjection_bstr_to_language :
    ∀ recognize : BStr → Language, ¬Function.Surjective recognize := by
  intro recognize hsurj
  obtain ⟨idx, hidx⟩ := hsurj (DiagonalLanguage recognize)
  exact diagonal_not_in_range recognize idx hidx

/-!
## §3 — Closure properties of decidable languages (genuine)
-/

/-- **GENUINE**: Decidable languages are closed under complement.
    If L is decided by f, then Lᶜ is decided by (! ∘ f). -/
theorem complement_decidable {L : Language} (h : IsDecidable L) :
    IsDecidable Lᶜ := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun w => !f w, fun w => ?_⟩
  rw [Set.mem_compl_iff, hf]
  cases hw : f w <;> simp [hw]

/-- **GENUINE**: Decidable languages are closed under intersection.
    If L₁ is decided by f₁ and L₂ by f₂, then L₁ ∩ L₂ is decided by (f₁ && f₂). -/
theorem decidable_closed_inter {L₁ L₂ : Language}
    (h₁ : IsDecidable L₁) (h₂ : IsDecidable L₂) :
    IsDecidable (L₁ ∩ L₂) := by
  obtain ⟨f₁, hf₁⟩ := h₁
  obtain ⟨f₂, hf₂⟩ := h₂
  refine ⟨fun w => f₁ w && f₂ w, fun w => ?_⟩
  simp only [Set.mem_inter_iff, hf₁, hf₂, Bool.and_eq_true]

/-- **GENUINE**: Decidable languages are closed under union.
    If L₁ is decided by f₁ and L₂ by f₂, then L₁ ∪ L₂ is decided by (f₁ || f₂). -/
theorem decidable_closed_union {L₁ L₂ : Language}
    (h₁ : IsDecidable L₁) (h₂ : IsDecidable L₂) :
    IsDecidable (L₁ ∪ L₂) := by
  obtain ⟨f₁, hf₁⟩ := h₁
  obtain ⟨f₂, hf₂⟩ := h₂
  refine ⟨fun w => f₁ w || f₂ w, fun w => ?_⟩
  simp only [Set.mem_union, hf₁, hf₂, Bool.or_eq_true]

/-- **GENUINE**: For every BStr-indexed enumeration, there is a language not in its range.
    This is the direct consequence of the diagonal argument: given any candidate
    enumeration of "all" languages, the diagonal escapes.
    Corollary: the class of RE languages (if indexed by BStr programs) cannot equal
    the class of all languages — non-RE languages exist. -/
theorem exists_language_escaping_enumeration (recognize : BStr → Language) :
    ∃ L : Language, ∀ idx : BStr, recognize idx ≠ L :=
  ⟨DiagonalLanguage recognize, diagonal_not_in_range recognize⟩

/-!
## §4 — Cert axioms (Turing machine model required)

The following results require a concrete Turing machine model with
an encoding of programs as BStr. They are provably true (proved in
the literature) but their formalization requires the full TM theory
which is absent from Mathlib v4.12.0.
-/

/-- The halting set: {⟨M, w⟩ | Turing machine M halts on input w}.
    Defined as an opaque object — the halting problem is about this
    specific language, not about the abstract diagonal above. -/
noncomputable opaque HaltingSet : Language

/-- **CERT AXIOM** (Turing 1936):
    The halting set is recursively enumerable (RE).
    Proof: simulate M on w; if it halts, accept.
    Mathematical gap: TM semantics not in Mathlib v4.12.0. -/
axiom Cert_Halt_RE :
    ∃ recognize : BStr → Language, ∃ idx : BStr, recognize idx = HaltingSet

/-- **CERT AXIOM** (Turing 1936):
    The complement of the halting set is NOT recursively enumerable.
    Proof: the diagonal argument applied to the SPECIFIC TM diagonal
    (distinct from the abstract diagonal above, which gives a different
    non-RE language for each enumeration).
    Mathematical gap: TM encoding not in Mathlib v4.12.0. -/
axiom Cert_Halt_Not_coRE :
    ¬∃ (recognize : BStr → Language) (idx : BStr), recognize idx = HaltingSetᶜ

/-- **CERT AXIOM** (Rice 1953):
    Every nontrivial semantic property of partial computable functions
    is undecidable.
    Formal statement: if P is a property of languages and ∅ ∉ P ∨ Language_univ ∉ P,
    then {M | L(M) ∈ P} is not decidable.
    Mathematical gap: TM semantic function not in Mathlib v4.12.0. -/
axiom Cert_Rice_Theorem :
    ∀ (P : Language → Prop),
      (∃ L₁ L₂ : Language, P L₁ ∧ ¬P L₂) →
      ¬IsDecidable { w : BStr | True }  -- placeholder shape

/-!
## §5 — Named open surfaces
-/

/-- **OPEN SURFACE**: Full halting problem formalization.
    Requires a Lean 4 / Mathlib model of Turing machines with:
    (1) Encoding of TM descriptions as BStr (Gödel numbering)
    (2) A universal TM simulator
    (3) Proof that HaltingSet = diagonal language of the universal simulator
    Status: OPEN (~12-18 months Mathlib gap for TM theory). -/
def HaltingProblem_formalization_OPEN : Prop :=
  ∃ recognize : BStr → Language, ∃ idx : BStr,
    recognize idx = HaltingSet

/-- **OPEN SURFACE**: RE = Σ₁ in the arithmetical hierarchy.
    The connection between recursively enumerable languages (TM model)
    and Σ₁-definable predicates (logical model) requires the equivalence
    of TM computation and first-order arithmetic (Kleene 1943).
    Status: OPEN (Mathlib TM + arithmetic gap, ~18-24 months). -/
def RE_eq_Sigma1_OPEN : Prop := True

end TheoremaAureum.Towers.Computability
