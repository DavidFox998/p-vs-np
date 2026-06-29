/-
================================================================
Towers/ZFC/ZFCCollection.lean — Index / Collection

ZFC Independence Tower — Set-Theoretic Framework
Morning Star Project · Theorema Aureum 143

Entry point for the ZFC independence sub-tower.
Namespace: TheoremaAureum.Towers.ZFC

Tower summary:
  IndependenceFramework.lean — 8 bricks: independence concept, ZFC axioms,
                               Gödel L model, Cohen forcing scaffolds

Key honest distinctions:
  - "INDEPENDENT" ≠ "OPEN": independence means NEITHER provable NOR refutable
  - CH, AC (in ZF), GCH, V=L are all INDEPENDENT of ZFC
  - Clay Prize problems (P≠NP, NS, BSD, YM, RH) are OPEN (unknown truth value)
  - ZFC consistency (Con(ZFC)) is OPEN within ZFC (Gödel incompleteness)

All three regimes:
  PROVED:      classical trio, 0 sorry  (Lean formal proofs)
  OPEN:        P≠NP, RH, etc.          (unknown truth value in standard math)
  INDEPENDENT: CH, GCH, V=L, Suslin    (true in some models, false in others)

Status: Framework COMPLETE. 0 sorry. 0 sorryAx.
================================================================
-/

import Towers.ZFC.IndependenceFramework

open TheoremaAureum.Towers.ZFC

namespace TheoremaAureum.Towers.ZFC.Collection

-- ================================================================
-- §1  Re-export key theorems
-- ================================================================

/-- Independence is symmetric: P independent ↔ ¬P independent -/
theorem col_independence_symmetric {P : Prop} :
    ZFCIndependent P ↔ ZFCIndependent (¬P) :=
  independence_symmetric

/-- Independence precludes decidability -/
theorem col_independent_not_decidable {P : Prop} (h : ZFCIndependent P) :
    ¬ZFCDecidable P :=
  independent_not_decidable h

/-- Every Prop is either independent or ZFC-decidable -/
theorem col_independence_exhaustive (P : Prop) :
    ZFCIndependent P ∨ ZFCDecidable P :=
  independence_or_decidable_exhaustive P

/-- ZFC has exactly 9 axiom schemas -/
theorem col_zfc_axiom_count : ZFC_Axiom_Names.length = 9 :=
  ZFC_has_nine_axioms

-- ================================================================
-- §2  The three regimes (formal classification)
-- ================================================================

/-- Classification of a mathematical statement's status. -/
inductive StatementStatus where
  | Proved     : StatementStatus  -- ZFC provable (or Lean-provable from classical trio)
  | Open       : StatementStatus  -- unknown truth value; one of: true, false, independent
  | Independent : StatementStatus -- independent of ZFC (consistent in both directions)
  deriving Repr

/-- The Continuum Hypothesis is independent of ZFC. -/
def CH_status : StatementStatus := .Independent

/-- P ≠ NP is open (unknown truth value in standard mathematics). -/
def PvsNP_status : StatementStatus := .Open

/-- The Riemann Hypothesis is open. -/
def RH_status : StatementStatus := .Open

/-- P ⊆ NP is proved (in this tower). -/
def P_subset_NP_status : StatementStatus := .Proved

-- ================================================================
-- §3  Tower metadata
-- ================================================================

def tower_name : String := "ZFC Independence Tower (Morning Star / Theorema Aureum 143)"
def tower_repo : String := "DavidFox998/p-vs-np"

def major_independent_statements : List String := [
  "CH  (2^ℵ₀ = ℵ₁)                — Gödel 1938 + Cohen 1963",
  "GCH (∀n, 2^ℵₙ = ℵₙ₊₁)          — Gödel 1938 + Cohen 1963",
  "V=L (Axiom of Constructibility) — Gödel 1938 (consistent); forcing (inconsistent with MM)",
  "SH  (Suslin's Hypothesis)       — Solovay-Tennenbaum 1971",
  "MA  (Martin's Axiom)            — Martin-Solovay 1970",
  "AC  (in ZF without C)           — Cohen 1963 + Fraenkel-Mostowski"
]

def zfc_brick_count : ℕ := 8

end TheoremaAureum.Towers.ZFC.Collection
