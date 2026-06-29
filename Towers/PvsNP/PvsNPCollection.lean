/-
================================================================
Towers/PvsNP/PvsNPCollection.lean — Index / Collection

P vs NP Clay Tower — All Phases
Morning Star Project · Theorema Aureum 143

Imports and re-exports all P vs NP tower phases.
This is the single entry point for the full tower.

Phase summary:
  Phase 1 (Complexity.lean)          — 14 proved + 2 structural cert axioms
  Phase 2 (Hierarchy.lean)           — 8 proved + 5 hierarchy cert axioms
  Phase 3 (CircuitComplexity.lean)   — 6 proved + 4 circuit cert axioms
  Phase 4 (Barriers.lean)            — 5 proved + 3 barrier cert axioms
  Phase 5 (ClayStatement.lean)       — 8 proved + 4 clay cert axioms
  Phase 6 (PolynomialHierarchy.lean) — 10 proved + 5 PH cert axioms (+2 cert→genuine Phase3)
  Phase 7 (DescriptiveComplexity)    — 9 proved + 6 descriptive cert axioms
  Phase 8 (KarpLipton.lean)          — 8 proved + 2 cert axioms
  Phase 9 (CountingComplexity.lean)  — 6 proved + 5 cert axioms (#P, PP, Toda)
  Phase 10 (FaginFragment.lean)      — 5 proved + 2 cert axioms (3-COLOR ∃SO witness)
  Phase 11 (ImmermanVardi.lean)      — 6 proved + 1 cert axiom (LFP Knaster-Tarski)
  Certificate (PvsNPCertificate)     — PNP_CLAY_CERTIFICATE

Total proved bricks: ~72 PvsNP (classical trio, 0 sorry)
Total cert axioms: ~35

Clay status: P ≠ NP LOCKED OPEN. No Clay claim.
================================================================
-/

import Towers.PvsNP.Complexity
import Towers.PvsNP.Hierarchy
import Towers.PvsNP.CircuitComplexity
import Towers.PvsNP.Barriers
import Towers.PvsNP.ClayStatement
import Towers.PvsNP.PolynomialHierarchy
import Towers.PvsNP.DescriptiveComplexity
import Towers.PvsNP.KarpLipton
import Towers.PvsNP.CountingComplexity
import Towers.PvsNP.FaginFragment
import Towers.PvsNP.ImmermanVardi

open TheoremaAureum.Towers.PvsNP.Complexity
open TheoremaAureum.Towers.PvsNP.Hierarchy
open TheoremaAureum.Towers.PvsNP.Circuits
open TheoremaAureum.Towers.PvsNP.Barriers
open TheoremaAureum.Towers.PvsNP.ClayStatement

namespace TheoremaAureum.Towers.PvsNP.Collection

-- ================================================================
-- §1  Re-export key theorems (CLAY_VALID)
-- ================================================================

/-- P ⊆ NP — the fundamental complexity inclusion -/
theorem col_P_subset_NP {L : Language} (h : InP L) : InNP L :=
  P_subset_NP h

/-- P is closed under complement -/
theorem col_InP_comp {L : Language} (h : InP L) : InP (L.comp) :=
  InP_comp h

/-- P is closed under union -/
theorem col_InP_union {L1 L2 : Language} (h1 : InP L1) (h2 : InP L2) :
    InP (L1 ∪ L2) := InP_union h1 h2

/-- P is closed under intersection -/
theorem col_InP_inter {L1 L2 : Language} (h1 : InP L1) (h2 : InP L2) :
    InP (L1 ∩ L2) := InP_inter h1 h2

/-- PneNP ↔ ∃ L ∈ NP \ P -/
theorem col_PneNP_iff : PneNP ↔ ∃ L : Language, InNP L ∧ ¬InP L :=
  PneNP_iff

/-- Both oracle worlds coexist — relativization barrier -/
theorem col_oracle_barrier :
    (∃ A : Oracle, RelativePeqNP A) ∧ (∃ B : Oracle, ¬RelativePeqNP B) :=
  barrier_relativization_consistency

/-- The Clay certificate (conditional on open conjecture) -/
theorem col_PNP_CLAY_CERTIFICATE : PNP_ClayStatement :=
  PNP_CLAY_CERTIFICATE

-- ================================================================
-- §2  Tower summary metadata
-- ================================================================

def tower_name : String := "P vs NP Clay Tower (Morning Star / Theorema Aureum 143)"

def tower_repo : String := "DavidFox998/p-vs-np"

def tower_mathlib : String := "v4.12.0"

def tower_phases : List String := [
  "Phase 1: Complexity.lean — BStr, Language, InP, InNP, P⊆NP, structural closure",
  "Phase 2: Hierarchy.lean — time hierarchy, padding, P≠EXP",
  "Phase 3: CircuitComplexity.lean — Boolean circuits, Shannon bound, Cook-Levin",
  "Phase 4: Barriers.lean — relativization, natural proofs, algebrization",
  "Phase 5: ClayStatement.lean — clay combinator, cert axioms, PNP_CLAY_CERTIFICATE",
  "Certificate: PvsNPCertificate.lean — formal audit of full tower"
]

def tower_proved_brick_count : ℕ := 41

def tower_clay_status : String :=
  "LOCKED OPEN — P vs NP is an unsolved Clay Millennium Prize Problem. " ++
  "PNP_CLAY_CERTIFICATE is CONDITIONAL on Cert_PNP_Separation (the Clay conjecture itself). " ++
  "NS Surface #3 LOCKED OPEN."

/-- HONEST SCOPE: Unlike NS cert axioms (proved results with Mathlib gaps),
    Cert_PNP_Separation is the Clay conjecture itself — NOT proved.
    This tower's certificate has a fundamentally different character:
    it formalizes the STRUCTURE of the problem, not a conditional closure
    of proved-but-unformalized mathematical content. -/
def honest_scope_declaration : String :=
  "NS cert axioms = proved results (Rellich-Kondrachov, BKM, etc.) needing Mathlib. " ++
  "PNP cert axioms = 14 proved + 4 OPEN CONJECTURES (including the Clay problem itself). " ++
  "The certificate is structurally valid but does not resolve the mathematical question."

end TheoremaAureum.Towers.PvsNP.Collection
