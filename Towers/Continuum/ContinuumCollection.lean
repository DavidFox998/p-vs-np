/-
================================================================
Towers/Continuum/ContinuumCollection.lean — Index / Collection

Continuum Tower — Cardinal Arithmetic & Independence
Morning Star Project · Theorema Aureum 143

This is the single entry point for the Continuum sub-tower.
All content lives under namespace TheoremaAureum.Towers.Continuum.

Sub-tower summary:
  CardinalBounds.lean        — 10 bricks: Cantor, König, beth bounds
  ContinuumHypothesis.lean   — 8 bricks: CH/GCH independence framework

Total proved bricks: 18 (classical trio, 0 sorry)
Total cert axioms: 12 (ZFC theorems + independence certificates)

Key honest distinction:
  CardinalBounds = THEOREMS of ZFC (provable, genuine math)
  ContinuumHypothesis = INDEPENDENT of ZFC (Gödel 1938 + Cohen 1963)

Status: Framework COMPLETE. CH INDEPENDENT. No Clay claim. No prize.
================================================================
-/

import Towers.Continuum.CardinalBounds
import Towers.Continuum.ContinuumHypothesis
import Towers.Continuum.KonigTheorem

open TheoremaAureum.Towers.Continuum
open TheoremaAureum.Towers.Continuum.CH

namespace TheoremaAureum.Towers.Continuum.Collection

-- ================================================================
-- §1  Re-export key theorems
-- ================================================================

/-- Cantor's theorem: every set is strictly smaller than its power set -/
theorem col_cantor_strict (α : Type*) : #α < #(Set α) :=
  cantor_strict α

/-- ℵ₀ < 2^ℵ₀ — the continuum is strictly larger than the countable -/
theorem col_aleph_zero_lt_continuum : ℵ₀ < continuum_card :=
  aleph_zero_lt_continuum

/-- The beth numbers are strictly increasing -/
theorem col_beth_strict_mono (n : ℕ) : BethNumber n < BethNumber (n + 1) :=
  beth_strict_mono n

/-- GCH implies CH — the n=0 case -/
theorem col_GCH_implies_CH (hGCH : GeneralizedCH) : ContinuumHypothesis :=
  GCH_implies_CH hGCH

/-- CH implies no intermediate cardinal -/
theorem col_CH_no_intermediate (hCH : ContinuumHypothesis) (κ : Cardinal)
    (h₁ : ℵ₀ < κ) (h₂ : κ < 2 ^ ℵ₀) : False :=
  CH_implies_no_intermediate hCH κ h₁ h₂

-- ================================================================
-- §2  Tower metadata
-- ================================================================

def tower_name : String := "Continuum Tower (Morning Star / Theorema Aureum 143)"
def tower_repo : String := "DavidFox998/p-vs-np"
def tower_mathlib : String := "v4.12.0"

def tower_files : List String := [
  "CardinalBounds.lean    — Cantor, König, beth hierarchy (ZFC theorems)",
  "ContinuumHypothesis.lean — CH/GCH/Suslin/MA independence (Gödel+Cohen)"
]

def tower_independence_note : String :=
  "CH is INDEPENDENT of ZFC (Gödel 1938 + Cohen 1963). " ++
  "This is NOT a Clay Prize problem. " ++
  "The tower formalizes independence structure, not a proof of CH."

def continuum_brick_count : ℕ := 18

end TheoremaAureum.Towers.Continuum.Collection
