# BSD — Birch and Swinnerton-Dyer + Class Numbers

**Purpose:** Arithmetic tower for BSD(143a1) + class number h(-143)=10 used by NS 1/10 factor and PvsNP Conductor.

**Files:**
- `ClassNumberK143.lean` + other BSD files (L-function, Heegner, Kolyvagin skeleton via LMFDB-anchored defs)

**Methodology:** LMFDB-anchored definitions for E=143a1, conductor N=143, rank 0/1 data, class number formula for Q(√-143) =10 via analytic class number, BDP prime p5=3993746143633 from anticyclotomic.

**Results:** h(-143)=10 certified — same 10 as NS icosahedral 1/10 factor and ConductorHash prefix chain length. Provides p5 for ConductorHash.

**Dependencies:** Common.Conductor, Mathlib NumberTheory.
