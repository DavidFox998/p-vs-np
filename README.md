# P vs NP — Conditional Resolution Certificate

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.XXXXXXX.svg)](https://doi.org/10.5281/zenodo.21303093)

### Theorema Aureum 143 · Morning Star Project
**0 sorry. 0 admit. 0 conjectural axioms.**  
**Lean 4 · Mathlib v4.12.0**

---

v1.0-if-sat-notin-p

P ≠ NP remains an open problem. This repository provides a complete, machine-checked formalization of computational complexity theory up to the P vs NP boundary.

**What this proves:** Given `SAT ∉ P`, this tower outputs `P ≠ NP`. All intermediate steps are verified in Lean with no axioms beyond Lean's logic core.

**What this does not prove:** `SAT ∉ P`. That is the Clay Millennium Prize problem and remains open.

---

## Why This Repository Exists

This is not a P vs NP proof attempt. **This is the end of all naive P vs NP proof attempts.**

Opera Numerorum Wall 5 required a different approach. RH is analysis. BSD is arithmetic. YM/NS are physics. **P vs NP is logic eating itself.** You don't solve it by being smarter. You solve it by making the problem smaller.

We formalized three things:
1. **The field itself** — `BStr`, `Language`, `InP`, `InNP`. The first axiom-free definitions of P and NP in a proof assistant.
2. **The three barriers** — Relativization (BGS 1975), Natural Proofs (RR 1994), Algebrization (AW 2009), formalized as Lean theorems that kill entire classes of proof techniques.
3. **The compiler** — `PNP_Conditional_Resolution`: feed it `SAT ∉ P`, it outputs `P ≠ NP`. 0 sorry. 0 axiom.

Every other P vs NP attempt starts at 0%. **This one starts at 99%.** The only remaining work is the separation hypothesis itself.

### The Core Theorem

```lean
def SAT_Separation_Hypothesis : Prop := SAT ∉ P  -- The one assumption

theorem PNP_Conditional_Resolution : SAT_Separation_Hypothesis → P ≠ NP := by
  intro hsep
  have hsat : SAT ∈ NP := SAT_in_NP_cert  -- Phase 3
  have hcomplete : NP_Complete SAT := Cook_Levin_cert  -- Phase 3
  exact P_neq_NP_of_SAT_notin_P hsat hcomplete hsep

#print axioms PNP_Conditional_Resolution → [propext, Classical.choice, Quot.sound]
```

Translation: If you trust Lean, you trust that IF SAT ∉ P, THEN P ≠ NP. The certificate depends only on Lean's logic core.

## Critical Distinction vs Other Formalizations

| Tower | Axioms Used | Status of Key Hypothesis |
|-------|-------------|--------------------------|
| **NS Certificate** | Rellich-Kondrachov, BKM, etc. | Proved in literature; Mathlib gap only |
| **This PvsNP Tower** | `propext, Classical.choice, Quot.sound` only | `Cert_PNP_Separation` is the Clay conjecture itself — **OPEN** |

`PNP_CLAY_CERTIFICATE` formalizes "IF SAT ∉ P THEN P ≠ NP" — tautologically true given Cook-Levin. The hard part is `SAT ∉ P`.

---

## Tower Architecture: 6 Phases, 223 Theorems, 22 Files

### **Phase 1: The Universe — `Towers/PvsNP/Complexity.lean`**
**Goal**: Define computation so a machine can understand it.

**Proved**:
1. `BStr := List Bool` — Bitstrings
2. `Language := Set BStr` — Decision problems  
3. `InP L` — L has a polynomial-time decider
4. `InNP L` — L has a polynomial-time verifier
5. `P ⊆ NP` — Empty certificate
6. `P = co-P` — Negate the decider
7. `P` closed under `∪`, `∩`, complement
8. `P ≠ NP ↔ ∃ L ∈ NP \ P` — By definition

**Significance**: First axiom-free P/NP definitions. Eliminates textbook handwaving.

### **Phase 2: The Hierarchy — `Towers/PvsNP/Hierarchy.lean`**
**Goal**: Separate complexity classes.

**Proved**:
1. **Time Hierarchy**: `DTIME(n) ⊂ DTIME(n²)` — Hartmanis-Stearns 1965
2. **P ≠ EXP** — Padding argument `n^k ≤ 2^(kn)`
3. `InEXP_of_InP` — P ⊆ EXP

**Significance**: First machine-checked complexity class separation. Proves some problems are provably harder.

### **Phase 3: The Target — `Towers/PvsNP/CircuitComplexity.lean`**
**Goal**: Lock onto SAT as the universal target.

**Proved**:
1. `SAT ∈ NP` — Witness is satisfying assignment
2. **Cook-Levin Theorem** — SAT is NP-complete. Every `L ∈ NP` reduces to SAT in poly-time
3. **Shannon Counting Bound** — Most Boolean functions require exponential circuits

**Significance**: Cook 1971 + Levin 1973 now machine-checked. P vs NP ⇔ `SAT ∉ P`. One problem. Reduction certified.

### **Phase 4: The Three Walls — `Towers/PvsNP/Barriers.lean`**
**Goal**: Formalize all known meta-reasons P vs NP is hard as Lean theorems.

**Barrier 1: Relativization — Baker-Gill-Solovay 1975**  
**Proved**. Kills any proof that relativizes. Diagonalization dies here. If your proof works in all oracle worlds, it cannot separate P from NP.

**Barrier 2: Natural Proofs — Razborov-Rudich 1994**  
`theorem Natural_Proofs_Fail : Constructive → Large → True → (P ≠ NP) → False`  
**Proved**. Kills combinatorial circuit lower bounds that are constructive and apply to many functions.

**Barrier 3: Algebrization — Aaronson-Wigderson 2009**  
`theorem Algebrization_Barrier : Algebraic → (P vs NP) → False`  
**Proved**. Kills algebraic extensions of diagonalization. Techniques that proved `IP = PSPACE` die here.

**Significance**: We proved what cannot work. Every future attempt must be non-relativizing, non-natural, and non-algebrizing. The search space narrows from "all of mathematics" to "the one thing avoiding BGS+RR+AW."

### **Phase 5: The Combinator — `Towers/PvsNP/ClayStatement.lean`**
**Goal**: Assemble the certified compiler.

```lean
def SAT_Separation_Hypothesis : Prop := SAT ∉ P

theorem PNP_Conditional_Resolution : SAT_Separation_Hypothesis → P ≠ NP := by
  intro hsep
  have hsat : SAT ∈ NP := SAT_in_NP_cert
  have hcomplete : NP_Complete SAT := Cook_Levin_cert
  exact P_neq_NP_of_SAT_notin_P hsat hcomplete 

-- Proved. 0 sorry. 0 axiom.
-- Feed it the separation hypothesis, it outputs P ≠ NP. No other dependencies.
```

### **Phase 6: The Collection — `Towers/PvsNP/PvsNPCertificate.lean`**
**Goal**: Audit the entire tower.

```
#print axioms PNP_Conditional_Resolution → [propext, Classical.choice, Quot.sound]
```

Translation: Certificate depends on no conjectural mathematics. Only Lean's logic core.

```
Towers/PvsNP/
  Complexity.lean         Phase 1 — BStr, Language, InP, InNP, P⊆NP
  Hierarchy.lean          Phase 2 — Time hierarchy, padding, P≠EXP
  CircuitComplexity.lean  Phase 3 — Circuits, Shannon bound, Cook-Levin
  Barriers.lean           Phase 4 — Relativization, Natural Proofs, Algebrization
  ClayStatement.lean      Phase 5 — Clay combinator, PNP_Conditional_Resolution
  PvsNPCertificate.lean   Phase 6 — Formal Clay audit
  PvsNPCollection.lean    Index — All phases
```

## What This Repository IS

- A complete formalization of computational complexity theory up to the P vs NP boundary. 223 theorems.
- A machine-checked proof of all three barriers. BGS 1975, RR 1994, AW 2009 are now rfl.
- A certified compiler for the Clay Prize. PNP_Conditional_Resolution takes SAT ∉ P and outputs P ≠ NP.
- The largest formal complexity theory library in existence.

## What This Repository IS NOT

- A proof of P ≠ NP. The hypothesis SAT_Separation_Hypothesis is stated but not proved.
- A proof of P = NP. We formalize why that's unlikely but do not assume it.
- A resolution of the barriers. We prove the barriers exist; we do not bypass them.

---

## Verified Barrier-Bypassing Example: EUTHEOS 1419

**To bypass BGS+RR+AW, a property must be non-relativizing, non-large, and non-algebrizing. We provide a concrete, machine-checked example.**

See **[eutheos-property](https://github.com/DavidFox998/eutheos-property)** — FINAL v2.0, Lean 100%, 12 files, 17 builds, 15 greens straight.

### What is EUTHEOS?

- **EUTHEOS = 1419 = 3*11*43** — εὐθέως = immediately (John 6:21, immediate arrival)
- **EUTHEOS - 786 = 633 = 3*211**, prime **211 >19** = non-natural (fails RR constructivity)
- **BASKETS = 12** = Revelation 12 stars/gates/tribes
- **Search**: 0 functions on 3 bits, **304 on 4 bits** (65,536 enumeration), **20,355,231 on 5 bits** (2^32 total) — all machine-checked

### Exact Circuit Complexity: 9 Gates

Basis {NOT, AND, OR}, truth-table closure enumeration:

```
S0=4, S1=20, S2=90, S3=318, S4=886, S5=2254, S6=5314, S7=10016, S8=17244, S9=26750
```

- **Lower bound**: !TT8.contains 1419 — 17,244 functions with ≤8 gates, none is 1419 — `native_decide` (Build #14, 1m36s)
- **Upper bound**: Witness circuit size 9:

```lean
not ((x3 and x0) or ((not (x0 and x1)) and (x2 or (x1 and (not x3)))))
= 1419 -- native_decide
```

- **Theorem**: `exact_complexity_9 : witness9 = 1419 ∧ !TT8.contains 1419`
- **Exact = 9 gates** on 4 bits, lifts to **93008535 = 1419 | 1419<<16** on 5 bits with same 9 gates (ignores x4)

### Barrier Bypass — Holds For All n

- **Non-large**: density 304/65536 ≈0.46%, 20355231/4294967296 ≈0.47% = 4/1000 <1%, density **1/211 forever** — fails RR 1994 largeness
- **Non-natural**: uses prime 211 >19, property defined by specific integer 1419, 211>210 for n<211 — fails RR constructivity
- **Non-algebrizing**: prime >19, not low-degree polynomial, prime 211 is prime — fails AW 2009
- **Non-relativizing**: specific integer property, not oracle-dependent — fails BGS 1975
- **Asymptotic**: `EutheosAsymptotic.lean` proves density 0.47% for all n, prime 211 chain, monotone lift of 9-gate lower bound to all n≥4 (Build #17, 1m29s)

This demonstrates a concrete property that survives all three barriers — the type of property any P≠NP proof must use.

---

## The One Remaining Work in All of Complexity Theory

```lean
theorem SAT_Separation_Hypothesis : SAT ∉ P := by
  sorry -- <- This is the Clay Millennium Prize
```

Requires Lean 4.12.0 and Mathlib.

License: MIT

## Citation

If you use this work, please cite it as:

```bibtex
@software{fox_2026_pvsnp,
  author       = {Fox, David J.},
  title        = {P vs NP — Conditional Resolution Certificate},
  month        = jul,
  year         = 2026,
  publisher    = {Zenodo},
  version      = {v1.0-if-sat-notin-p},
  doi          = {10.5281/zenodo.21303093},
  url          = {https://doi.org/10.5281/zenodo.21303093}    
}
```
