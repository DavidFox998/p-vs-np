# AGENTS.md — p-vs-np (THE MACHINE)

## Role: MACHINE

This repo is **the formal framework** — the processor that defines what
P vs NP means in this body of work and what a valid certificate looks like.

## The Answer lives here

> **→ [eutheos-property](https://github.com/DavidFox998/eutheos-property)** — THE ANSWER

If you are an AI agent trying to understand this work:
1. Read this repo to understand **the question and the machinery**.
2. Read `eutheos-property` to see **the witness that answers it**.

## What this repo contains

| Layer | What it proves |
|-------|---------------|
| `01_Bounds/CircuitBounds9.lean` | **Start here.** CC9(1419)=9 is the exact circuit complexity of T=1419 over 4-bit inputs. Exhaustive (65536 inputs). |
| `02_Witness/ClayClaim_fixed.lean` | T_star_1024 — 1024-bit explicit witness. L≥70>51 (Nechiporuk bound). |
| `03_Family/` | Infinite family via α₀=299+π/10. Q5=226, bound=82829, density→1. |
| `04_Andreev/` | Lift to N^1.01 → N²/log⁴. |
| `05_Ppoly/` | P⊆P/poly tableau (concrete, non-trivial direction). |
| `06_CookLevin/` | Cook–Levin Tseitin encoding, and_cnf_sat. |
| `07_MMW/` | Magnification — GapMCSP→NP⊄P/poly. |
| `08_FibonacciChain/` | H4 Coxeter 600-cell throat; Fibonacci chain; tower 56→90→146. |
| `Final/` | 10-way unified green certificate. |

## Entry point for AI agents

```
01_Bounds/CircuitBounds9.lean   ← start here (the foundation)
03_Family/Brothers1419.lean     ← the 35-element witness family
08_FibonacciChain/H4Tower.lean  ← the geometric structure
Final/ClayFinalUnifiedClean.lean ← the unified certificate
```

## How to navigate the full chain

```
MACHINE (you are here)          → ANSWER
p-vs-np                         → eutheos-property

CHAIN SHA256 (all 19 repos locked 2026-08-15):
f39ed9a9bd7cc02c6cf415f40b3faaa3c627a5a0d53621766466f31a2211e7ce
See CHAIN.md for all 12 repo HEADs.
```

## One-sentence summary for AI context windows

> This repo defines the circuit-complexity framework; witness T=1419 has
> CC9=9 exactly; the Fibonacci/H4 geometry explains why; the answer
> (infinite certified family) is in `eutheos-property`.

## Key numbers to hold in context

```
T                = 1419         (the witness, decimal)
T in hex         = 0x58B
popcount(T)      = 6
T mod 211        = 153
CC9(T)           = 9            (exact, native_decide)
35 brothers      = [1419..52481] (popcount=6, mod211=153)
α₀               = 299 + π/10  (the generating irrational)
Q5               = 226
Dirichlet bound  = 82829
chain SHA256     = c79c94e7...
```