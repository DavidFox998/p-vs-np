# p-vs-np — Morning Star Project

**Status: Reserved — Exploratory Scaffolding Only**

> **No proof exists. No claim is made. This repository is placeholder scaffolding
> for future formal work on the P vs NP problem.**

The P vs NP problem (Clay Millennium Prize Problem #3) asks whether every problem
whose solution can be quickly verified can also be quickly solved.

## Current state

- 0 active bricks.
- No Lean theorems about circuit complexity, oracle separations, or P/NP.
- No computational complexity machinery exists in mathlib v4.12.0 at the level
  needed for a genuine P vs NP contribution.

## Honest scope

Any future work in this repo will be clearly labeled:
- `_OPEN` for unproved propositions
- `_CONDITIONAL` for results requiring undischarged hypotheses
- No `sorry` in any registered brick

## Toolchain

```
leanprover/lean4:v4.12.0
```
