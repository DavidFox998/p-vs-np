# Continuum — Cardinal Arithmetic + CH

### Overview
Formalizes cardinal bounds, König's theorem, continuum hypothesis independence scaffolding.

How many real numbers are there? More than integers — Cantor proved. Continuum hypothesis says no size between integers and reals. This tower formalizes sizes of infinite sets and König's theorem that says cofinality prevents certain cardinal exponentiations.

Defines `Cardinal` via `Cardinal.mk`, Beth `ℶ0=ℵ0, ℶ_{α+1}=2^{ℶα}`, `cf κ` cofinality, König's theorem `κ < κ^{cf κ}` for infinite κ, König's inequality `cf(2^κ) > κ`,
