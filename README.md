# Density-Theorem
Formalising Yoneda's Lemma and the Density Theorem in Lean 4

This repository contains a Lean 4 project that formalizes key results in category theory:

- Yoneda’s Lemma (fully faithfulness of the Yoneda embedding)
- The Density Theorem (every sheaf is a colimit of representables)

It builds on Lean 4’s Mathlib library, importing various modules from `CategoryTheory` and related areas.

## Main Content

1. Yoneda Lemma  
   - We define the Yoneda embedding y from C^{op} to Fun(C,Sets).
   - We prove it is fully faithful via a bijection between Hom(B,A) and Hom(Hom(B,_),Hom(A,_)).
   - See definitions and proofs in `Project 3.lean` under sections labeled `Hom_Functor`, `y`, `Yoneda_bij`, and so on.

2. Density Theorem  
   - We show that any functor P from C to Sets is the colimit of y composed with A, for some A.
   - The formal statement is given through a cocone and `IsColimit`, culminating in `ColimitPφ`.

Throughout the code, we rely on Lean’s typeclass mechanisms for category theory (`[Category C]`), natural transformations, `Full` and `Faithful` typeclasses, etc.

## Prerequisites

- Lean 4  
  This project requires Lean 4.  
- Mathlib4  
  The standard math library for Lean 4.
