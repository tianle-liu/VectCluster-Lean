/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteAlgebraSplit
import Mathlib.RingTheory.Smooth.Basic

/-!
# Finite Algebra Smooth

Smoothness of the actual finite tensor algebra, proved by its recursive
algebra isomorphism and ordinary stability of smooth algebras under base change.
-/
noncomputable section
namespace Verification.FiniteAlgebraSmooth
open scoped TensorProduct
variable (R : Type) [CommRing R]

theorem self : Algebra.Smooth R R := by
  refine ⟨?_,inferInstance⟩
  constructor
  intro C _ _ I _ f
  refine ⟨Algebra.ofId R C, ?_⟩
  apply AlgHom.ext
  intro r
  exact (AlgHom.commutes f r).symm

theorem tensor (S T : Type) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra.Smooth R S] [Algebra.Smooth R T] : Algebra.Smooth R (S⊗[R] T) :=
  Algebra.Smooth.comp R S (S⊗[R] T)

theorem finite : ∀ (n : ℕ) (S : Fin n→Type) [∀ i,CommRing (S i)] [∀ i,Algebra R (S i)]
    [∀ i,Algebra.Smooth R (S i)], Algebra.Smooth R (⨂[R] i,S i) := by
  intro n
  induction n with
  | zero =>
    intro S _ _ _
    letI : Algebra.Smooth R R := self R
    exact Algebra.Smooth.of_equiv (FiniteAlgebraSplit.empty R S).symm
  | succ n ih =>
    intro S _ _ _
    letI : Algebra.Smooth R (⨂[R] i : Fin n,S i.succ) := ih (fun i=>S i.succ)
    letI : Algebra.Smooth R (S 0⊗[R] (⨂[R] i : Fin n,S i.succ)) := tensor R _ _
    exact Algebra.Smooth.of_equiv (FiniteAlgebraSplit.equiv R S).symm

#print axioms self
#print axioms tensor
#print axioms finite
end Verification.FiniteAlgebraSmooth
