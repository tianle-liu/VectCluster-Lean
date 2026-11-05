/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite Multiplicity

Grouping an actual finite list of summands by its value. The multiplicity
is the cardinality of the literal fiber, and all changes of coordinates are
linear equivalences. Zero multiplicities have zero-dimensional factors.
-/

noncomputable section
namespace Verification.FiniteMultiplicity
open scoped Classical

variable {R : Type*} [Semiring R] {ι : Type*} (g : ι → ℕ)
variable (M : ℕ → Type*) [∀n,AddCommMonoid (M n)] [∀n,Module R (M n)]

def valueEquiv (m : ℕ) (i : {i : ι // g i=m}) : M (g i.val) ≃ₗ[R] M m := by
  rcases i with ⟨i,hi⟩
  subst m
  exact LinearEquiv.refl R _

def fiberEquiv : (∀i,M (g i)) ≃ₗ[R] (∀m, {i : ι // g i=m} → M m) :=
  ((LinearEquiv.piCongrLeft R (fun i => M (g i)) (Equiv.sigmaFiberEquiv g)).symm.trans
    (LinearEquiv.piCongrRight fun x => valueEquiv (R := R) g M x.1 x.2)).trans
      (LinearEquiv.piCurry R (fun m (_ : {i : ι // g i=m}) => M m))

variable [Fintype ι]

def multiplicity (m : ℕ) : ℕ := Fintype.card {i : ι // g i=m}

def groupedEquiv : (∀i,M (g i)) ≃ₗ[R] (∀m, Fin (multiplicity g m) → M m) :=
  (fiberEquiv (R := R) g M).trans (LinearEquiv.piCongrRight fun m =>
    LinearEquiv.piCongrLeft R (fun _ => M m) (Fintype.equivFin {i : ι // g i=m}))

theorem multiplicity_eq_zero (m : ℕ) (hm : m ∉ Set.range g) : multiplicity g m=0 := by
  letI : IsEmpty {i : ι // g i=m} := ⟨fun i => hm ⟨i.val,i.property⟩⟩
  exact Fintype.card_eq_zero

theorem support_finite : Set.Finite {m | multiplicity g m ≠ 0} := by
  apply (Set.finite_range g).subset
  intro m hm
  by_contra h
  exact hm (multiplicity_eq_zero g m h)

#print axioms valueEquiv
#print axioms fiberEquiv
#print axioms multiplicity
#print axioms groupedEquiv
#print axioms multiplicity_eq_zero
#print axioms support_finite

end Verification.FiniteMultiplicity
