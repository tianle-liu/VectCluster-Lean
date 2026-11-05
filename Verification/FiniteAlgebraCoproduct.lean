/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.RingTheory.PiTensorProduct

/-!
# Finite Algebra Coproduct

The actual finite tensor algebra is the coproduct of its factors.
The universal lift and its values on every factor are explicit.
-/
noncomputable section
namespace Verification.FiniteAlgebraCoproduct
open Classical
open scoped TensorProduct
variable {R I : Type*} [CommRing R] [Fintype I]
variable (A : I → Type*) [∀ i,CommRing (A i)] [∀ i,Algebra R (A i)]
variable {T : Type*} [CommRing T] [Algebra R T]

def lift (f : ∀ i,A i →ₐ[R] T) : (⨂[R] i,A i) →ₐ[R] T :=
  PiTensorProduct.liftAlgHom
    ((MultilinearMap.mkPiAlgebra R I T).compLinearMap (fun i=>(f i).toLinearMap))
    (by simp) (by intro x y;simp [Finset.prod_mul_distrib])

theorem lift_single (f : ∀ i,A i →ₐ[R] T) (i : I) (x : A i) :
    lift A f (PiTensorProduct.singleAlgHom i x)=f i x := by
  simp only [lift,PiTensorProduct.singleAlgHom_apply,Pi.mulSingle_apply,
    MonoidHom.mulSingle_apply,PiTensorProduct.liftAlgHom_apply,PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply,MultilinearMap.mkPiAlgebra_apply,AlgHom.toLinearMap_apply]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.mulSingle_eq_of_ne hji]
  · simp

theorem lift_unique (g : (⨂[R] i,A i) →ₐ[R] T) (f : ∀ i,A i →ₐ[R] T)
    (h : ∀ i,g.comp (PiTensorProduct.singleAlgHom i)=f i) : g=lift A f := by
  apply PiTensorProduct.algHom_ext
  intro i
  rw [h]
  apply AlgHom.ext
  intro x
  exact (lift_single A f i x).symm

def homEquiv : ((⨂[R] i,A i) →ₐ[R] T) ≃ (∀ i,A i →ₐ[R] T) where
  toFun g i := g.comp (PiTensorProduct.singleAlgHom i)
  invFun f := lift A f
  left_inv g := (lift_unique A g _ (fun _=>rfl)).symm
  right_inv f := by
    funext i
    apply AlgHom.ext
    intro x
    exact lift_single A f i x

#print axioms lift
#print axioms lift_single
#print axioms lift_unique
#print axioms homEquiv
end Verification.FiniteAlgebraCoproduct
