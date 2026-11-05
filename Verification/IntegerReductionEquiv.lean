/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IntegerLinearReduction
import Mathlib.LinearAlgebra.Finsupp.SumProd
import Mathlib.LinearAlgebra.Pi

/-!
# Integer Reduction Equiv

Reducing an actual integral lattice isomorphism modulo two retains
its inverse and its specified column splitting.
-/
noncomputable section
namespace Verification.IntegerReductionEquiv
open Verification.IntegerLinearReduction
variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

def equiv (e : (ι →₀ ℤ) ≃ₗ[ℤ] (κ →₀ ℤ)) : (ι → ZMod 2) ≃ₗ[ZMod 2] (κ → ZMod 2) :=
  LinearEquiv.ofLinear (reduce e.toLinearMap) (reduce e.symm.toLinearMap)
    (by rw [← reduce_comp,show e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id from by ext; simp,reduce_id])
    (by rw [← reduce_comp,show e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id from by ext; simp,reduce_id])

theorem apply_cast (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ)) (x : ι →₀ ℤ) :
    reduce f (fun i => (x i : ZMod 2)) = fun k => (f x k : ZMod 2) := by
  classical
  funext k
  rw [reduce_apply]
  calc
    _ = ∑ i, ((f (Finsupp.single i (x i)) k : ℤ) : ZMod 2) := by
      apply Finset.sum_congr rfl
      intro i _
      have h : Finsupp.single i (x i) = x i • Finsupp.single i (1 : ℤ) := by simp
      rw [h,map_smul,Finsupp.smul_apply,smul_eq_mul,Int.cast_mul,mul_comm]
    _ = ((f (∑ i, Finsupp.single i (x i)) k : ℤ) : ZMod 2) := by
      rw [map_sum,Finsupp.finset_sum_apply,Int.cast_sum]
    _ = _ := by rw [Finsupp.univ_sum_single]

def productEquiv (e : (κ →₀ ℤ) ≃ₗ[ℤ] ((ι →₀ ℤ) × (τ →₀ ℤ))) :
    (κ → ZMod 2) ≃ₗ[ZMod 2] ((ι → ZMod 2) × (τ → ZMod 2)) :=
  (equiv (e.trans (Finsupp.sumFinsuppLEquivProdFinsupp ℤ).symm)).trans
    (LinearEquiv.sumArrowLequivProdArrow ι τ (ZMod 2) (ZMod 2))

theorem productEquiv_cast (e : (κ →₀ ℤ) ≃ₗ[ℤ] ((ι →₀ ℤ) × (τ →₀ ℤ)))
    (x : κ →₀ ℤ) : productEquiv e (fun k => (x k : ZMod 2)) =
      ((fun i => ((e x).1 i : ZMod 2)),fun t => ((e x).2 t : ZMod 2)) := by
  change (LinearEquiv.sumArrowLequivProdArrow ι τ (ZMod 2) (ZMod 2))
    (reduce (e.trans (Finsupp.sumFinsuppLEquivProdFinsupp ℤ).symm).toLinearMap
      (fun k => (x k : ZMod 2))) = _
  rw [apply_cast]
  rfl

theorem productEquiv_column (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ))
    (e : (κ →₀ ℤ) ≃ₗ[ℤ] ((ι →₀ ℤ) × (τ →₀ ℤ)))
    (he : ∀ x, e (f x) = (x,0)) (a : ι → ZMod 2) :
    productEquiv e (reduce f a) = (a,0) := by
  classical
  let x : ι →₀ ℤ := Finsupp.equivFunOnFinite.symm (fun i => (a i).val)
  have hx : (fun i => (x i : ZMod 2)) = a := by
    funext i
    simp [x]
  rw [← hx,apply_cast,productEquiv_cast,he]
  rfl

#print axioms equiv
#print axioms apply_cast
#print axioms productEquiv
#print axioms productEquiv_cast
#print axioms productEquiv_column
end Verification.IntegerReductionEquiv
