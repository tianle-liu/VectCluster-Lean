/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.DiagonalPowerFibers
import Verification.FiniteTensorFree
import Mathlib.RingTheory.Flat.Basic

/-!
# Power Tensor Product

The actual simultaneous monic power quotient is the finite tensor
product of its one-variable quotients. In particular it is free and flat
over every commutative base ring, without a tameness assumption.
-/
noncomputable section
universe u
namespace Verification.PowerTensorProduct
open Verification.DiagonalPowerFibers
open scoped TensorProduct
variable {R I : Type u} [CommRing R] [Fintype I] [DecidableEq I]
variable (e : I → ℕ) (b : I → Rˣ)

abbrev Factors (i : I) := Verification.SmoothPowerChart.PowerAlgebra R (e i) (b i)
abbrev TensorAlgebra := ⨂[R] i, Factors e b i

def fromTensor : TensorAlgebra e b →ₐ[R] PowerAlgebra e b :=
  PiTensorProduct.liftAlgHom
    ((MultilinearMap.mkPiAlgebra R I (PowerAlgebra e b)).compLinearMap
      (fun i => (factorMap e b i).toLinearMap))
    (by simp) (by intro x y; simp [Finset.prod_mul_distrib])

theorem fromTensor_single (i : I) (x : Factors e b i) :
    fromTensor e b (PiTensorProduct.singleAlgHom i x) = factorMap e b i x := by
  simp only [fromTensor, PiTensorProduct.singleAlgHom_apply,
    Pi.mulSingle_apply, Finset.prod_ite_eq', MonoidHom.mulSingle_apply]
  simp only [PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    AlgHom.toLinearMap_apply]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.mulSingle_eq_of_ne hji]
  · simp

def tensorRoot (i : I) : TensorAlgebra e b :=
  PiTensorProduct.singleAlgHom i (Verification.SmoothPowerChart.root R (e i) (b i))

omit [Fintype I] in
theorem tensorRoot_power (i : I) :
    tensorRoot e b i ^ e i = algebraMap R (TensorAlgebra e b) (b i : R) := by
  change (PiTensorProduct.singleAlgHom (R := R) (A := Factors e b) i)
    (Verification.SmoothPowerChart.root R (e i) (b i)) ^ e i = _
  rw [← map_pow, Verification.SmoothPowerChart.root_power, AlgHom.commutes]

def toTensor : PowerAlgebra e b →ₐ[R] TensorAlgebra e b :=
  lift e b (tensorRoot e b) (tensorRoot_power e b)

omit [Fintype I] in
theorem toTensor_coordinate (i : I) : toTensor e b (coordinate e b i) = tensorRoot e b i :=
  lift_coordinate e b _ _ i

theorem fromTensor_toTensor : (fromTensor e b).comp (toTensor e b) = AlgHom.id R _ := by
  apply hom_ext
  intro i
  rw [AlgHom.comp_apply, toTensor_coordinate]
  exact (fromTensor_single e b i _).trans (factorMap_root e b i)

theorem toTensor_fromTensor : (toTensor e b).comp (fromTensor e b) = AlgHom.id R _ := by
  apply PiTensorProduct.algHom_ext
  intro i
  apply AdjoinRoot.algHom_ext
  change toTensor e b (fromTensor e b (PiTensorProduct.singleAlgHom i
    (Verification.SmoothPowerChart.root R (e i) (b i)))) = _
  rw [fromTensor_single, factorMap_root, toTensor_coordinate]
  rfl

def tensorEquiv : TensorAlgebra e b ≃ₐ[R] PowerAlgebra e b :=
  AlgEquiv.ofAlgHom (fromTensor e b) (toTensor e b)
    (fromTensor_toTensor e b) (toTensor_fromTensor e b)

theorem power_free (he : ∀ i, 0 < e i) : Module.Free R (PowerAlgebra e b) := by
  letI : ∀ i, Module.Free R (Factors e b i) := fun i =>
    Verification.SmoothPowerChart.power_free R (e i) (b i) (he i)
  letI := Verification.FiniteTensorFree.finite_tensor_free R I (Factors e b)
  exact Module.Free.of_equiv (tensorEquiv e b).toLinearEquiv

theorem power_flat (he : ∀ i, 0 < e i) : Module.Flat R (PowerAlgebra e b) := by
  letI := power_free e b he
  infer_instance

#print axioms Factors
#print axioms TensorAlgebra
#print axioms fromTensor
#print axioms fromTensor_single
#print axioms tensorRoot
#print axioms tensorRoot_power
#print axioms toTensor
#print axioms toTensor_coordinate
#print axioms fromTensor_toTensor
#print axioms toTensor_fromTensor
#print axioms tensorEquiv
#print axioms power_free
#print axioms power_flat
end Verification.PowerTensorProduct
