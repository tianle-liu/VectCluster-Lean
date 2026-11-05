/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.UniversalExchangeChart
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Local Exchange Tensor

The actual exchange-equation quotient is the base change of the
universal exchange chart along its character algebra map.
-/
noncomputable section
universe u
namespace Verification.LocalExchangeTensor
open MvPolynomial Verification.LocalExchangeSmooth Verification.UniversalExchangeChart
open scoped TensorProduct
variable {R S κ : Type u} [CommRing R] [CommRing S]
variable [Algebra (Target R κ) S]
variable (χ : κ → Sˣ)
variable (hχ : ∀ k, algebraMap (Target R κ) S (DiagonalPowerFibers.laurentCoordinate R κ k) = χ k)
attribute [local instance] MvPolynomial.algebraMvPolynomial

abbrev BaseChange := Universal R κ ⊗[Target R κ] S

def fromUniversal : Universal R κ →ₐ[Target R κ] LocalAlgebra χ :=
  lift (targetUnit R κ) (Algebra.ofId (Target R κ) (LocalAlgebra χ)) (x χ) (y χ) (fun k => by
    rw [equation]
    change algebraMap S (LocalAlgebra χ) (χ k : S) =
      algebraMap (Target R κ) (LocalAlgebra χ) (targetUnit R κ k : Target R κ)
    rw [IsScalarTower.algebraMap_apply (Target R κ) S (LocalAlgebra χ)]
    rw [show (targetUnit R κ k : Target R κ) = DiagonalPowerFibers.laurentCoordinate R κ k from rfl, hχ])

theorem fromUniversal_x (k : κ) : fromUniversal χ hχ (x (targetUnit R κ) k) = x χ k :=
  lift_x _ _ _ _ _ k

theorem fromUniversal_y (k : κ) : fromUniversal χ hχ (y (targetUnit R κ) k) = y χ k :=
  lift_y _ _ _ _ _ k

def fromTensor : BaseChange (R := R) (S := S) (κ := κ) →ₐ[Target R κ] LocalAlgebra χ :=
  Algebra.TensorProduct.lift (fromUniversal χ hχ)
    (IsScalarTower.toAlgHom (Target R κ) S (LocalAlgebra χ)) (fun _ _ => Commute.all _ _)

def toTensor : LocalAlgebra χ →ₐ[Target R κ] BaseChange (R := R) (S := S) (κ := κ) :=
  lift χ Algebra.TensorProduct.includeRight
    (fun k => Algebra.TensorProduct.includeLeft (x (targetUnit R κ) k))
    (fun k => Algebra.TensorProduct.includeLeft (y (targetUnit R κ) k)) (fun k => by
      rw [← map_mul, ← map_one (Algebra.TensorProduct.includeLeft :
        Universal R κ →ₐ[Target R κ] BaseChange (R := R) (S := S) (κ := κ)), ← map_sub, equation]
      rw [AlgHom.commutes]
      rw [show (targetUnit R κ k : Target R κ) = DiagonalPowerFibers.laurentCoordinate R κ k from rfl]
      rw [← hχ k, AlgHom.commutes])

theorem toTensor_x (k : κ) : toTensor χ hχ (x χ k) =
    (x (targetUnit R κ) k) ⊗ₜ[Target R κ] (1 : S) := lift_x _ _ _ _ _ k

theorem toTensor_y (k : κ) : toTensor χ hχ (y χ k) =
    (y (targetUnit R κ) k) ⊗ₜ[Target R κ] (1 : S) := lift_y _ _ _ _ _ k

theorem toTensor_coefficient (z : S) : toTensor χ hχ (algebraMap S (LocalAlgebra χ) z) =
    (1 : Universal R κ) ⊗ₜ[Target R κ] z := lift_coefficient _ _ _ _ _ z

theorem fromTensor_toTensor : (fromTensor χ hχ).comp (toTensor χ hχ) =
    AlgHom.id (Target R κ) (LocalAlgebra χ) := by
  apply hom_ext χ
  · intro z
    rw [AlgHom.comp_apply, toTensor_coefficient]
    change fromUniversal χ hχ 1 * algebraMap S (LocalAlgebra χ) z = _
    rw [map_one, one_mul]
    rfl
  · intro k
    rw [AlgHom.comp_apply, toTensor_x]
    change fromUniversal χ hχ (x (targetUnit R κ) k) * algebraMap S (LocalAlgebra χ) 1 = _
    rw [map_one, mul_one, fromUniversal_x]
    rfl
  · intro k
    rw [AlgHom.comp_apply, toTensor_y]
    change fromUniversal χ hχ (y (targetUnit R κ) k) * algebraMap S (LocalAlgebra χ) 1 = _
    rw [map_one, mul_one, fromUniversal_y]
    rfl

theorem toTensor_fromUniversal : (toTensor χ hχ).comp (fromUniversal χ hχ) =
    (Algebra.TensorProduct.includeLeft : Universal R κ →ₐ[Target R κ]
      BaseChange (R := R) (S := S) (κ := κ)) := by
  apply hom_ext (targetUnit R κ)
  · intro z
    simp only [AlgHom.comp_apply, AlgHom.commutes]
  · intro k
    rw [AlgHom.comp_apply, fromUniversal_x, toTensor_x]
    rfl
  · intro k
    rw [AlgHom.comp_apply, fromUniversal_y, toTensor_y]
    rfl

theorem toTensor_fromTensor : (toTensor χ hχ).comp (fromTensor χ hχ) =
    AlgHom.id (Target R κ) (BaseChange (R := R) (S := S) (κ := κ)) := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro a
    change toTensor χ hχ (fromUniversal χ hχ a * algebraMap S (LocalAlgebra χ) 1) =
      a ⊗ₜ[Target R κ] (1 : S)
    rw [map_one, mul_one]
    exact AlgHom.congr_fun (toTensor_fromUniversal χ hχ) a
  · apply AlgHom.ext
    intro z
    change toTensor χ hχ (fromUniversal χ hχ 1 * algebraMap S (LocalAlgebra χ) z) =
      (1 : Universal R κ) ⊗ₜ[Target R κ] z
    rw [map_one, one_mul, toTensor_coefficient]

def tensorEquiv : LocalAlgebra χ ≃ₐ[Target R κ] BaseChange (R := R) (S := S) (κ := κ) :=
  AlgEquiv.ofAlgHom (toTensor χ hχ) (fromTensor χ hχ)
    (toTensor_fromTensor χ hχ) (fromTensor_toTensor χ hχ)

#print axioms BaseChange
#print axioms fromUniversal
#print axioms fromUniversal_x
#print axioms fromUniversal_y
#print axioms fromTensor
#print axioms toTensor
#print axioms toTensor_x
#print axioms toTensor_y
#print axioms toTensor_coefficient
#print axioms fromTensor_toTensor
#print axioms toTensor_fromUniversal
#print axioms toTensor_fromTensor
#print axioms tensorEquiv
end Verification.LocalExchangeTensor
