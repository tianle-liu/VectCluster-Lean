/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittTensorTerms

/-!
# Original Witt Tensor Differential

The differential of the literal coefficient tensor extension, on every
element, in its actual independent-stratum coordinates.
-/
noncomputable section
open scoped Classical TensorProduct
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalWittTensorDifferential
open CategoryTheory
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.OriginalWittTensorTerms
variable (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (A : Type) [AddCommGroup A]
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)

omit [Fintype κ] in
theorem apply (p : ℕ) (x : (complex κ n B A hpos hneg hsupport).X p)
    (J : ActualCellThom.Index κ n B (p+1)) :
    termEquiv κ n B A (p+1) (((complex κ n B A hpos hneg hsupport).d p (p+1)) x) J =
      ∑ v : J.val, SubsetProjectionComplex.sign J.val v.val •
        OriginalWittAdjacentFace.integerFace κ n J.val B v hpos hneg hsupport J.property.2 A
          (termEquiv κ n B A p x (ActualGlobalBoundary.edgeIndex κ n B p J v)) := by
  let lhs : (complex κ n B A hpos hneg hsupport).X p →ₗ[ℤ]
      (OriginalWittQuotient.Stratum (fun a i => B a (Sum.inl i)) J.val ⊗[ℤ] A) :=
    (LinearMap.proj J).comp ((termEquiv κ n B A (p+1)).toLinearMap.comp
      ((complex κ n B A hpos hneg hsupport).d p (p+1)).hom)
  let rhs : (complex κ n B A hpos hneg hsupport).X p →ₗ[ℤ]
      (OriginalWittQuotient.Stratum (fun a i => B a (Sum.inl i)) J.val ⊗[ℤ] A) :=
    ∑ v : J.val, SubsetProjectionComplex.sign J.val v.val •
      (OriginalWittAdjacentFace.integerFace κ n J.val B v hpos hneg hsupport J.property.2 A).comp
        ((LinearMap.proj (ActualGlobalBoundary.edgeIndex κ n B p J v)).comp
          (termEquiv κ n B A p).toLinearMap)
  have he : lhs=rhs := by
    apply TensorProduct.ext'
    intro f a
    simpa only [lhs,rhs,LinearMap.comp_apply,LinearMap.proj_apply,
      LinearMap.sum_apply,LinearMap.smul_apply,LinearEquiv.coe_coe] using
        differential_tmul κ n B A hpos hneg hsupport p f a J
  simpa only [lhs,rhs,LinearMap.comp_apply,LinearMap.proj_apply,
    LinearMap.sum_apply,LinearMap.smul_apply,LinearEquiv.coe_coe] using LinearMap.congr_fun he x

#print axioms apply
end Verification.OriginalWittTensorDifferential
