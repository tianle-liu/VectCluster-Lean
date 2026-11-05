/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualTransverseRegular
import Verification.PrincipalConormalMap

/-!
# Actual Transverse Normal Map

The true base-changed conormal comparison for the transverse slice
is an isomorphism. It is the actual ideal-induced map and sends the
original x_v frame to the u frame with coefficient exactly one.
-/
noncomputable section
universe u
namespace Verification.ActualTransverseNormalMap
open Verification.ActualOpenChart Verification.ActualOpenGeometry
open Verification.ActualTransverseSlice Verification.ActualTransverseLocalization
open Verification.ActualTransverseRegular Verification.ExchangeTransverseSlice
open scoped TensorProduct
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0)
variable (hf : Function.Injective (columnMap ι κ τ B)) (v : ι)

abbrev SliceClosed := Slice (characters R ι κ τ B) ⧸ parameterIdeal (characters R ι κ τ B)

def sliceClosedAlgebra : Algebra (ClosedSource R ι κ τ j B v) (SliceClosed R ι κ τ B) :=
  PrincipalConormalMap.quotientAlgebra (transverseSlice R ι κ τ j B hB v).toRingHom
    (originalParameter R ι κ τ j B v) Polynomial.X (transverse_parameter R ι κ τ j B hB v)

def normalPullbackEquiv : letI := sliceClosedAlgebra R ι κ τ j B hB v;
    (SliceClosed R ι κ τ B) ⊗[ClosedSource R ι κ τ j B v] (closedIdeal R ι κ τ j B v).Cotangent
      ≃ₗ[SliceClosed R ι κ τ B] (parameterIdeal (characters R ι κ τ B)).Cotangent :=
  PrincipalConormalMap.pullbackEquiv (transverseSlice R ι κ τ j B hB v).toRingHom
    (originalParameter R ι κ τ j B v) Polynomial.X (transverse_parameter R ι κ τ j B hB v)
    (parameter_regular R ι κ τ j B hB hf v) Polynomial.isRegular_X.left

theorem normalPullbackEquiv_map (z : (closedIdeal R ι κ τ j B v).Cotangent) :
    letI := sliceClosedAlgebra R ι κ τ j B hB v;
    normalPullbackEquiv R ι κ τ j B hB hf v (1 ⊗ₜ[ClosedSource R ι κ τ j B v] z) =
      conormalMap R ι κ τ j B hB v z := by
  letI := sliceClosedAlgebra R ι κ τ j B hB v
  have h := PrincipalConormalMap.pullbackEquiv_one_tmul
    (transverseSlice R ι κ τ j B hB v).toRingHom
    (originalParameter R ι κ τ j B v) Polynomial.X (transverse_parameter R ι κ τ j B hB v)
    (parameter_regular R ι κ τ j B hB hf v) Polynomial.isRegular_X.left z
  exact h

theorem normalPullbackEquiv_frame : letI := sliceClosedAlgebra R ι κ τ j B hB v;
    normalPullbackEquiv R ι κ τ j B hB hf v
      (1 ⊗ₜ[ClosedSource R ι κ τ j B v] conormalBasis R ι κ τ j B hB hf v PUnit.unit) =
    (parameterIdeal (characters R ι κ τ B)).toCotangent
      ⟨Polynomial.X,Ideal.subset_span (Set.mem_singleton _)⟩ := by
  letI := sliceClosedAlgebra R ι κ τ j B hB v
  rw [normalPullbackEquiv_map]
  exact conormal_slice R ι κ τ j B hB hf v

#print axioms SliceClosed
#print axioms sliceClosedAlgebra
#print axioms normalPullbackEquiv
#print axioms normalPullbackEquiv_map
#print axioms normalPullbackEquiv_frame
end Verification.ActualTransverseNormalMap
