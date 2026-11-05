/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinateLastRegular
import Verification.PrincipalConormal
import Verification.ActualOpenRegular
import Verification.ActualTransverseLocalization
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Actual Transverse Regular

The literal transverse intermediate quotient has a regular last
original coordinate under selected-column injectivity. Its actual normal
line is framed by that original parameter, so the slice's parameter
identity is an identity of genuine conormal generators.
-/
noncomputable section
universe u
namespace Verification.ActualTransverseRegular
open Verification.ActualOpenChart Verification.ActualOpenGeometry
open Verification.ActualTransverseSlice Verification.ActualTransverseLocalization
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0)
variable (hf : Function.Injective (columnMap ι κ τ B)) (v : ι)

include hB hf in
theorem parameter_regular : IsSMulRegular (Intermediate R ι κ τ j B v)
    (originalParameter R ι κ τ j B v) :=
  CoordinateLastRegular.regular_after_others (globalCoordinate R ι κ τ j B) v
    (ActualOpenRegular.original_coordinates_weaklyRegular R ι κ τ j B hB hf)

def conormalBasis : Basis PUnit.{u+1} (ClosedSource R ι κ τ j B v)
    (closedIdeal R ι κ τ j B v).Cotangent :=
  PrincipalConormal.basis (originalParameter R ι κ τ j B v)
    (parameter_regular R ι κ τ j B hB hf v)

theorem conormalBasis_apply (i : PUnit.{u+1}) :
    conormalBasis R ι κ τ j B hB hf v i =
      (closedIdeal R ι κ τ j B v).toCotangent
        ⟨originalParameter R ι κ τ j B v,Ideal.subset_span (Set.mem_singleton _)⟩ :=
  PrincipalConormal.basis_apply _ _ i

set_option synthInstance.maxHeartbeats 100000 in
def normalBasis : Basis PUnit.{u+1} (ClosedSource R ι κ τ j B v)
    (Module.Dual (ClosedSource R ι κ τ j B v) (closedIdeal R ι κ τ j B v).Cotangent) :=
  (conormalBasis R ι κ τ j B hB hf v).dualBasis

theorem normal_parameter : normalBasis R ι κ τ j B hB hf v PUnit.unit
    ((closedIdeal R ι κ τ j B v).toCotangent
      ⟨originalParameter R ι κ τ j B v,Ideal.subset_span (Set.mem_singleton _)⟩) = 1 := by
  rw [← conormalBasis_apply R ι κ τ j B hB hf v PUnit.unit]
  simp only [normalBasis,Basis.dualBasis_apply_self,ite_true]

theorem conormal_slice : conormalMap R ι κ τ j B hB v
    (conormalBasis R ι κ τ j B hB hf v PUnit.unit) =
    (ExchangeTransverseSlice.parameterIdeal (characters R ι κ τ B)).toCotangent
      ⟨Polynomial.X,Ideal.subset_span (Set.mem_singleton _)⟩ := by
  rw [conormalBasis_apply]
  exact conormal_parameter R ι κ τ j B hB v

#print axioms parameter_regular
#print axioms conormalBasis
#print axioms conormalBasis_apply
#print axioms normalBasis
#print axioms normal_parameter
#print axioms conormal_slice
end Verification.ActualTransverseRegular
