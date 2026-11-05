/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathNormalizedBasis

/-!
# Path Endpoint Basis

Actual finite free bases for both full-rho endpoint quotient modules.
The indices are original independent zero sets and original binary words
with each constant endpoint normalized to an unselected symbol.
-/

namespace Verification.PathEndpointBasis

open Classical Verification.PathCochains Verification.PathEndpointComplex
  Verification.PathEndpointWords Verification.PathNormalizedBasis

variable {R : Type*} [CommRing R]

theorem right_column_normal (k : R) (w : List Bool) :
    Verification.PathRightEndpoint.projection k (Finsupp.single w 1) ∈
      normalLayer (R := R) RightNormal w.length := by
  rw [right_projection_column]
  apply (normalLayer RightNormal w.length).smul_mem
  exact Finsupp.single_mem_supported R 1
    ⟨normalizeRight_length w,normalizeRight_idempotent w⟩

theorem both_column_normal (a b : R) (w : List Bool) :
    ((Verification.PathLeftEndpoint.projection a).comp
      (Verification.PathRightEndpoint.projection b)) (Finsupp.single w 1) ∈
      normalLayer (R := R) BothNormal w.length := by
  rw [LinearMap.comp_apply,right_projection_column,map_smul,left_projection_column]
  apply (normalLayer BothNormal w.length).smul_mem
  apply (normalLayer BothNormal w.length).smul_mem
  exact Finsupp.single_mem_supported R 1
    ⟨(normalizeLeft_length _).trans (normalizeRight_length w),both_normalized w⟩

theorem both_column_fixed (a b : R) (w : List Bool) (hw : BothNormal w) :
    ((Verification.PathLeftEndpoint.projection a).comp
      (Verification.PathRightEndpoint.projection b)) (Finsupp.single w 1)=Finsupp.single w 1 := by
  rw [LinearMap.comp_apply,right_projection_fixed b w hw.2,left_projection_fixed a w hw.1]

/-- This is the quotient module of the actual Z differential, with a proved free basis. -/
noncomputable def zBasis (ρ : R) (n : ℕ) :
    Basis (NormalIndex RightNormal n) R (ZModule ρ n) :=
  rangeBasis RightNormal (Verification.PathRightEndpoint.projection (endpointConstant ρ n))
    (right_column_normal _) (right_projection_fixed _) n (zProjection ρ n) (fun _ _ => rfl)

/-- The Y basis has both constant endpoints omitted in every original stratum. -/
noncomputable def yBasis (ρ : R) (a : ℕ) :
    Basis (NormalIndex BothNormal (2*a)) R (YModule ρ a) :=
  rangeBasis BothNormal ((Verification.PathLeftEndpoint.projection 0).comp
    (Verification.PathRightEndpoint.projection (endpointConstant ρ (2*a))))
      (both_column_normal _ _) (both_column_fixed _ _) (2*a) (yProjection ρ a) (fun _ _ => rfl)

theorem zModule_free (ρ : R) (n : ℕ) : Module.Free R (ZModule ρ n) := Module.Free.of_basis (zBasis ρ n)
theorem yModule_free (ρ : R) (a : ℕ) : Module.Free R (YModule ρ a) := Module.Free.of_basis (yBasis ρ a)

theorem zModule_finite (ρ : R) (n : ℕ) : Module.Finite R (ZModule ρ n) := Module.Finite.of_basis (zBasis ρ n)
theorem yModule_finite (ρ : R) (a : ℕ) : Module.Finite R (YModule ρ a) := Module.Finite.of_basis (yBasis ρ a)

/-- The inverse representation is a literal coefficient vector on the finite normalized-word set. -/
noncomputable def zCoordinates (ρ : R) (n : ℕ) :
    ZModule ρ n ≃ₗ[R] (NormalIndex RightNormal n → R) :=
  (zBasis ρ n).repr.trans (Finsupp.linearEquivFunOnFinite R R _)

noncomputable def yCoordinates (ρ : R) (a : ℕ) :
    YModule ρ a ≃ₗ[R] (NormalIndex BothNormal (2*a) → R) :=
  (yBasis ρ a).repr.trans (Finsupp.linearEquivFunOnFinite R R _)

#print axioms right_column_normal
#print axioms both_column_normal
#print axioms both_column_fixed
#print axioms zBasis
#print axioms yBasis
#print axioms zModule_free
#print axioms yModule_free
#print axioms zModule_finite
#print axioms yModule_finite
#print axioms zCoordinates
#print axioms yCoordinates

end Verification.PathEndpointBasis
