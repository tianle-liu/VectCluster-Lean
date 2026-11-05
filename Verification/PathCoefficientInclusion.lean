/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathEndpointCoordinates

/-!
# Path Coefficient Inclusion

The underlying inverse coordinate vector is independent of the scalar
endpoint evaluation. The statement is proved before specializing the actual
endpoint projectors, keeping those proof-dependent range types opaque.
-/

namespace Verification.PathCoefficientInclusion

open Verification.PathCompression Verification.PathCochains
  Verification.PathNormalizedBasis Verification.PathEndpointCoordinates
  Verification.PathEndpointWords Verification.PathEndpointComplex Verification.PathEndpointBasis

variable {R : Type*} [CommRing R]

noncomputable def includedCoordinates (B : List Bool → Prop) (n : ℕ) :
    (NormalIndex B n → R) →ₗ[R] Total (R := R) n :=
  (normalInclusion B n).comp (normalCoordinates B n).symm.toLinearMap

theorem inverse_val (B : List Bool → Prop)
    (P : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R))
    (hmap : ∀ w, P (Finsupp.single w 1) ∈ normalLayer (R := R) B w.length)
    (hfix : ∀ w, B w → P (Finsupp.single w 1)=Finsupp.single w 1)
    (n : ℕ) (T : Total (R := R) n →ₗ[R] Total (R := R) n)
    (ht : ∀ x I, (T x I).val=P (x I).val) (f : NormalIndex B n → R) :
    (((rangeEquiv B P hmap hfix n T ht).trans (normalCoordinates B n)).symm f).val=
      includedCoordinates B n f := rfl

theorem z_inverse_val (ρ : R) (n : ℕ) (f : NormalIndex RightNormal n → R) :
    ((zCoefficients ρ n).symm f).val=includedCoordinates RightNormal n f :=
  inverse_val RightNormal (Verification.PathRightEndpoint.projection (endpointConstant ρ n))
    (right_column_normal _) (right_projection_fixed _) n (zProjection ρ n) (fun _ _ => rfl) f

theorem y_inverse_val (ρ : R) (a : ℕ) (f : NormalIndex BothNormal (2*a) → R) :
    ((yCoefficients ρ a).symm f).val=includedCoordinates BothNormal (2*a) f :=
  inverse_val BothNormal ((Verification.PathLeftEndpoint.projection 0).comp
    (Verification.PathRightEndpoint.projection (endpointConstant ρ (2*a))))
      (both_column_normal _ _) (both_column_fixed _ _) (2*a) (yProjection ρ a) (fun _ _ => rfl) f

#print axioms includedCoordinates
#print axioms inverse_val
#print axioms z_inverse_val
#print axioms y_inverse_val

end Verification.PathCoefficientInclusion
