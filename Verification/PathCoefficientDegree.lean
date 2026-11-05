/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathCoefficientInclusion
import Verification.PathRecursionDegree
import Verification.PathStratumGrading

/-!
# Path Coefficient Degree

Degree support in the actual stratum modules is exactly support in the
literal finite coefficient functions. This supplies the basis comparison
needed for recursive matrix-complex isomorphisms.
-/

namespace Verification.PathCoefficientDegree

open Verification.PathCompression Verification.PathCochains Verification.PathNormalizedBasis
  Verification.PathEndpointCoordinates Verification.PathEndpointWords Verification.PathEndpointBasis
  Verification.PathEndpointComplex Verification.PathRecursionDegree Verification.PathStratumGrading
  Verification.GradedPerturbation

variable {R : Type*} [CommRing R]

theorem normal_coordinates_degree (B : List Bool → Prop) (n : ℕ) (p : ℤ)
    (x : NormalTotal (R := R) B n) :
    normalCoordinates B n x ∈ degreeModule degree p ↔ TotalDegree n p (normalInclusion B n x) := by
  constructor
  · intro hx I hI
    apply Subtype.ext
    apply Finsupp.ext
    intro w
    change (x I).val w=0
    by_cases hw : w.length=(available I.val (n+2)).card ∧ B w
    · exact hx (⟨I,⟨w,hw⟩⟩ : NormalIndex B n) hI
    · exact (Finsupp.mem_supported' R _).mp (x I).property w hw
  · intro hx i hi
    have hh := hx i.1 hi
    exact congrArg (fun z => z.val i.2.val) hh

theorem z_coefficients_degree (ρ : R) (n : ℕ) (p : ℤ) (x : ZModule ρ n) :
    zCoefficients ρ n x ∈ degreeModule degree p ↔ TotalDegree n p x.val :=
  normal_coordinates_degree RightNormal n p
    (rangeEquiv RightNormal (Verification.PathRightEndpoint.projection (endpointConstant ρ n))
      (right_column_normal _) (right_projection_fixed _) n (zProjection ρ n) (fun _ _ => rfl) x)

theorem y_coefficients_degree (ρ : R) (m : ℕ) (p : ℤ) (x : YModule ρ m) :
    yCoefficients ρ m x ∈ degreeModule degree p ↔ TotalDegree (2*m) p x.val :=
  normal_coordinates_degree BothNormal (2*m) p
    (rangeEquiv BothNormal ((Verification.PathLeftEndpoint.projection 0).comp
      (Verification.PathRightEndpoint.projection (endpointConstant ρ (2*m))))
        (both_column_normal _ _) (both_column_fixed _ _) (2*m) (yProjection ρ m) (fun _ _ => rfl) x)

theorem z_inverse_degree (ρ : R) (n : ℕ) (p : ℤ) (f : NormalIndex RightNormal n → R)
    (hf : f ∈ degreeModule degree p) : TotalDegree n p ((zCoefficients ρ n).symm f).val := by
  apply (z_coefficients_degree ρ n p _).mp
  simpa only [LinearEquiv.apply_symm_apply] using hf

theorem y_inverse_degree (ρ : R) (m : ℕ) (p : ℤ) (f : NormalIndex BothNormal (2*m) → R)
    (hf : f ∈ degreeModule degree p) : TotalDegree (2*m) p ((yCoefficients ρ m).symm f).val := by
  apply (y_coefficients_degree ρ m p _).mp
  simpa only [LinearEquiv.apply_symm_apply] using hf

#print axioms normal_coordinates_degree
#print axioms z_coefficients_degree
#print axioms y_coefficients_degree
#print axioms z_inverse_degree
#print axioms y_inverse_degree

end Verification.PathCoefficientDegree
