/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathActualConeMatrices
import Verification.PathActualConeDegrees
import Verification.PathCoefficientDegree

/-!
# Path Recursive Degree Coefficients

The recursively split finite matrices carry the actual cellular grading,
including the closed degree shift. These are exact coefficient comparisons.
-/

namespace Verification.PathRecursiveDegreeCoefficients

open Verification.PathEndpointComplex Verification.PathEndpointCoordinates Verification.PathStratumGrading
  Verification.PathActualCones Verification.PathActualConeMatrices Verification.PathActualConeDegrees
  Verification.PathCoefficientDegree Verification.PathRecursionDegree Verification.GradedPerturbation

variable {R : Type*} [CommRing R]

def zDegree (n : ℕ) : ZRecursiveIndex n → ℤ := Sum.elim (fun x => degree x+1) (fun x => degree x.2)
def yDegree (m : ℕ) : YRecursiveIndex m → ℤ := Sum.elim (fun x => degree x+1) degree

variable (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)

theorem z_coefficients_degree (n : ℕ) (p : ℤ) (x : ZModule ρ (n+2)) :
    zRecursiveCoefficients g ρ hg hr n x ∈ degreeModule (zDegree n) p ↔ TotalDegree (n+2) p x.val := by
  constructor
  · intro hx
    have hc : TotalDegree n (p-1) (zCoordinates g ρ hg hr n x).1.val := by
      apply (Verification.PathCoefficientDegree.z_coefficients_degree ρ n (p-1) _).mp
      intro i hi
      exact hx (Sum.inl i) (by change degree i+1 ≠ p; omega)
    have ho : ∀ bit, TotalDegree (n+1) p ((zCoordinates g ρ hg hr n x).2 bit).val := by
      intro bit
      apply (Verification.PathCoefficientDegree.z_coefficients_degree ρ (n+1) p _).mp
      intro i hi
      exact hx (Sum.inr ⟨bit,i⟩) hi
    have hh := Verification.PathActualConeDegrees.z_inverse_degree g ρ hg hr n p _ hc ho
    simpa only [LinearEquiv.symm_apply_apply] using hh
  · intro hx i hi
    have hc := (z_coordinates_degree g ρ hg hr n p x hx).1
    have ho := (z_coordinates_degree g ρ hg hr n p x hx).2
    cases i with
    | inl i =>
      exact (Verification.PathCoefficientDegree.z_coefficients_degree ρ n (p-1) _).mpr hc i
        (by change degree i+1 ≠ p at hi; omega)
    | inr i => exact (Verification.PathCoefficientDegree.z_coefficients_degree ρ (n+1) p _).mpr (ho i.1) i.2 hi

theorem y_coefficients_degree (m : ℕ) (p : ℤ) (x : YModule ρ (m+1)) :
    yRecursiveCoefficients g ρ hg hr m x ∈ degreeModule (yDegree m) p ↔ TotalDegree (2*(m+1)) p x.val := by
  constructor
  · intro hx
    have hc : TotalDegree (2*m) (p-1) (yCoordinates g ρ hg hr m x).1.val := by
      apply (Verification.PathCoefficientDegree.y_coefficients_degree ρ m (p-1) _).mp
      intro i hi
      exact hx (Sum.inl i) (by change degree i+1 ≠ p; omega)
    have ho : TotalDegree (2*m+1) p (yCoordinates g ρ hg hr m x).2.val := by
      apply (Verification.PathCoefficientDegree.z_coefficients_degree ρ (2*m+1) p _).mp
      intro i hi
      exact hx (Sum.inr i) hi
    have hh := Verification.PathActualConeDegrees.y_inverse_degree g ρ hg hr m p _ hc ho
    simpa only [LinearEquiv.symm_apply_apply] using hh
  · intro hx i hi
    have hc := (y_coordinates_degree g ρ hg hr m p x hx).1
    have ho := (y_coordinates_degree g ρ hg hr m p x hx).2
    cases i with
    | inl i =>
      exact (Verification.PathCoefficientDegree.y_coefficients_degree ρ m (p-1) _).mpr hc i
        (by change degree i+1 ≠ p at hi; omega)
    | inr i => exact (Verification.PathCoefficientDegree.z_coefficients_degree ρ (2*m+1) p _).mpr ho i hi

theorem z_inverse_degree (n : ℕ) (p : ℤ) (f : ZRecursiveIndex n → R)
    (hf : f ∈ degreeModule (zDegree n) p) :
    TotalDegree (n+2) p ((zRecursiveCoefficients g ρ hg hr n).symm f).val := by
  apply (z_coefficients_degree g ρ hg hr n p _).mp
  simpa only [LinearEquiv.apply_symm_apply] using hf

theorem y_inverse_degree (m : ℕ) (p : ℤ) (f : YRecursiveIndex m → R)
    (hf : f ∈ degreeModule (yDegree m) p) :
    TotalDegree (2*(m+1)) p ((yRecursiveCoefficients g ρ hg hr m).symm f).val := by
  apply (y_coefficients_degree g ρ hg hr m p _).mp
  simpa only [LinearEquiv.apply_symm_apply] using hf

#print axioms zDegree
#print axioms yDegree
#print axioms z_coefficients_degree
#print axioms y_coefficients_degree
#print axioms z_inverse_degree
#print axioms y_inverse_degree

end Verification.PathRecursiveDegreeCoefficients
