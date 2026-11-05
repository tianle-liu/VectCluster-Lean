/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRecursiveDegreeCoefficients
import Verification.PathFullComplex
import Verification.MatrixOfDegree
import Verification.MatrixDegreeEquivalence

/-!
# Path Recursive Complex

Genuine recursive cochain complexes and chain isomorphisms from the
original full-rho path complexes, with the closed summand shifted by one.
-/

namespace Verification.PathRecursiveComplex

open CategoryTheory Verification.PathEndpointComplex Verification.PathEndpointCoordinates
  Verification.PathEndpointWords Verification.PathNormalizedBasis Verification.PathStratumGrading
  Verification.PathActualConeMatrices Verification.PathRecursiveDegreeCoefficients
  Verification.PathDifferentialDegree Verification.GradedPerturbation Verification.PathFullComplex

variable {R : Type} [CommRing R] (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)

theorem z_matrix_degree (n : ℕ) : Homogeneous (zDegree n) 1 (zRecursiveMatrix g ρ hg hr n) :=
  Verification.MatrixOfDegree.matrixOf_degree (R := R) (M := ZModule ρ (n+2))
    (zDegree n) (zRecursiveCoefficients g ρ hg hr n) (zDifferential g ρ (n+2))
    (fun p x hx => (z_coefficients_degree g ρ hg hr n (p+1) _).mpr
      (z_differential_degree g ρ (n+2) p x ((z_coefficients_degree g ρ hg hr n p x).mp hx)))

theorem y_matrix_degree (m : ℕ) : Homogeneous (yDegree m) 1 (yRecursiveMatrix g ρ hg hr m) :=
  Verification.MatrixOfDegree.matrixOf_degree (R := R) (M := YModule ρ (m+1))
    (yDegree m) (yRecursiveCoefficients g ρ hg hr m) (yDifferential g ρ (m+1))
    (fun p x hx => (y_coefficients_degree g ρ hg hr m (p+1) _).mpr
      (y_differential_degree g ρ (m+1) p x ((y_coefficients_degree g ρ hg hr m p x).mp hx)))

noncomputable def zComplex (n : ℕ) : CochainComplex (ModuleCat R) ℤ :=
  matrixComplex (zDegree n) (zRecursiveMatrix g ρ hg hr n) (z_matrix_degree g ρ hg hr n)
    (z_recursive_square g ρ hg hr n)

noncomputable def yComplex (m : ℕ) : CochainComplex (ModuleCat R) ℤ :=
  matrixComplex (yDegree m) (yRecursiveMatrix g ρ hg hr m) (y_matrix_degree g ρ hg hr m)
    (y_recursive_square g ρ hg hr m)

noncomputable def zChangeData (n : ℕ) :
    Verification.MatrixOfDegree.ChangeData (zMatrix g ρ (n+2)) (zRecursiveMatrix g ρ hg hr n) := by
  unfold zMatrix zRecursiveMatrix
  exact Verification.MatrixOfDegree.changeData (R := R) (M := ZModule ρ (n+2))
    (ι := NormalIndex RightNormal (n+2)) (κ := ZRecursiveIndex n)
    (zCoefficients ρ (n+2)) (zRecursiveCoefficients g ρ hg hr n) (zDifferential g ρ (n+2))

noncomputable def yChangeData (m : ℕ) :
    Verification.MatrixOfDegree.ChangeData (yMatrix g ρ (m+1)) (yRecursiveMatrix g ρ hg hr m) := by
  unfold yMatrix yRecursiveMatrix
  exact Verification.MatrixOfDegree.changeData (R := R) (M := YModule ρ (m+1))
    (ι := NormalIndex BothNormal (2*(m+1))) (κ := YRecursiveIndex m)
    (yCoefficients ρ (m+1)) (yRecursiveCoefficients g ρ hg hr m) (yDifferential g ρ (m+1))

noncomputable def zChange (n : ℕ) :
    (NormalIndex RightNormal (n+2) → R) ≃ₗ[R] (ZRecursiveIndex n → R) :=
  (zChangeData g ρ hg hr n).change

noncomputable def yChange (m : ℕ) :
    (NormalIndex BothNormal (2*(m+1)) → R) ≃ₗ[R] (YRecursiveIndex m → R) :=
  (yChangeData g ρ hg hr m).change

theorem z_change_degree (n : ℕ) (p : ℤ) (f : NormalIndex RightNormal (n+2) → R)
    (hf : f ∈ degreeModule degree p) : zChange g ρ hg hr n f ∈ degreeModule (zDegree n) p :=
  (z_coefficients_degree g ρ hg hr n p _).mpr (Verification.PathCoefficientDegree.z_inverse_degree ρ (n+2) p f hf)

theorem y_change_degree (m : ℕ) (p : ℤ) (f : NormalIndex BothNormal (2*(m+1)) → R)
    (hf : f ∈ degreeModule degree p) : yChange g ρ hg hr m f ∈ degreeModule (yDegree m) p :=
  (y_coefficients_degree g ρ hg hr m p _).mpr (Verification.PathCoefficientDegree.y_inverse_degree ρ (m+1) p f hf)

theorem z_change_inverse_degree (n : ℕ) (p : ℤ) (f : ZRecursiveIndex n → R)
    (hf : f ∈ degreeModule (zDegree n) p) : (zChange g ρ hg hr n).symm f ∈ degreeModule degree p :=
  (Verification.PathCoefficientDegree.z_coefficients_degree ρ (n+2) p _).mpr (z_inverse_degree g ρ hg hr n p f hf)

theorem y_change_inverse_degree (m : ℕ) (p : ℤ) (f : YRecursiveIndex m → R)
    (hf : f ∈ degreeModule (yDegree m) p) : (yChange g ρ hg hr m).symm f ∈ degreeModule degree p :=
  (Verification.PathCoefficientDegree.y_coefficients_degree ρ (m+1) p _).mpr (y_inverse_degree g ρ hg hr m p f hf)

theorem z_change_differential (n : ℕ) :
    (Matrix.toLin' (zRecursiveMatrix g ρ hg hr n)).comp (zChange g ρ hg hr n).toLinearMap=
      (zChange g ρ hg hr n).toLinearMap.comp (Matrix.toLin' (zMatrix g ρ (n+2))) :=
  (zChangeData g ρ hg hr n).intertwining

theorem y_change_differential (m : ℕ) :
    (Matrix.toLin' (yRecursiveMatrix g ρ hg hr m)).comp (yChange g ρ hg hr m).toLinearMap=
      (yChange g ρ hg hr m).toLinearMap.comp (Matrix.toLin' (yMatrix g ρ (m+1))) :=
  (yChangeData g ρ hg hr m).intertwining

noncomputable def zIso (n : ℕ) : zCochainComplex g ρ (n+2) hg hr ≅ zComplex g ρ hg hr n :=
  Verification.MatrixDegreeEquivalence.complexIso degree (zDegree n) (zChange g ρ hg hr n)
    (z_change_degree g ρ hg hr n) (z_change_inverse_degree g ρ hg hr n)
    (zMatrix g ρ (n+2)) (zRecursiveMatrix g ρ hg hr n)
    (zMatrix_degree g ρ (n+2)) (z_matrix_degree g ρ hg hr n)
    (zMatrix_squared g ρ (n+2) hg hr) (z_recursive_square g ρ hg hr n) (z_change_differential g ρ hg hr n)

noncomputable def yIso (m : ℕ) : yCochainComplex g ρ (m+1) hg hr ≅ yComplex g ρ hg hr m :=
  Verification.MatrixDegreeEquivalence.complexIso degree (yDegree m) (yChange g ρ hg hr m)
    (y_change_degree g ρ hg hr m) (y_change_inverse_degree g ρ hg hr m)
    (yMatrix g ρ (m+1)) (yRecursiveMatrix g ρ hg hr m)
    (yMatrix_degree g ρ (m+1)) (y_matrix_degree g ρ hg hr m)
    (yMatrix_squared g ρ (m+1) hg hr) (y_recursive_square g ρ hg hr m) (y_change_differential g ρ hg hr m)

#print axioms z_matrix_degree
#print axioms y_matrix_degree
#print axioms zComplex
#print axioms yComplex
#print axioms zChangeData
#print axioms yChangeData
#print axioms zChange
#print axioms yChange
#print axioms z_change_degree
#print axioms y_change_degree
#print axioms z_change_inverse_degree
#print axioms y_change_inverse_degree
#print axioms z_change_differential
#print axioms y_change_differential
#print axioms zIso
#print axioms yIso

end Verification.PathRecursiveComplex
