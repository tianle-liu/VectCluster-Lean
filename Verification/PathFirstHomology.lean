/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.NonpositiveMatrixHomology
import Verification.PathFirstDegreeBoundary
import Verification.PathActualFirstCokernel

/-!
# Path First Homology

The literal first word cokernels are the genuine degree-zero homology of
the full finite path chain complexes at rho=0, with their stated free bases.
-/

namespace Verification.PathFirstHomology

open Classical CategoryTheory Verification.PathFirstDegreeCoordinates
  Verification.PathFirstDegreeBoundary Verification.PathFirstBoundaryCutout
  Verification.PathActualFirstCokernel Verification.PathEndpointWords
  Verification.PathFullComplex Verification.PathEndpointCoordinates Verification.PathStratumGrading
  Verification.BoundaryCokernelTransport

variable {R : Type} [CommRing R]

noncomputable def zCokernelEquiv (g : R) (n : ℕ) :
    (Verification.GradedPerturbation.degreeModule (R := R) (fun x => -degree x) 0 ⧸
      LinearMap.range (zFirstMap g n)) ≃ₗ[R] ZCokernel g n :=
  cokernelEquiv (zFirstMap g n) (zBoundary g n)
    (firstCoordinates RightNormal n) (zZeroCoordinates n) (z_first_coordinates g n)

noncomputable def yCokernelEquiv (g : R) (m : ℕ) :
    (Verification.GradedPerturbation.degreeModule (R := R) (fun x => -degree x) 0 ⧸
      LinearMap.range (yFirstMap g m)) ≃ₗ[R] YCokernel g m :=
  cokernelEquiv (yFirstMap g m) (yBoundary g m)
    (firstCoordinates BothNormal (2*m)) (yZeroCoordinates m) (y_first_coordinates g m)

noncomputable def zHomologyIso (g : R) (hg : g*g=1) (n : ℕ) :
    (zChainComplex g 0 n hg (by simp)).homology 0 ≅ ModuleCat.of R (ZCokernel g n) :=
  Verification.NonpositiveMatrixHomology.homologyZeroIso _ _
    (transpose_degree _ _ (zMatrix_degree g 0 n))
    (transpose_square _ (zMatrix_squared g 0 n hg (by simp)))
    (by intro i; change -(i.1.val.card:ℤ)≤0; omega) ≪≫ (zCokernelEquiv g n).toModuleIso

noncomputable def yHomologyIso (g : R) (hg : g*g=1) (m : ℕ) :
    (yChainComplex g 0 m hg (by simp)).homology 0 ≅ ModuleCat.of R (YCokernel g m) :=
  Verification.NonpositiveMatrixHomology.homologyZeroIso _ _
    (transpose_degree _ _ (yMatrix_degree g 0 m))
    (transpose_square _ (yMatrix_squared g 0 m hg (by simp)))
    (by intro i; change -(i.1.val.card:ℤ)≤0; omega) ≪≫ (yCokernelEquiv g m).toModuleIso

noncomputable def zHomologyBasis (g : R) (hg : g*g=1) (n : ℕ) :
    Basis (Fin (n+2)) R ((zChainComplex g 0 n hg (by simp)).homology 0) :=
  (zBasis g hg n).map (zHomologyIso g hg n).symm.toLinearEquiv

noncomputable def yHomologyBasis (g : R) (hg : g*g=1) (m : ℕ) :
    Basis (Fin (m+1)) R ((yChainComplex g 0 m hg (by simp)).homology 0) :=
  (yBasis g hg m).map (yHomologyIso g hg m).symm.toLinearEquiv

theorem z_homology_finrank [Nontrivial R] (g : R) (hg : g*g=1) (n : ℕ) :
    Module.finrank R ((zChainComplex g 0 n hg (by simp)).homology 0)=n+2 := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (zHomologyBasis g hg n)

theorem y_homology_finrank [Nontrivial R] (g : R) (hg : g*g=1) (m : ℕ) :
    Module.finrank R ((yChainComplex g 0 m hg (by simp)).homology 0)=m+1 := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (yHomologyBasis g hg m)

#print axioms zCokernelEquiv
#print axioms yCokernelEquiv
#print axioms zHomologyIso
#print axioms yHomologyIso
#print axioms zHomologyBasis
#print axioms yHomologyBasis
#print axioms z_homology_finrank
#print axioms y_homology_finrank

end Verification.PathFirstHomology
