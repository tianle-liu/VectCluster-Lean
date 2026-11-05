/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathFirstBasis
import Verification.PathSignedCokernel

/-!
# Path First Boundary Cutout

The actual degree-one to degree-zero matrix cutouts after deleting the
constant endpoint slots. The preceding basis bijections prove exhaustiveness.
-/

namespace Verification.PathFirstBoundaryCutout

open Classical Verification.PathEndpointWords Verification.PathEndpointCoordinates
  Verification.PathFirstBasis Verification.PathActualFirstEntries Verification.PathEndpointWordRemoval
  Verification.PathFirstCofaces

variable {R : Type*} [CommRing R]

noncomputable def zZeroWord (n : ℕ) (w : Verification.PathWords.Word (n+1)) :
    Verification.PathNormalizedBasis.NormalWord RightNormal (n+2) := (rightWordEquiv (n+1)).symm w

noncomputable def yZeroWord (a : ℕ) (w : Verification.PathWords.Word (2*a)) :
    Verification.PathNormalizedBasis.NormalWord BothNormal (2*a+2) := (bothWordEquiv (2*a)).symm w

/-- These columns are extracted from the already constructed full rho matrix at rho=0. -/
noncomputable def zColumn (g : R) (n : ℕ) (v : OneSource RightNormal n) : Verification.PathWords.Word (n+1) →₀ R :=
  Finsupp.equivFunOnFinite.symm (fun w =>
    (zMatrix g 0 n).transpose (zeroIndex RightNormal n (zZeroWord n w)) (oneIndex RightNormal n v))

noncomputable def yColumn (g : R) (a : ℕ) (v : OneSource BothNormal (2*a)) : Verification.PathWords.Word (2*a) →₀ R :=
  Finsupp.equivFunOnFinite.symm (fun w =>
    (yMatrix g 0 a).transpose (zeroIndex BothNormal (2*a) (yZeroWord a w)) (oneIndex BothNormal (2*a) v))

theorem zColumn_apply (g : R) (n : ℕ) (v : OneSource RightNormal n) (w : Verification.PathWords.Word (n+1)) :
    zColumn g n v w=cofaceColumn (-g) 0 (v.1.val-1) v.2.val (w.val++[false]) := by
  exact z_first_entry g n v.1.val v.1.property
    (zeroIndex RightNormal n (zZeroWord n w)).2 (oneIndex RightNormal n v).2

theorem yColumn_apply (g : R) (a : ℕ) (v : OneSource BothNormal (2*a)) (w : Verification.PathWords.Word (2*a)) :
    yColumn g a v w=cofaceColumn (-g) 0 (v.1.val-1) v.2.val (false::(w.val++[false])) := by
  exact y_first_entry g a v.1.val v.1.property
    (zeroIndex BothNormal (2*a) (yZeroWord a w)).2 (oneIndex BothNormal (2*a) v).2

noncomputable def zBoundary (g : R) (n : ℕ) :
    (OneSource RightNormal n →₀ R) →ₗ[R] (Verification.PathWords.Word (n+1) →₀ R) :=
  Finsupp.linearCombination R (zColumn g n)

noncomputable def yBoundary (g : R) (a : ℕ) :
    (OneSource BothNormal (2*a) →₀ R) →ₗ[R] (Verification.PathWords.Word (2*a) →₀ R) :=
  Finsupp.linearCombination R (yColumn g a)

theorem zBoundary_single (g : R) (n : ℕ) (v : OneSource RightNormal n) :
    zBoundary g n (Finsupp.single v 1)=zColumn g n v := by
  simp only [zBoundary,Finsupp.linearCombination_single,one_smul]

theorem yBoundary_single (g : R) (a : ℕ) (v : OneSource BothNormal (2*a)) :
    yBoundary g a (Finsupp.single v 1)=yColumn g a v := by
  simp only [yBoundary,Finsupp.linearCombination_single,one_smul]

#print axioms zZeroWord
#print axioms yZeroWord
#print axioms zColumn
#print axioms yColumn
#print axioms zColumn_apply
#print axioms yColumn_apply
#print axioms zBoundary
#print axioms yBoundary
#print axioms zBoundary_single
#print axioms yBoundary_single

end Verification.PathFirstBoundaryCutout
