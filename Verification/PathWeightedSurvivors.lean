/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TerminalMatrixProjection
import Verification.PathSignedRepresentatives
import Verification.PathPureSpecialization
import Verification.PathGradedCancellation

/-!
# Path Weighted Survivors

The literal pure projector has a proved basis in precisely the manuscript's
surviving weights. Every basis vector is the projection of its original signed
normal word; this supplies explicit rectangular coordinates for realization.
-/

namespace Verification.PathWeightedSurvivors

open Verification.PathWords Verification.PathCokernel Verification.PathFirstDegreeCoordinates
  Verification.PathFirstDegreeBoundary Verification.PathFirstHomology
  Verification.PathEndpointWords Verification.PathEndpointCoordinates Verification.PathStratumGrading
  Verification.PathPureContractionData Verification.PathSignedRepresentatives
  Verification.FinitePerturbation Verification.PathWeightFiltration
  Verification.PathFirstBoundaryCutout Verification.DegreeBasisCoordinates

variable {R : Type} [CommRing R]

noncomputable def zEquiv (g : R) (n : ℕ)
    (T : Data (fun x=>-degree x) (zMatrix g 0 n).transpose) :
    Verification.PathActualFirstCokernel.ZCokernel g n ≃ₗ[R]
      Verification.SurvivorBaseChange.fixedModule (pureProjection (zMatrix g 0 n).transpose T.homotopy) :=
  (zCokernelEquiv g n).symm.trans (Verification.TerminalMatrixProjection.quotientEquiv _ _ T
    (by intro i;change -(i.1.val.card:ℤ)≤0;omega))

noncomputable def yEquiv (g : R) (a : ℕ)
    (T : Data (fun x=>-degree x) (yMatrix g 0 a).transpose) :
    Verification.PathActualFirstCokernel.YCokernel g a ≃ₗ[R]
      Verification.SurvivorBaseChange.fixedModule (pureProjection (yMatrix g 0 a).transpose T.homotopy) :=
  (yCokernelEquiv g a).symm.trans (Verification.TerminalMatrixProjection.quotientEquiv _ _ T
    (by intro i;change -(i.1.val.card:ℤ)≤0;omega))

theorem zEquiv_mk (g : R) (n : ℕ)
    (T : Data (fun x=>-degree x) (zMatrix g 0 n).transpose) (x : Word (n+1) →₀ R) :
    (zEquiv g n T ((LinearMap.range (zBoundary g n)).mkQ x)).val=
      (pureProjection (zMatrix g 0 n).transpose T.homotopy).mulVec ((zZeroCoordinates n).symm x).val := by
  exact Verification.TerminalMatrixProjection.quotientEquiv_mk _ _ T
    (by intro i;change -(i.1.val.card:ℤ)≤0;omega) ((zZeroCoordinates n).symm x)

theorem yEquiv_mk (g : R) (a : ℕ)
    (T : Data (fun x=>-degree x) (yMatrix g 0 a).transpose) (x : Word (2*a) →₀ R) :
    (yEquiv g a T ((LinearMap.range (yBoundary g a)).mkQ x)).val=
      (pureProjection (yMatrix g 0 a).transpose T.homotopy).mulVec ((yZeroCoordinates a).symm x).val := by
  exact Verification.TerminalMatrixProjection.quotientEquiv_mk _ _ T
    (by intro i;change -(i.1.val.card:ℤ)≤0;omega) ((yZeroCoordinates a).symm x)

noncomputable def zBasis (g : R) (hg : g*g=1) (n : ℕ)
    (T : Data (fun x=>-degree x) (zMatrix g 0 n).transpose) :=
  (PathSignedRepresentatives.zBasis g hg n).map (zEquiv g n T)

noncomputable def yBasis (g : R) (hg : g*g=1) (a : ℕ)
    (T : Data (fun x=>-degree x) (yMatrix g 0 a).transpose) :=
  (PathSignedRepresentatives.yBasis g hg a).map (yEquiv g a T)

theorem zBasis_entry (g : R) (hg : g*g=1) (n : ℕ)
    (T : Data (fun x=>-degree x) (zMatrix g 0 n).transpose) (k : Weight false (n+1)) (i) :
    (zBasis g hg n T k).val i=
      pureProjection (zMatrix g 0 n).transpose T.homotopy i (zZeroIndex n (representative k)).val *
        Verification.PathSignNormalization.wordScale g (n+1) (representative k) := by
  rw [zBasis,Basis.map_apply,zBasis_representative]
  rw [zEquiv_mk,representativeVector_single]
  change ((pureProjection (zMatrix g 0 n).transpose T.homotopy).mulVec
    (((basisEquiv _ 0 (zZeroIndex n)).symm (Finsupp.single _ _)).val)) i=_
  rw [basis_inverse_single,Matrix.mulVec_single]
  rfl

theorem yBasis_entry (g : R) (hg : g*g=1) (a : ℕ)
    (T : Data (fun x=>-degree x) (yMatrix g 0 a).transpose) (k : Weight true (2*a)) (i) :
    (yBasis g hg a T k).val i=
      pureProjection (yMatrix g 0 a).transpose T.homotopy i (yZeroIndex a (representative k)).val *
        Verification.PathSignNormalization.wordScale g (2*a) (representative k) := by
  rw [yBasis,Basis.map_apply,yBasis_representative]
  rw [yEquiv_mk,representativeVector_single]
  change ((pureProjection (yMatrix g 0 a).transpose T.homotopy).mulVec
    (((basisEquiv _ 0 (yZeroIndex a)).symm (Finsupp.single _ _)).val)) i=_
  rw [basis_inverse_single,Matrix.mulVec_single]
  rfl

theorem zZeroIndex_weight (n : ℕ) (w : Word (n+1)) :
    PathWeightFiltration.weight (zZeroIndex n w).val=w.val.count true := by
  change 0+(w.val++[false]).count true=w.val.count true
  simp

theorem yZeroIndex_weight (a : ℕ) (w : Word (2*a)) :
    PathWeightFiltration.weight (yZeroIndex a w).val=w.val.count true := by
  change 0+(false::(w.val++[false])).count true=w.val.count true
  simp

#print axioms zEquiv
#print axioms yEquiv
#print axioms zEquiv_mk
#print axioms yEquiv_mk
#print axioms zBasis
#print axioms yBasis
#print axioms zBasis_entry
#print axioms yBasis_entry
#print axioms zZeroIndex_weight
#print axioms yZeroIndex_weight

end Verification.PathWeightedSurvivors
