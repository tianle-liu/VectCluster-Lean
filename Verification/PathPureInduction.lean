/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathZeroPureBases
import Verification.PathOnePureBase
import Verification.PathZPureStep
import Verification.PathYPureStep

/-!
# Path Pure Induction

All-length normalized contractions of the manuscript's actual pure path
chain matrices. The induction uses the proved literal endpoint recursion,
actual first-homology bases, and the constructed finite cone elimination.
-/

namespace Verification.PathPureInduction

open Classical CategoryTheory Verification.PathPureContractionData Verification.PathStratumGrading
  Verification.PathEndpointCoordinates Verification.PathFullComplex

variable {R : Type} [CommRing R]

noncomputable def zData (g : R) (hg : g*g=1) (n : ℕ) :
    Data (fun x => -degree x) (zMatrix g 0 n).transpose :=
  Nat.twoStepInduction (Verification.PathZeroPureBases.zZero g)
    (Verification.PathOnePureBase.zOne g hg) (fun n T U => Verification.PathZPureStep.step g hg n T U) n

noncomputable def yData (g : R) (hg : g*g=1) (m : ℕ) :
    Data (fun x => -degree x) (yMatrix g 0 m).transpose :=
  Nat.rec (Verification.PathZeroPureBases.yZero g)
    (fun m T => Verification.PathYPureStep.step g hg m T (zData g hg (2*m+1))) m

theorem z_vanishing (g : R) (hg : g*g=1) (n : ℕ) (p : ℤ) (hp : p ≠ 0) :
    Limits.IsZero ((zChainComplex g 0 n hg (by simp)).homology p) :=
  Verification.PureContractionTransfer.vanishing _ _ (zData g hg n) p hp

theorem y_vanishing (g : R) (hg : g*g=1) (m : ℕ) (p : ℤ) (hp : p ≠ 0) :
    Limits.IsZero ((yChainComplex g 0 m hg (by simp)).homology p) :=
  Verification.PureContractionTransfer.vanishing _ _ (yData g hg m) p hp

#print axioms zData
#print axioms yData
#print axioms z_vanishing
#print axioms y_vanishing

end Verification.PathPureInduction
