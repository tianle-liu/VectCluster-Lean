/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphDegreeDualCoordinates

/-!
# Graph Chain Cochain Betti

The exponent computed from the actual independence cochains is
the manuscript's reduced chain-homology Betti number in degree p-1.
The integer chain model places that augmented chain degree at -p.
-/
noncomputable section
open scoped Classical
namespace Verification.GraphChainCochainBetti
open CategoryTheory
open Verification.GraphCoverGrading Verification.GraphChainMatrix
open Verification.GraphDegreeDualCoordinates
attribute [local instance 2000] ModuleCat.isModule
variable {V C : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) (c : V → C) (T : Finset V)

def shortIso (p : ℕ) (hp : 0 < p) :
    (GraphTensorTF.integral G c T).sc' (p-1) p (p+1) ≅
      (dualComplex G T).sc' ((p-1:ℕ):ℤ) (p:ℤ) ((p+1:ℕ):ℤ) :=
  ShortComplex.isoMk (degreeEquiv G c T (p-1)).toModuleIso
    (degreeEquiv G c T p).toModuleIso (degreeEquiv G c T (p+1)).toModuleIso
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (differential G c T (p-1) p (by omega) x).symm)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (differential G c T p (p+1) rfl x).symm)

def homologyEquiv (p : ℕ) (hp : 0 < p) :
    (GraphTensorTF.integral G c T).homology p ≃ₗ[ℤ] (dualComplex G T).homology (p:ℤ) :=
  ((GraphTensorTF.integral G c T).homologyIsoSc' (p-1) p (p+1)
      ((ComplexShape.up ℕ).prev_eq' (by change p-1+1=p; omega))
      ((ComplexShape.up ℕ).next_eq' rfl) ≪≫
    ShortComplex.homologyMapIso (shortIso G c T p hp) ≪≫
      ((dualComplex G T).homologyIsoSc' ((p-1:ℕ):ℤ) (p:ℤ) ((p+1:ℕ):ℤ)
        (by simp; omega) (by simp)).symm).toLinearEquiv

theorem betti (p : ℕ) (hp : 0 < p) : GraphTensorTF.betti G c T p=
    Module.finrank ℤ ((chainComplex (R:=ℤ) G T).homology (-(p:ℤ))) := by
  have he := (homologyEquiv G c T p hp).finrank_eq
  have hr := IntegerGradedTransposeRank.homology_rank (degree G T) (chainMatrix (R:=ℤ) G T)
    (chainMatrix_degree G T) (chainMatrix_square G T) (-(p:ℤ))
  rw [neg_neg] at hr
  exact he.trans hr.symm

#print axioms shortIso
#print axioms homologyEquiv
#print axioms betti
end Verification.GraphChainCochainBetti
