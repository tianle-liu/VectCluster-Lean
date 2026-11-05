/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SevenfoldCycleParameter
import Verification.ModuleHomologyZeroIncoming
import Verification.GraphChainKernelCoordinates

/-!
# Sevenfold Actual Homology

The genuine induced independence-chain homology in degree minus two
is the integral square-cycle parameter module.
-/
noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.SevenfoldActualHomology
open CategoryTheory
open Verification.SevenfoldGraphFreeness Verification.SevenfoldActualCycles
open Verification.GraphChainMatrix
attribute [local instance 2000] ModuleCat.isModule
variable (T : Finset (Fin 5))

def kernelIso : LinearMap.ker ((chainComplex (R := ℤ) graph T).d (-2) (-1)).hom ≃ₗ[ℤ]
    LinearMap.ker (delta T) := by
  exact GraphChainKernelCoordinates.equiv graph T inferInstance inferInstance (-2) (-1) (by decide)

def equiv : (chainComplex (R := ℤ) graph T).homology (-2) ≃ₗ[ℤ]
    SevenfoldCycleParameter.parameters T := by
  let C := chainComplex (R := ℤ) graph T
  let S := C.sc' (-3) (-2) (-1)
  letI : Subsingleton S.X₁ := term_minus_three T
  exact ((C.homologyIsoSc' (-3) (-2) (-1) (by simp) (by simp)).toLinearEquiv).trans
    ((ModuleHomologyZeroIncoming.equiv S).trans
      ((kernelIso T).trans ((kernelEquiv T).trans (SevenfoldCycleParameter.equiv T))))

theorem rank : Module.finrank ℤ ((chainComplex (R := ℤ) graph T).homology (-2)) =
    if SevenfoldCycleSupport.whole T then 1 else 0 := by
  rw [(equiv T).finrank_eq]
  split_ifs with h
  · rw [SevenfoldCycleParameter.top T h]
    exact (Submodule.topEquiv : (⊤ : Submodule ℤ ℤ) ≃ₗ[ℤ] ℤ).finrank_eq.trans
      (Module.finrank_self ℤ)
  · rw [SevenfoldCycleParameter.bot T h]
    simp

#print axioms kernelIso
#print axioms equiv
#print axioms rank
end Verification.SevenfoldActualHomology
