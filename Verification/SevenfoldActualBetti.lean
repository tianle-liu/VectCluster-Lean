/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SevenfoldActualHomology
import Verification.GraphWeightedChainBetti

/-!
# Sevenfold Actual Betti

The actual weighted chain-Betti exponent in degree two is two. Both
nonzero summands come from actual induced subgraphs containing the square.
-/
noncomputable section
open scoped Classical
set_option maxHeartbeats 800000
namespace Verification.SevenfoldActualBetti
open Verification.SevenfoldExchangeMatrix Verification.SevenfoldGraphFreeness
attribute [local instance 2000] ModuleCat.isModule

theorem whole_iff : ∀ T : Finset (Fin 5), SevenfoldCycleSupport.whole T ↔
    T={0,1,2,3} ∨ T=Finset.univ := by
  unfold SevenfoldCycleSupport.whole
  decide

theorem multiplicity_whole (T : Finset (Fin 5)) (h : SevenfoldCycleSupport.whole T) :
    GraphBlockMultiplicity.multiplicity color T=1 := by
  have he : T.image color=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro a
    fin_cases a
    · exact Finset.mem_image.mpr ⟨0,h (by decide),rfl⟩
    · exact Finset.mem_image.mpr ⟨2,h (by decide),rfl⟩
  simp only [GraphBlockMultiplicity.multiplicity,GraphBlockMultiplicity.missing,he,
    Finset.sdiff_self,Finset.prod_empty]

theorem weighted : (∑ T : Finset (Fin 5), GraphBlockMultiplicity.multiplicity color T *
    (if SevenfoldCycleSupport.whole T then 1 else 0)) = 2 := by
  have he (T : Finset (Fin 5)) : GraphBlockMultiplicity.multiplicity color T *
      (if SevenfoldCycleSupport.whole T then 1 else 0) =
      if T={0,1,2,3} then 1 else if T=Finset.univ then 1 else 0 := by
    by_cases h : SevenfoldCycleSupport.whole T
    · rw [if_pos h,mul_one,multiplicity_whole T h]
      rcases (whole_iff T).mp h with rfl | rfl <;> simp
    · have hn := mt (whole_iff T).mpr h
      simp only [not_or] at hn
      simp [h,hn.1,hn.2]
  simp_rw [he]
  have hi (T : Finset (Fin 5)) : (if T={0,1,2,3} then 1 else if T=Finset.univ then 1 else 0) =
      (if T={0,1,2,3} then 1 else 0)+(if T=Finset.univ then 1 else 0) := by
    by_cases h : T={0,1,2,3}
    · subst T
      simp [show ({0,1,2,3} : Finset (Fin 5)) ≠ Finset.univ from by decide]
    · simp [h]
  simp_rw [hi]
  rw [Finset.sum_add_distrib]
  simp

theorem exponent : GraphWeightedChainBetti.exponent graph color 2=2 := by
  unfold GraphWeightedChainBetti.exponent
  calc
    _ = ∑ T : Finset (Fin 5), GraphBlockMultiplicity.multiplicity color T *
        (if SevenfoldCycleSupport.whole T then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro T _
      congr 1
      · congr
      · exact SevenfoldActualHomology.rank T
    _ = 2 := weighted

#print axioms whole_iff
#print axioms multiplicity_whole
#print axioms weighted
#print axioms exponent
end Verification.SevenfoldActualBetti
