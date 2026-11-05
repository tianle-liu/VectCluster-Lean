/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathWeightedSurvivors

/-!
# Path Zero Weight Index

Weight zero in the actual path basis consists of exactly the empty word
on the empty stratum. It is therefore a single constant summand in chain
degree zero, independent of the positive Milnor--Witt coefficient objects.
-/

namespace Verification.PathZeroWeightIndex

open Verification.PathWords Verification.PathNormalizedBasis Verification.PathEndpointWords
  Verification.PathFirstDegreeCoordinates Verification.PathWeightedSurvivors
  Verification.PathWeightFiltration Verification.PathStratumGrading

def falseWord (n : ℕ) : Word n := ⟨List.replicate n false,by simp⟩

theorem false_of_count (w : List Bool) (h : w.count true=0) : w=List.replicate w.length false := by
  apply List.eq_replicate_length.mpr
  intro b hb
  cases b with
  | false => rfl
  | true => exact ((List.count_eq_zero.mp h) hb).elim

noncomputable def zIndex (n : ℕ) : NormalIndex RightNormal n := (zZeroIndex n (falseWord (n+1))).val
noncomputable def yIndex (a : ℕ) : NormalIndex BothNormal (2*a) := (yZeroIndex a (falseWord (2*a))).val

theorem zIndex_weight (n : ℕ) : weight (zIndex n)=0 := by
  rw [zIndex,zZeroIndex_weight]
  simp [falseWord,List.count_replicate]

theorem yIndex_weight (a : ℕ) : weight (yIndex a)=0 := by
  rw [yIndex,yZeroIndex_weight]
  simp [falseWord,List.count_replicate]

theorem zIndex_degree (n : ℕ) : -degree (zIndex n)=0 := (zZeroIndex n (falseWord (n+1))).property

theorem yIndex_degree (a : ℕ) : -degree (yIndex a)=0 := (yZeroIndex a (falseWord (2*a))).property

theorem weight_zero_degree {B : List Bool → Prop} {n : ℕ} (x : NormalIndex B n)
    (h : weight x=0) : -degree x=0 := by
  change x.1.val.card+x.2.val.count true=0 at h
  change -(x.1.val.card:ℤ)=0
  omega

theorem z_unique (n : ℕ) (x : NormalIndex RightNormal n) (h : weight x=0) : x=zIndex n := by
  obtain ⟨w,hw⟩ := (zZeroIndex n).surjective ⟨x,weight_zero_degree x h⟩
  have hx : x=(zZeroIndex n w).val := (congrArg Subtype.val hw).symm
  rw [hx,zZeroIndex_weight] at h
  have he : w=falseWord (n+1) := by
    apply Subtype.ext
    change w.val=List.replicate (n+1) false
    simpa only [w.property] using false_of_count w.val h
  rw [hx,he]
  rfl

theorem y_unique (a : ℕ) (x : NormalIndex BothNormal (2*a)) (h : weight x=0) : x=yIndex a := by
  obtain ⟨w,hw⟩ := (yZeroIndex a).surjective ⟨x,weight_zero_degree x h⟩
  have hx : x=(yZeroIndex a w).val := (congrArg Subtype.val hw).symm
  rw [hx,yZeroIndex_weight] at h
  have he : w=falseWord (2*a) := by
    apply Subtype.ext
    change w.val=List.replicate (2*a) false
    simpa only [w.property] using false_of_count w.val h
  rw [hx,he]
  rfl

#print axioms falseWord
#print axioms false_of_count
#print axioms zIndex
#print axioms yIndex
#print axioms zIndex_weight
#print axioms yIndex_weight
#print axioms zIndex_degree
#print axioms yIndex_degree
#print axioms weight_zero_degree
#print axioms z_unique
#print axioms y_unique

end Verification.PathZeroWeightIndex
