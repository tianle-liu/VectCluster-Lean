/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ModuleGrothendieck
import Verification.ProjectiveRankCriterion

/-!
# Rank From Cartan

Transfer an actual coherent G_0 structure-sheaf generator through
the actual Cartan map to prove that the already constructed field-rank
map on finite-projective K_0 is bijective.
-/
noncomputable section
namespace Verification.RankFromCartan
open Verification.ProjectiveClasses Verification.ProjectiveRankCriterion
variable (A k : Type) [CommRing A] [Field k] [Algebra A k]

theorem cartan_unit : ModuleGrothendieck.cartan A (unitClass A)=
    ModuleGrothendieck.classOf A (ModuleGrothendieck.of A A) := by
  rw [unitClass,ModuleGrothendieck.cartan_class]
  exact ModuleGrothendieck.iso_class A _ _ (LinearEquiv.funUnique (Fin 1) A A)

theorem rank_unit : ProjectiveFieldRank.rankMap A k (unitClass A)=1 :=
  ProjectiveFieldRank.rankMap_free A k 1

theorem rank_bijective
    (hc : Function.Injective (ModuleGrothendieck.cartan A))
    (hg : Function.Surjective (fun z : ℤ => z • ModuleGrothendieck.classOf A (ModuleGrothendieck.of A A))) :
    Function.Bijective (ProjectiveFieldRank.rankMap A k) := by
  have hrep (a : Completion A) : ∃ z : ℤ,a=z • unitClass A := by
    obtain ⟨z,hz⟩ := hg (ModuleGrothendieck.cartan A a)
    refine ⟨z,hc ?_⟩
    rw [map_zsmul,cartan_unit]
    exact hz.symm
  have hr (z : ℤ) : ProjectiveFieldRank.rankMap A k (z • unitClass A)=z := by
    rw [map_zsmul,rank_unit]
    simp
  constructor
  · intro a b hab
    obtain ⟨z,rfl⟩ := hrep a
    obtain ⟨w,rfl⟩ := hrep b
    rw [hr,hr] at hab
    rw [hab]
  · intro z
    exact ⟨z • unitClass A,hr z⟩

#print axioms cartan_unit
#print axioms rank_unit
#print axioms rank_bijective
end Verification.RankFromCartan
