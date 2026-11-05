/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOpenRight

/-!
# Path Open Both

Opening a fixed left endpoint leaves exactly the shorter right-endpoint
path module. This is a quotient calculation for the actual full differential.
-/

namespace Verification.PathOpenBoth

open Classical Verification.PathCochains Verification.PathConfigRecursion
  Verification.PathRhoWords Verification.PathRhoFaces Verification.PathOpenWords
  Verification.PathOpenEmbedding Verification.PathOpenDifferential
  Verification.PathOpenEndpointWords Verification.PathOpenRight
  Verification.PathEndpointTotal Verification.PathEndpointComplex

variable {R : Type*} [CommRing R]

noncomputable def bothProjection (k : R) (n : ℕ) : Total (R := R) n →ₗ[R] Total (R := R) n :=
  (left 0 n).comp (right k n)

theorem restriction_both (k : R) (n : ℕ) :
    (restriction n false).comp (bothProjection k (n+1))=
      (right k n).comp (restriction n false) := by
  apply LinearMap.ext
  intro x
  have hh := LinearMap.congr_fun (restriction_right k n false) x
  simp only [LinearMap.comp_apply] at hh
  simp only [LinearMap.comp_apply]
  rw [← hh]
  funext I
  apply Subtype.ext
  exact left_zero_unprepend_false _

theorem restriction_both_true (k : R) (n : ℕ) :
    (restriction n true).comp (bothProjection k (n+1))=0 := by
  apply LinearMap.ext
  intro x
  funext I
  apply Subtype.ext
  exact left_zero_unprepend_true _

theorem left_extension_false (n : ℕ) :
    (left (0:R) (n+1)).comp (extension n false)=extension n false := by
  apply LinearMap.ext
  intro x
  funext I
  by_cases hI : 1 ∉ I.val
  · apply Subtype.ext
    change Verification.PathLeftEndpoint.projection 0 ((extension n false x) I).val=
      ((extension n false x) I).val
    rw [extension_open n false x ⟨I,hI⟩,Verification.PathLeftEndpoint.projection_prepend]
    simp [Verification.PathRhoEndpoint.evaluation]
  · have hp : 1 ∈ I.val := not_not.mp hI
    apply Subtype.ext
    change Verification.PathLeftEndpoint.projection 0 ((extension n false x) I).val=
      ((extension n false x) I).val
    rw [extension_closed n false x I hp]
    exact map_zero _

theorem both_extension (k : R) (n : ℕ) :
    (bothProjection k (n+1)).comp (extension n false)=(extension n false).comp (right k n) := by
  unfold bothProjection
  rw [LinearMap.comp_assoc,right_extension,← LinearMap.comp_assoc,left_extension_false]

noncomputable def bothRestriction (k : R) (n : ℕ) :
    LinearMap.range (bothProjection k (n+1)) →ₗ[R] LinearMap.range (right k n) :=
  LinearMap.codRestrict _ ((restriction n false).comp (LinearMap.range (bothProjection k (n+1))).subtype)
    (fun x => by
      rcases x.property with ⟨z,hz⟩
      refine ⟨restriction n false z,?_⟩
      change right k n (restriction n false z)=restriction n false x.val
      have hh := LinearMap.congr_fun (restriction_both k n) z
      simp only [LinearMap.comp_apply] at hh
      rw [← hh,hz])

noncomputable def bothSection (k : R) (n : ℕ) :
    LinearMap.range (right k n) →ₗ[R] LinearMap.range (bothProjection k (n+1)) :=
  LinearMap.codRestrict _ ((extension n false).comp (LinearMap.range (right k n)).subtype)
    (fun x => by
      rcases x.property with ⟨z,hz⟩
      refine ⟨extension n false z,?_⟩
      change bothProjection k (n+1) (extension n false z)=extension n false x.val
      have hh := LinearMap.congr_fun (both_extension k n) z
      simp only [LinearMap.comp_apply] at hh
      rw [hh,hz])

theorem bothRestriction_section (k : R) (n : ℕ) :
    (bothRestriction k n).comp (bothSection k n)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change restriction n false (extension n false x.val)=x.val
  rw [restriction_extension,if_pos rfl]

theorem bothRestriction_surjective (k : R) (n : ℕ) : Function.Surjective (bothRestriction k n) := by
  intro x
  exact ⟨bothSection k n x,LinearMap.congr_fun (bothRestriction_section k n) x⟩

theorem bothRestriction_zero_iff (k : R) (n : ℕ)
    (x : LinearMap.range (bothProjection k (n+1))) :
    bothRestriction k n x=0 ↔ ∀ I : Config (n+1), 1 ∉ I.val → x.val I=0 := by
  rw [← projection_zero_iff n x.val]
  have ht : restriction n true x.val=0 := by
    rcases x.property with ⟨z,hz⟩
    have hh := LinearMap.congr_fun (restriction_both_true k n) z
    simpa only [LinearMap.comp_apply,LinearMap.zero_apply,hz] using hh
  constructor
  · intro hx
    funext bit
    cases bit with
    | false => exact congrArg Subtype.val hx
    | true => exact ht
  · intro hx
    apply Subtype.ext
    exact congrFun hx false

theorem bothRestriction_differential (k g ρ : R) (n : ℕ) :
    (bothRestriction k n).comp (imageDifferential (bothProjection k (n+1)) (differential g ρ (n+1)))=
      (imageDifferential (right k n) (differential g ρ n)).comp (bothRestriction k n) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change restriction n false (bothProjection k (n+1) (differential g ρ (n+1) x.val))=
    right k n (differential g ρ n (restriction n false x.val))
  have hq := LinearMap.congr_fun (restriction_both k n) (differential g ρ (n+1) x.val)
  have hd := LinearMap.congr_fun (restriction_differential g ρ n false) x.val
  simp only [LinearMap.comp_apply,LinearMap.smul_apply,phase,Bool.false_eq_true,↓reduceIte,one_smul] at hq hd
  rw [hq,hd]

#print axioms bothProjection
#print axioms restriction_both
#print axioms restriction_both_true
#print axioms left_extension_false
#print axioms both_extension
#print axioms bothRestriction
#print axioms bothSection
#print axioms bothRestriction_section
#print axioms bothRestriction_surjective
#print axioms bothRestriction_zero_iff
#print axioms bothRestriction_differential

end Verification.PathOpenBoth
