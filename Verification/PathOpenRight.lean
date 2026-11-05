/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOpenEndpointWords
import Verification.PathOpenDifferential
import Verification.PathEndpointComplex

/-!
# Path Open Right

The actual right-endpoint quotient has the complete open torus recursion.
All maps are induced from literal path strata and word coordinates.
-/

namespace Verification.PathOpenRight

open Classical Verification.PathCompression Verification.PathCochains Verification.PathRhoFinite
  Verification.PathRhoWords Verification.PathRhoFaces Verification.PathConfigRecursion
  Verification.PathOpenWords Verification.PathOpenEmbedding Verification.PathOpenDifferential
  Verification.PathOpenEndpointWords Verification.PathEndpointTotal Verification.PathEndpointComplex

variable {R : Type*} [CommRing R]

theorem restriction_right (k : R) (n : ℕ) (bit : Bool) :
    (restriction n bit).comp (right k (n+1))=(right k n).comp (restriction n bit) := by
  apply LinearMap.ext
  intro x
  funext I
  apply Subtype.ext
  change unprepend bit (Verification.PathRightEndpoint.projection k (x (openUp n I).val).val)=
    Verification.PathRightEndpoint.projection k (unprepend bit (x (openUp n I).val).val)
  apply (right_unprepend k (available I.val (n+2)).card _ bit _ _).symm
  · exact Finset.card_pos.mpr ⟨0,zero_available I.property (by omega)⟩
  · rw [← openUp_length n I]
    exact (x (openUp n I).val).property

theorem right_extension (k : R) (n : ℕ) (bit : Bool) :
    (right k (n+1)).comp (extension n bit)=(extension n bit).comp (right k n) := by
  apply LinearMap.ext
  intro x
  funext I
  by_cases hI : 1 ∉ I.val
  · apply Subtype.ext
    change Verification.PathRightEndpoint.projection k ((extension n bit x) I).val=
      ((extension n bit (right k n x)) I).val
    rw [extension_open n bit x ⟨I,hI⟩,extension_open n bit (right k n x) ⟨I,hI⟩]
    exact Verification.PathRightEndpoint.projection_prepend k bit _
      (Finset.card_pos.mpr ⟨0,zero_available (openDown n ⟨I,hI⟩).property (by omega)⟩)
      _ (x (openDown n ⟨I,hI⟩)).property
  · have hp : 1 ∈ I.val := not_not.mp hI
    apply Subtype.ext
    change Verification.PathRightEndpoint.projection k ((extension n bit x) I).val=
      ((extension n bit (right k n x)) I).val
    rw [extension_closed n bit x I hp,extension_closed n bit (right k n x) I hp]
    exact map_zero _

noncomputable def rightRestriction (k : R) (n : ℕ) (bit : Bool) :
    LinearMap.range (right k (n+1)) →ₗ[R] LinearMap.range (right k n) :=
  LinearMap.codRestrict _ ((restriction n bit).comp (LinearMap.range (right k (n+1))).subtype)
    (fun x => by
      rcases x.property with ⟨z,hz⟩
      refine ⟨restriction n bit z,?_⟩
      change right k n (restriction n bit z)=restriction n bit x.val
      have hh := LinearMap.congr_fun (restriction_right k n bit) z
      simp only [LinearMap.comp_apply] at hh
      rw [← hh,hz])

noncomputable def rightExtension (k : R) (n : ℕ) (bit : Bool) :
    LinearMap.range (right k n) →ₗ[R] LinearMap.range (right k (n+1)) :=
  LinearMap.codRestrict _ ((extension n bit).comp (LinearMap.range (right k n)).subtype)
    (fun x => by
      rcases x.property with ⟨z,hz⟩
      refine ⟨extension n bit z,?_⟩
      change right k (n+1) (extension n bit z)=extension n bit x.val
      have hh := LinearMap.congr_fun (right_extension k n bit) z
      simp only [LinearMap.comp_apply] at hh
      rw [hh,hz])

noncomputable def rightProjection (k : R) (n : ℕ) :
    LinearMap.range (right k (n+1)) →ₗ[R] (Bool → LinearMap.range (right k n)) :=
  LinearMap.pi (rightRestriction k n)

noncomputable def rightSection (k : R) (n : ℕ) :
    (Bool → LinearMap.range (right k n)) →ₗ[R] LinearMap.range (right k (n+1)) :=
  (rightExtension k n false).comp (LinearMap.proj false)+
    (rightExtension k n true).comp (LinearMap.proj true)

theorem rightProjection_section (k : R) (n : ℕ) :
    (rightProjection k n).comp (rightSection k n)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext bit
  apply Subtype.ext
  change restriction n bit (extension n false (x false).val+extension n true (x true).val)=(x bit).val
  rw [map_add,restriction_extension,restriction_extension]
  cases bit <;> simp

theorem rightProjection_surjective (k : R) (n : ℕ) :
    Function.Surjective (rightProjection k n) := by
  intro x
  exact ⟨rightSection k n x,LinearMap.congr_fun (rightProjection_section k n) x⟩

theorem rightProjection_zero_iff (k : R) (n : ℕ) (x : LinearMap.range (right k (n+1))) :
    rightProjection k n x=0 ↔ ∀ I : Config (n+1), 1 ∉ I.val → x.val I=0 := by
  rw [← projection_zero_iff n x.val]
  constructor
  · intro hx
    funext bit
    exact congrArg Subtype.val (congrFun hx bit)
  · intro hx
    funext bit
    apply Subtype.ext
    exact congrFun hx bit

noncomputable def rightOpenDifferential (k g ρ : R) (n : ℕ) :
    (Bool → LinearMap.range (right k n)) →ₗ[R] (Bool → LinearMap.range (right k n)) :=
  LinearMap.pi (fun bit => phase (-g) bit •
    (imageDifferential (right k n) (differential g ρ n)).comp (LinearMap.proj bit))

theorem rightProjection_differential (k g ρ : R) (n : ℕ) :
    (rightProjection k n).comp (imageDifferential (right k (n+1)) (differential g ρ (n+1)))=
      (rightOpenDifferential k g ρ n).comp (rightProjection k n) := by
  apply LinearMap.ext
  intro x
  funext bit
  apply Subtype.ext
  change restriction n bit (right k (n+1) (differential g ρ (n+1) x.val))=
    phase (-g) bit • right k n (differential g ρ n (restriction n bit x.val))
  have hq := LinearMap.congr_fun (restriction_right k n bit) (differential g ρ (n+1) x.val)
  have hd := LinearMap.congr_fun (restriction_differential g ρ n bit) x.val
  simp only [LinearMap.comp_apply,LinearMap.smul_apply] at hq hd
  rw [hq,hd,map_smul]

#print axioms restriction_right
#print axioms right_extension
#print axioms rightRestriction
#print axioms rightExtension
#print axioms rightProjection
#print axioms rightSection
#print axioms rightProjection_section
#print axioms rightProjection_surjective
#print axioms rightProjection_zero_iff
#print axioms rightOpenDifferential
#print axioms rightProjection_differential

end Verification.PathOpenRight
