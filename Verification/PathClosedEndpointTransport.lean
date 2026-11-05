/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathClosedSignedComplex
import Verification.PathBothSignQuotients

/-!
# Path Closed Endpoint Transport

Endpoint projections commute with the literal closed extension and
restriction, giving genuine maps of their image modules.
-/

namespace Verification.PathClosedEndpointTransport

open Classical Verification.PathCompression Verification.PathCochains Verification.PathRhoFinite
  Verification.PathConfigRecursion Verification.PathClosedEmbedding Verification.PathClosedDifferential
  Verification.PathClosedSignedComplex Verification.PathEndpointTotal Verification.PathEndpointComplex

variable {R : Type*} [CommRing R]
variable (P : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R))
variable (hP : ∀ n x, x ∈ layer (R := R) n → P x ∈ layer n)

theorem totalMap_extension (n : ℕ) :
    (totalMap P hP (n+2)).comp (extension n)=(extension n).comp (totalMap P hP n) := by
  apply LinearMap.ext
  intro x
  funext I
  apply Subtype.ext
  change P ((extension n x) I).val=((extension n (totalMap P hP n x)) I).val
  by_cases hI : 1 ∈ I.val
  · rw [extension_closed n x ⟨I,hI⟩,extension_closed n _ ⟨I,hI⟩]
    rfl
  · rw [extension_open n x I hI,extension_open n _ I hI]
    exact map_zero _

theorem totalMap_restriction (n : ℕ) :
    (restriction n).comp (totalMap P hP (n+2))=(totalMap P hP n).comp (restriction n) := rfl

theorem totalMap_twist (g : R) (n : ℕ) :
    (totalMap P hP n).comp (degreeTwist g n)=(degreeTwist g n).comp (totalMap P hP n) := by
  apply LinearMap.ext
  intro x
  funext I
  apply Subtype.ext
  change P (g^I.val.card • (x I).val)=g^I.val.card • P (x I).val
  exact map_smul P _ _

noncomputable def projectedExtension (n : ℕ) :
    LinearMap.range (totalMap P hP n) →ₗ[R] LinearMap.range (totalMap P hP (n+2)) :=
  LinearMap.codRestrict _ ((extension n).comp (LinearMap.range (totalMap P hP n)).subtype)
    (fun x => by
      obtain ⟨y,hy⟩ := x.property
      refine ⟨extension n y,?_⟩
      change totalMap P hP (n+2) (extension n y)=extension n x.val
      rw [show totalMap P hP (n+2) (extension n y)=extension n (totalMap P hP n y) from
        LinearMap.congr_fun (totalMap_extension P hP n) y,hy])

noncomputable def projectedRestriction (n : ℕ) :
    LinearMap.range (totalMap P hP (n+2)) →ₗ[R] LinearMap.range (totalMap P hP n) :=
  LinearMap.codRestrict _ ((restriction n).comp (LinearMap.range (totalMap P hP (n+2))).subtype)
    (fun x => by
      obtain ⟨y,hy⟩ := x.property
      refine ⟨restriction n y,?_⟩
      change totalMap P hP n (restriction n y)=restriction n x.val
      rw [← show restriction n (totalMap P hP (n+2) y)=totalMap P hP n (restriction n y) from
        LinearMap.congr_fun (totalMap_restriction P hP n) y,hy])

theorem projectedRestriction_extension (n : ℕ) :
    (projectedRestriction P hP n).comp (projectedExtension P hP n)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (restriction_extension n) x.val

theorem projectedExtension_restriction (n : ℕ) (x : LinearMap.range (totalMap P hP (n+2)))
    (hx : x.val ∈ closedSupport n) : projectedExtension P hP n (projectedRestriction P hP n x)=x := by
  apply Subtype.ext
  exact extension_restriction n x.val ((mem_closedSupport n x.val).mp hx)

theorem projectedExtension_injective (n : ℕ) : Function.Injective (projectedExtension P hP n) := by
  intro x y h
  apply Subtype.ext
  apply extension_injective n
  exact congrArg Subtype.val h

/-- The image is exactly the original endpoint module's closed-stratum part. -/
theorem projectedExtension_range (n : ℕ) (x : LinearMap.range (totalMap P hP (n+2))) :
    x ∈ LinearMap.range (projectedExtension P hP n) ↔ x.val ∈ closedSupport n := by
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨y.val,rfl⟩
  · intro hx
    exact ⟨projectedRestriction P hP n x,projectedExtension_restriction P hP n x hx⟩

/-- No endpoint parameter assumption is needed for this literal projected block identity. -/
theorem projectedExtension_differential (g ρ : R) (n : ℕ) :
    (imageDifferential (totalMap P hP (n+2)) (differential g ρ (n+2))).comp
      (projectedExtension P hP n)=
        (projectedExtension P hP n).comp
          (g • imageDifferential (totalMap P hP n) (differential g ρ n)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change totalMap P hP (n+2) (differential g ρ (n+2) (extension n x.val))=
    extension n (g • totalMap P hP n (differential g ρ n x.val))
  have hd := LinearMap.congr_fun (differential_extension g ρ n) x.val
  change differential g ρ (n+2) (extension n x.val)=extension n (g • differential g ρ n x.val) at hd
  rw [hd]
  have hp := LinearMap.congr_fun (totalMap_extension P hP n) (g • differential g ρ n x.val)
  change totalMap P hP (n+2) (extension n (g • differential g ρ n x.val))=
    extension n (totalMap P hP n (g • differential g ρ n x.val)) at hp
  rw [hp,map_smul]

#print axioms totalMap_extension
#print axioms totalMap_restriction
#print axioms totalMap_twist
#print axioms projectedExtension
#print axioms projectedRestriction
#print axioms projectedRestriction_extension
#print axioms projectedExtension_restriction
#print axioms projectedExtension_injective
#print axioms projectedExtension_range
#print axioms projectedExtension_differential

end Verification.PathClosedEndpointTransport
