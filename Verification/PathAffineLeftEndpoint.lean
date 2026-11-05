/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathAffineIntertwiner

/-!
# Path Affine Left Endpoint

The full affine sign substitution changes an actual constant endpoint
by k ↦ rho+g k and descends through its literal projector relation.
-/

namespace Verification.PathAffineLeftEndpoint

open Classical Verification.PathRhoWords Verification.PathRhoEndpoint
  Verification.PathAffineSigns

variable {R : Type*} [CommRing R] (g ρ : R)

def flipConstant (a : Bool) (k : R) : R := if a then ρ+g*k else k

theorem flipConstant_squared (hg : g*g=1) (hr : (1+g)*ρ=0) (a : Bool) (k : R) :
    flipConstant g ρ a (flipConstant g ρ a k)=k := by
  cases a with
  | false => rfl
  | true =>
    change ρ+g*(ρ+g*k)=k
    linear_combination k*hg+hr

theorem flipConstant_relation (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a : Bool) (k : R) (hk : k*k=ρ*k) :
    flipConstant g ρ a k*flipConstant g ρ a k=ρ*flipConstant g ρ a k := by
  cases a with
  | false => exact hk
  | true =>
    change (ρ+g*k)*(ρ+g*k)=ρ*(ρ+g*k)
    linear_combination k^2*hg+k*hr+hk

theorem prefix_evaluation (a bit : Bool) (k : R) (x : List Bool →₀ R) :
    Verification.PathLeftEndpoint.projection k (prefixMap g ρ a bit x)=
      evaluation (flipConstant g ρ a k) bit • prepend false x := by
  cases a <;> cases bit <;>
    simp only [prefixMap,Bool.false_eq_true,↓reduceIte,LinearMap.add_apply,LinearMap.smul_apply,
      map_add,map_smul,Verification.PathLeftEndpoint.projection_prepend,
      evaluation,Bool.false_eq_true,↓reduceIte,one_smul,smul_smul,flipConstant]
  rw [add_smul]

/-- The original and signed left constant ideals give the same substituted quotient map. -/
theorem left_sign_quotient (a b : Bool) (k : R) :
    (Verification.PathLeftEndpoint.projection k).comp ((signMap g ρ a b).comp
      (Verification.PathLeftEndpoint.projection (flipConstant g ρ a k)))=
        (Verification.PathLeftEndpoint.projection k).comp (signMap g ρ a b) := by
  apply Finsupp.lhom_ext
  intro w r
  have hr : Finsupp.single w r=r • Finsupp.single w (1 : R) := by simp
  rw [hr,map_smul,map_smul]
  congr 1
  change Verification.PathLeftEndpoint.projection k (signMap g ρ a b
      (Verification.PathLeftEndpoint.projection (flipConstant g ρ a k) (Finsupp.single w 1)))=
    Verification.PathLeftEndpoint.projection k (signMap g ρ a b (Finsupp.single w 1))
  cases w with
  | nil => simp only [Verification.PathLeftEndpoint.projection_single,
      Verification.PathLeftEndpoint.projectionColumn,sign_single,signColumn]
  | cons bit tail =>
    rw [← prepend_single,Verification.PathLeftEndpoint.projection_prepend,map_smul,map_smul,
      sign_prepend,sign_prepend,prefix_evaluation,prefix_evaluation]
    simp only [evaluation,Bool.false_eq_true,↓reduceIte,one_smul]

#print axioms flipConstant
#print axioms flipConstant_squared
#print axioms flipConstant_relation
#print axioms prefix_evaluation
#print axioms left_sign_quotient

end Verification.PathAffineLeftEndpoint
