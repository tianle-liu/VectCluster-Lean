/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRhoWords

/-!
# Path Affine Signs

The complete Milnor--Witt sign substitution e ↦ rho+g e on actual
arbitrary-length word modules, with period-two coordinate sign choices.
-/

namespace Verification.PathAffineSigns

open Classical Verification.PathRhoWords

variable {R : Type*} [CommRing R] (g ρ : R)

/-- First-coordinate substitution; a selected symbol expands into its constant and selected terms. -/
noncomputable def prefixMap (s bit : Bool) : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R) :=
  if bit then (if s then ρ • prepend false+g • prepend true else prepend true) else prepend false

noncomputable def signColumn : Bool → Bool → List Bool → (List Bool →₀ R)
  | _, _, [] => Finsupp.single [] 1
  | a, b, bit::tail => prefixMap g ρ a bit (signColumn b a tail)

noncomputable def signMap (a b : Bool) : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R) :=
  Finsupp.linearCombination R (signColumn g ρ a b)

theorem sign_single (a b : Bool) (w : List Bool) :
    signMap g ρ a b (Finsupp.single w 1)=signColumn g ρ a b w := by
  simp only [signMap,Finsupp.linearCombination_single,one_smul]

theorem sign_prepend (a b bit : Bool) (x : List Bool →₀ R) :
    signMap g ρ a b (prepend bit x)=prefixMap g ρ a bit (signMap g ρ b a x) := by
  have hh : (signMap g ρ a b).comp (prepend bit)=
      (prefixMap g ρ a bit).comp (signMap g ρ b a) := by
    apply Finsupp.lhom_ext
    intro w r
    have hr : Finsupp.single w r=r • Finsupp.single w (1 : R) := by simp
    rw [hr,map_smul,map_smul]
    congr 1
    simp only [LinearMap.comp_apply,prepend_single,sign_single,signColumn]
  exact congrArg (fun f : _ →ₗ[R] _ => f x) hh

/-- The complete affine prefixMap substitution is its own inverse under the formal relations. -/
theorem sign_prefix (hg : g*g=1) (hr : (1+g)*ρ=0) (a b bit : Bool) (x : List Bool →₀ R) :
    signMap g ρ a b (prefixMap g ρ a bit x)=prepend bit (signMap g ρ b a x) := by
  have hρ : ρ+g*ρ=0 := by simpa only [add_mul,one_mul] using hr
  cases a <;> cases bit <;>
    simp only [prefixMap,Bool.false_eq_true,↓reduceIte,LinearMap.add_apply,LinearMap.smul_apply,
      map_add,map_smul,sign_prepend,prefixMap,Bool.false_eq_true,↓reduceIte,
      LinearMap.add_apply,LinearMap.smul_apply,smul_add,smul_smul]
  rw [← add_assoc,← add_smul,hρ,hg,zero_smul,one_smul,zero_add]

/-- A genuine involution on every finite or unrestricted original word vector. -/
theorem sign_squared (hg : g*g=1) (hr : (1+g)*ρ=0) (a b : Bool) :
    (signMap g ρ a b).comp (signMap g ρ a b)=LinearMap.id := by
  have hc (w : List Bool) : ∀ a b, signMap g ρ a b (signMap g ρ a b (Finsupp.single w 1))=
      Finsupp.single w 1 := by
    induction w with
    | nil => intro a b; simp only [sign_single,signColumn,sign_single,signColumn]
    | cons bit tail ih =>
      intro a b
      rw [← prepend_single,sign_prepend,sign_prefix g ρ hg hr,ih,prepend_single]
  apply Finsupp.lhom_ext
  intro w r
  have hr' : Finsupp.single w r=r • Finsupp.single w (1 : R) := by simp
  rw [hr',map_smul,map_smul]
  congr 1
  exact hc w a b

noncomputable def signEquiv (hg : g*g=1) (hr : (1+g)*ρ=0) (a b : Bool) :
    (List Bool →₀ R) ≃ₗ[R] (List Bool →₀ R) :=
  LinearEquiv.ofLinear (signMap g ρ a b) (signMap g ρ a b)
    (sign_squared g ρ hg hr a b) (sign_squared g ρ hg hr a b)

#print axioms prefixMap
#print axioms signColumn
#print axioms signMap
#print axioms sign_single
#print axioms sign_prepend
#print axioms sign_prefix
#print axioms sign_squared
#print axioms signEquiv

end Verification.PathAffineSigns
