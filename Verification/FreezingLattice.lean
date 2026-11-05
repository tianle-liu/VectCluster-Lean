/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Freezing Lattice

The lattice step of the freezing argument, manuscript.tex:524–538.
We quotient an actual primitive family by its distinguished first member.
Its remaining columns have a constructed left inverse, and saturation passes
to the quotient. No geometric freezing assertion is used as an input.
-/
namespace Verification.FreezingLattice

variable {R M U : Type*} [CommRing R]
variable [AddCommGroup M] [AddCommGroup U] [Module R M] [Module R U]

abbrev firstSpan (b : R × U →ₗ[R] M) : Submodule R M :=
  LinearMap.range (b.comp (LinearMap.inl R R U))

def residualColumns (b : R × U →ₗ[R] M) : U →ₗ[R] (M ⧸ firstSpan b) :=
  (firstSpan b).mkQ.comp (b.comp (LinearMap.inr R R U))

def residualRetraction (b : R × U →ₗ[R] M) (r : M →ₗ[R] R × U)
    (h : r.comp b = LinearMap.id) : (M ⧸ firstSpan b) →ₗ[R] U :=
  (firstSpan b).liftQ ((LinearMap.snd R R U).comp r) (by
    rintro x ⟨a, rfl⟩
    change (r (b (a,0))).2 = 0
    have hx := LinearMap.congr_fun h (a,0)
    exact congrArg Prod.snd hx)

theorem residual_left_inverse (b : R × U →ₗ[R] M) (r : M →ₗ[R] R × U)
    (h : r.comp b = LinearMap.id) :
    (residualRetraction b r h).comp (residualColumns b) = LinearMap.id := by
  ext u
  change (r (b (0,u))).2 = u
  exact congrArg Prod.snd (LinearMap.congr_fun h (0,u))

theorem residual_injective (b : R × U →ₗ[R] M) (r : M →ₗ[R] R × U)
    (h : r.comp b = LinearMap.id) : Function.Injective (residualColumns b) := by
  apply Function.LeftInverse.injective (g := residualRetraction b r h)
  intro u
  exact LinearMap.congr_fun (residual_left_inverse b r h) u

/-- Saturation is the actual divisibility property of a lattice submodule. -/
def Saturated (T : Submodule R M) : Prop :=
  ∀ a : R, a ≠ 0 → ∀ x : M, a • x ∈ T → x ∈ T

theorem quotient_preserves_saturation (S T : Submodule R M) (hST : S ≤ T)
    (hT : Saturated T) : Saturated (T.map S.mkQ) := by
  intro a ha x
  refine Submodule.Quotient.induction_on S x ?_
  intro m hm
  change a • S.mkQ m ∈ T.map S.mkQ at hm
  obtain ⟨t, ht, heq⟩ := hm
  have hd : t - a • m ∈ S := by
    apply (Submodule.Quotient.eq S).mp
    simpa only [map_smul] using heq
  have ham : a • m ∈ T := by
    have := T.sub_mem ht (hST hd)
    simpa only [sub_sub_cancel] using this
  exact ⟨m, hT a ha m ham, rfl⟩

/-- The precise double quotient appearing in the article. -/
def freezingQuotient (S T : Submodule R M) (hST : S ≤ T) :
    ((M ⧸ S) ⧸ T.map S.mkQ) ≃ₗ[R] (M ⧸ T) :=
  Submodule.quotientQuotientEquivQuotient S T hST

#print axioms residualRetraction
#print axioms residual_left_inverse
#print axioms residual_injective
#print axioms quotient_preserves_saturation
#print axioms freezingQuotient
end Verification.FreezingLattice

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.FreezingLattice.Saturated
#print axioms Verification.FreezingLattice.firstSpan
#print axioms Verification.FreezingLattice.residualColumns
