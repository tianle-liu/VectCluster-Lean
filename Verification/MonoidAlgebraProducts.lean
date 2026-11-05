/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Algebra.Pi

/-!
# Monoid Algebra Products

Coefficient transport and finite products of actual monoid algebras.
This turns the finite separable-field decomposition of a Smith factor into
an actual product of Laurent coordinate rings over those fields.
-/
noncomputable section
namespace Verification.MonoidAlgebraProducts
open MonoidAlgebra
variable {R A B G : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [CommMonoid G]

def coefficientMap (f : A →ₐ[R] B) : MonoidAlgebra A G →ₐ[R] MonoidAlgebra B G :=
  liftNCAlgHom ((singleOneAlgHom : B →ₐ[R] MonoidAlgebra B G).comp f)
    (of B G) (fun _ _ => Commute.all _ _)

theorem coefficientMap_single (f : A →ₐ[R] B) (g : G) (a : A) :
    coefficientMap f (Finsupp.single g a) = Finsupp.single g (f a) := by
  change liftNC _ _ (Finsupp.single g a) = _
  rw [liftNC_single]
  change (MonoidAlgebra.single (1 : G) (f a)) * (MonoidAlgebra.single g (1 : B)) = _
  simp only [single_mul_single, one_mul, mul_one]

theorem coefficientMap_apply (f : A →ₐ[R] B) (p : MonoidAlgebra A G) (g : G) :
    coefficientMap f p g = f (p g) := by
  classical
  induction p using Finsupp.induction with
  | zero => simp
  | single_add a c p _ _ ih =>
    rw [map_add, coefficientMap_single]
    change (Finsupp.single a (f c)) g + coefficientMap f p g =
      f ((Finsupp.single a c) g + p g)
    rw [map_add, ih]
    by_cases h : a = g
    · subst a
      simp
    · simp [Finsupp.single_apply, h, Ne.symm h]

def coefficientEquiv (e : A ≃ₐ[R] B) : MonoidAlgebra A G ≃ₐ[R] MonoidAlgebra B G :=
  AlgEquiv.ofAlgHom (coefficientMap e.toAlgHom) (coefficientMap e.symm.toAlgHom)
    (by
      apply AlgHom.ext
      intro p
      apply Finsupp.ext
      intro g
      change coefficientMap e.toAlgHom (coefficientMap e.symm.toAlgHom p) g = p g
      rw [coefficientMap_apply, coefficientMap_apply]
      exact e.apply_symm_apply (p g))
    (by
      apply AlgHom.ext
      intro p
      apply Finsupp.ext
      intro g
      change coefficientMap e.symm.toAlgHom (coefficientMap e.toAlgHom p) g = p g
      rw [coefficientMap_apply, coefficientMap_apply]
      exact e.symm_apply_apply (p g))

variable (R G) {J : Type*} (S : J → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]

def productMap : MonoidAlgebra (∀ i, S i) G →ₐ[R] ∀ i, MonoidAlgebra (S i) G :=
  Pi.algHom R _ (fun i => coefficientMap (Pi.evalAlgHom R S i))

theorem productMap_apply (p : MonoidAlgebra (∀ i, S i) G) (i : J) (g : G) :
    productMap R G S p i g = p g i := coefficientMap_apply _ p g

theorem productMap_injective : Function.Injective (productMap R G S) := by
  intro p q h
  apply Finsupp.ext
  intro g
  funext i
  simpa only [productMap_apply] using congrArg (fun f => f i g) h

variable [Fintype J]

def productInverse (p : ∀ i, MonoidAlgebra (S i) G) : MonoidAlgebra (∀ i, S i) G := by
  classical
  exact ∑ i, (p i).sum (fun g a => Finsupp.single g (Pi.single i a))

omit [CommMonoid G] in
theorem productInverse_apply (p : ∀ i, MonoidAlgebra (S i) G) (g : G) (i : J) :
    productInverse G S p g i = p i g := by
  classical
  change (∑ a, (p a).sum (fun h c => Finsupp.single h (Pi.single a c)) :
    G →₀ (∀ a, S a)) g i = p i g
  simp only [Finsupp.finset_sum_apply, Finset.sum_apply, Finsupp.sum,
    Finsupp.single_apply]
  simp only [ite_apply, Pi.zero_apply]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, eq_comm, Finsupp.mem_support_iff]
  symm
  rw [Finset.sum_eq_single i]
  · by_cases h : 0 = p i g <;> simp [h, eq_comm]
  · intro a _ hai
    by_cases h : 0 = p a g <;> simp [h, Pi.single_eq_of_ne (Ne.symm hai)]
  · simp

theorem productMap_surjective : Function.Surjective (productMap R G S) := by
  intro p
  refine ⟨productInverse G S p, ?_⟩
  funext i
  apply Finsupp.ext
  intro g
  rw [productMap_apply, productInverse_apply]

def productEquiv : MonoidAlgebra (∀ i, S i) G ≃ₐ[R] ∀ i, MonoidAlgebra (S i) G :=
  AlgEquiv.ofBijective (productMap R G S)
    ⟨productMap_injective R G S, productMap_surjective R G S⟩

#print axioms coefficientMap
#print axioms coefficientMap_single
#print axioms coefficientMap_apply
#print axioms coefficientEquiv
#print axioms productMap
#print axioms productMap_apply
#print axioms productMap_injective
#print axioms productInverse
#print axioms productInverse_apply
#print axioms productMap_surjective
#print axioms productEquiv
end Verification.MonoidAlgebraProducts
