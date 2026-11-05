/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AdditiveFiberProduct
import Verification.StrictNisnevichInput

/-!
# Chow Witt Fiber Product Input

The ordinary Milnor--Witt coefficient square on every smooth affine
scheme. Its Chow corner is a subgroup of the actual Chow group; the lower
corner is the actual quotient by doubles. The cited fiber-product theorem
is used only under absence of 2-torsion. The first projection is required
to be the given change-of-coefficients map CW → Nis H(I^p).
There is no exchange-variety conclusion among the reference fields.
-/
noncomputable section
namespace Verification.ChowWittFiberProductInput
open CategoryTheory AlgebraicGeometry
variable (C : Type*) [AddCommGroup C]

def doubling : C →+ C := 2 • AddMonoidHom.id C

abbrev modTwo := C ⧸ (doubling C).range

def reduce : C →+ modTwo C := QuotientAddGroup.mk' (doubling C).range

variable {A : Type*}
variable (T : StrictNisnevichInput.Theory A) (k : Type) [Field k]
variable (IP : ℕ → A) (CW CH : Scheme → ℕ → AddCommGrp)

structure Theory where
  comparison : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R] (p : ℕ),
    CW (Spec (CommRingCat.of R)) p →+ T.cohomology (Spec (CommRingCat.of R)) (IP p) p
  reduction : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R] (p : ℕ),
    T.cohomology (Spec (CommRingCat.of R)) (IP p) p →+ modTwo (CH (Spec (CommRingCat.of R)) p)
  chowSubgroup : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R] (p : ℕ),
    AddSubgroup (CH (Spec (CommRingCat.of R)) p)

variable (Q : Theory T k IP CW CH)
variable (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R] (p : ℕ)

def chowReduction : Q.chowSubgroup R p →+ modTwo (CH (Spec (CommRingCat.of R)) p) :=
  (reduce (CH (Spec (CommRingCat.of R)) p)).comp (Q.chowSubgroup R p).subtype

abbrev fiber := AdditiveFiberProduct.group (Q.reduction R p) (chowReduction T k IP CW CH Q R p)

structure Standard where
  fiberEquiv : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R] (p : ℕ),
    Function.Injective (doubling (CH (Spec (CommRingCat.of R)) p)) →
    CW (Spec (CommRingCat.of R)) p ≃+ fiber T k IP CW CH Q R p
  comparison_first : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    (p : ℕ) (h2 : Function.Injective (doubling (CH (Spec (CommRingCat.of R)) p)))
    (x : CW (Spec (CommRingCat.of R)) p),
    (fiberEquiv R p h2 x).val.1 = Q.comparison R p x

variable (S : Standard T k IP CW CH Q)

include S in
theorem comparison_bijective [Subsingleton (CH (Spec (CommRingCat.of R)) p)] :
    Function.Bijective (Q.comparison R p) := by
  have h2 : Function.Injective (doubling (CH (Spec (CommRingCat.of R)) p)) :=
    fun _ _ _ => Subsingleton.elim _ _
  letI : Subsingleton (modTwo (CH (Spec (CommRingCat.of R)) p)) :=
    (QuotientAddGroup.mk'_surjective (doubling (CH (Spec (CommRingCat.of R)) p)).range).subsingleton
  have he := (S.fiberEquiv R p h2).bijective
  have hf := AdditiveFiberProduct.first_bijective
    (Q.reduction R p) (chowReduction T k IP CW CH Q R p)
  have hc := hf.comp he
  have hmap : (AdditiveFiberProduct.first (Q.reduction R p)
      (chowReduction T k IP CW CH Q R p)) ∘ (S.fiberEquiv R p h2) = Q.comparison R p := by
    funext x
    exact S.comparison_first R p h2 x
  rwa [hmap] at hc

def comparisonEquiv [Subsingleton (CH (Spec (CommRingCat.of R)) p)] :
    CW (Spec (CommRingCat.of R)) p ≃+ T.cohomology (Spec (CommRingCat.of R)) (IP p) p :=
  AddEquiv.ofBijective (Q.comparison R p) (comparison_bijective T k IP CW CH Q R p S)

theorem comparisonEquiv_apply [Subsingleton (CH (Spec (CommRingCat.of R)) p)]
    (x : CW (Spec (CommRingCat.of R)) p) :
    comparisonEquiv T k IP CW CH Q R p S x = Q.comparison R p x := rfl

#print axioms doubling
#print axioms modTwo
#print axioms reduce
#print axioms Theory
#print axioms chowReduction
#print axioms fiber
#print axioms Standard
#print axioms comparison_bijective
#print axioms comparisonEquiv
#print axioms comparisonEquiv_apply
end Verification.ChowWittFiberProductInput
