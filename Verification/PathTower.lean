/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathPresentation
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Path Tower

Universal maps from the actual path quotient over a smaller ground ring,
without imposing an extra coefficient-algebra structure on the target.
-/
noncomputable section
namespace Verification.PathTower
open MvPolynomial Verification.PathPresentation
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] {n : ℕ}
attribute [local instance] MvPolynomial.algebraMvPolynomial

def liftTower (f : S →ₐ[R] T) (a b : S) (xx yy : Fin n → T)
    (h : Equations (f a) (f b) xx yy) : PathAlgebra n a b →ₐ[R] T :=
  Ideal.Quotient.liftₐ (relations n a b) (aevalTower f (Sum.elim xx yy)) (by
    change relations n a b ≤ RingHom.ker (aevalTower f (Sum.elim xx yy)).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change aevalTower f (Sum.elim xx yy) (relation a b i) = 0
    simp only [relation, map_sub, map_mul, boundary_map (aevalTower f (Sum.elim xx yy)),
      aevalTower_X, aevalTower_C, Sum.elim_inl, Sum.elim_inr]
    simpa only [sub_sub, sub_eq_zero] using h i)

@[simp] theorem liftTower_x (f : S →ₐ[R] T) (a b : S) (xx yy : Fin n → T)
    (h : Equations (f a) (f b) xx yy) (i : Fin n) :
    liftTower f a b xx yy h (x a b i) = xx i := by
  change aevalTower f (Sum.elim xx yy) (X (Sum.inl i)) = xx i
  exact aevalTower_X _ _ _

@[simp] theorem liftTower_y (f : S →ₐ[R] T) (a b : S) (xx yy : Fin n → T)
    (h : Equations (f a) (f b) xx yy) (i : Fin n) :
    liftTower f a b xx yy h (y a b i) = yy i := by
  change aevalTower f (Sum.elim xx yy) (X (Sum.inr i)) = yy i
  exact aevalTower_X _ _ _

@[simp] theorem liftTower_coefficient (f : S →ₐ[R] T) (a b : S) (xx yy : Fin n → T)
    (h : Equations (f a) (f b) xx yy) (r : S) :
    liftTower f a b xx yy h (algebraMap S (PathAlgebra n a b) r) = f r := by
  change aevalTower f (Sum.elim xx yy) (C r) = f r
  exact aevalTower_C _ _ _

theorem hom_ext (a b : S) (f g : PathAlgebra n a b →ₐ[R] T)
    (hc : ∀ c, f (algebraMap S _ c) = g (algebraMap S _ c))
    (hx : ∀ i, f (x a b i) = g (x a b i)) (hy : ∀ i, f (y a b i) = g (y a b i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · exact hc
  · intro i
    cases i with
    | inl i => exact hx i
    | inr i => exact hy i

#print axioms liftTower
#print axioms liftTower_x
#print axioms liftTower_y
#print axioms liftTower_coefficient
#print axioms hom_ext
end Verification.PathTower
