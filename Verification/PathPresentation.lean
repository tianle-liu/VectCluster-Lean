/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Path Presentation

Actual nearest-neighbour exchange algebras, including both prescribed
endpoints. The universal property is over arbitrary commutative rings.
-/
noncomputable section
namespace Verification.PathPresentation
open MvPolynomial
variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

def boundary {A : Type*} (a b : A) (x : Fin n → A) : Fin (n+2) → A :=
  Fin.cons a (Fin.snoc x b)

@[simp] theorem boundary_zero {A : Type*} (a b : A) (x : Fin n → A) :
    boundary a b x 0 = a := by simp [boundary]

@[simp] theorem boundary_middle {A : Type*} (a b : A) (x : Fin n → A) (i : Fin n) :
    boundary a b x i.castSucc.succ = x i := by simp [boundary]

@[simp] theorem boundary_last {A : Type*} (a b : A) (x : Fin n → A) :
    boundary a b x (Fin.last (n+1)) = b := by
  change boundary a b x (Fin.last n).succ = b
  simp only [boundary, Fin.cons_succ, Fin.snoc_last]

theorem boundary_map {A B : Type*} (f : A → B) (a b : A) (x : Fin n → A)
    (i : Fin (n+2)) :
    f (boundary a b x i) = boundary (f a) (f b) (fun j => f (x j)) i := by
  induction i using Fin.cases with
  | zero => simp
  | succ i =>
    induction i using Fin.lastCases with
    | last =>
      change f (boundary a b x (Fin.last (n+1))) = boundary (f a) (f b) _ (Fin.last (n+1))
      rw [boundary_last, boundary_last]
    | cast i => simp [boundary]

def Equations (a b : R) (x y : Fin n → R) : Prop :=
  ∀ i, x i * y i = boundary a b x i.castSucc.castSucc + boundary a b x i.succ.succ

def relation (a b : R) (i : Fin n) : MvPolynomial (Fin n ⊕ Fin n) R :=
  X (Sum.inl i) * X (Sum.inr i) -
    boundary (C a) (C b) (fun j => X (Sum.inl j)) i.castSucc.castSucc -
    boundary (C a) (C b) (fun j => X (Sum.inl j)) i.succ.succ

def relations (n : ℕ) (a b : R) : Ideal (MvPolynomial (Fin n ⊕ Fin n) R) :=
  Ideal.span (Set.range (relation a b))

abbrev PathAlgebra (n : ℕ) (a b : R) := MvPolynomial (Fin n ⊕ Fin n) R ⧸ relations n a b

def x (a b : R) (i : Fin n) : PathAlgebra n a b :=
  Ideal.Quotient.mk (relations n a b) (X (Sum.inl i))

def y (a b : R) (i : Fin n) : PathAlgebra n a b :=
  Ideal.Quotient.mk (relations n a b) (X (Sum.inr i))

theorem equations (n : ℕ) (a b : R) :
    Equations (algebraMap R _ a) (algebraMap R _ b) (x (n:=n) a b) (y a b) := by
  intro i
  have h : Ideal.Quotient.mk (relations n a b) (relation a b i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  simp only [relation, map_sub, map_mul, boundary_map (Ideal.Quotient.mk (relations n a b))] at h
  change x a b i * y a b i -
    boundary (algebraMap R _ a) (algebraMap R _ b) (x a b) i.castSucc.castSucc -
    boundary (algebraMap R _ a) (algebraMap R _ b) (x a b) i.succ.succ = 0 at h
  simpa only [sub_sub, sub_eq_zero] using h

variable [Algebra R S]

def lift (a b : R) (xx yy : Fin n → S)
    (h : Equations (algebraMap R S a) (algebraMap R S b) xx yy) :
    PathAlgebra n a b →ₐ[R] S :=
  Ideal.Quotient.liftₐ (relations n a b) (aeval (Sum.elim xx yy)) (by
    change relations n a b ≤ RingHom.ker (aeval (Sum.elim xx yy)).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change aeval (Sum.elim xx yy) (relation a b i) = 0
    simp only [relation, map_sub, map_mul, boundary_map (aeval (Sum.elim xx yy)), aeval_X, aeval_C,
      Sum.elim_inl, Sum.elim_inr]
    simpa only [sub_sub, sub_eq_zero] using h i)

@[simp] theorem lift_x (a b : R) (xx yy : Fin n → S)
    (h : Equations (algebraMap R S a) (algebraMap R S b) xx yy) (i : Fin n) :
    lift a b xx yy h (x a b i) = xx i := by simp [lift, x]

@[simp] theorem lift_y (a b : R) (xx yy : Fin n → S)
    (h : Equations (algebraMap R S a) (algebraMap R S b) xx yy) (i : Fin n) :
    lift a b xx yy h (y a b i) = yy i := by simp [lift, y]

@[ext] theorem hom_ext (a b : R) (f g : PathAlgebra n a b →ₐ[R] S)
    (hx : ∀ i, f (x a b i) = g (x a b i)) (hy : ∀ i, f (y a b i) = g (y a b i)) :
    f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl i => exact hx i
  | inr i => exact hy i

#print axioms boundary
#print axioms boundary_zero
#print axioms boundary_middle
#print axioms boundary_last
#print axioms boundary_map
#print axioms Equations
#print axioms relation
#print axioms relations
#print axioms PathAlgebra
#print axioms x
#print axioms y
#print axioms equations
#print axioms lift
#print axioms lift_x
#print axioms lift_y
#print axioms hom_ext
end Verification.PathPresentation
