/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.NestedExchangeUniversal
import Verification.FiniteAlgebraCoproduct
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Nested Exchange Components

Disjoint exchange equations give a literal finite tensor product of their
component quotient rings. No product decomposition is an input.
-/
noncomputable section
namespace Verification.NestedExchangeComponents
open Classical MvPolynomial
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable (R : Type*) [CommRing R]
variable {I : Type*} [Fintype I] (V : I → Type*)
variable (p : ∀ i,V i → MvPolynomial (V i) R)

abbrev Component (i : I) := NestedExchangeUniversal.Ring R (p i)
def polynomial (v : (i : I) × V i) : MvPolynomial ((i : I) × V i) R :=
  rename (Sigma.mk v.1) (p v.1 v.2)
abbrev Global := NestedExchangeUniversal.Ring R (polynomial R V p)
abbrev Product := ⨂[R] i,Component R V p i

def inclusion (i : I) : Component R V p i →ₐ[R] Global R V p :=
  NestedExchangeUniversal.lift R R (p i) (Algebra.ofId R _)
    (fun v=>NestedExchangeUniversal.x R (polynomial R V p) ⟨i,v⟩)
    (fun v=>NestedExchangeUniversal.y R (polynomial R V p) ⟨i,v⟩) (by
      intro v
      rw [aevalTower_ofId]
      exact (NestedExchangeUniversal.equation_aeval R (polynomial R V p) ⟨i,v⟩).trans
        (aeval_rename (Sigma.mk i) _ (p i v)))

omit [Fintype I] in
theorem inclusion_x (i : I) (v : V i) :
    inclusion R V p i (NestedExchangeUniversal.x R (p i) v)=
      NestedExchangeUniversal.x R (polynomial R V p) ⟨i,v⟩ :=
  NestedExchangeUniversal.lift_x R R (p i) _ _ _ _ v

omit [Fintype I] in
theorem inclusion_y (i : I) (v : V i) :
    inclusion R V p i (NestedExchangeUniversal.y R (p i) v)=
      NestedExchangeUniversal.y R (polynomial R V p) ⟨i,v⟩ :=
  NestedExchangeUniversal.lift_y R R (p i) _ _ _ _ v

def fromProduct : Product R V p →ₐ[R] Global R V p :=
  FiniteAlgebraCoproduct.lift (Component R V p) (inclusion R V p)

theorem fromProduct_single (i : I) (a : Component R V p i) :
    fromProduct R V p (PiTensorProduct.singleAlgHom i a)=inclusion R V p i a :=
  FiniteAlgebraCoproduct.lift_single _ _ i a

def productX (v : (i : I) × V i) : Product R V p :=
  PiTensorProduct.singleAlgHom v.1 (NestedExchangeUniversal.x R (p v.1) v.2)
def productY (v : (i : I) × V i) : Product R V p :=
  PiTensorProduct.singleAlgHom v.1 (NestedExchangeUniversal.y R (p v.1) v.2)

omit [Fintype I] in
theorem product_equation (v : (i : I) × V i) :
    productX R V p v*productY R V p v=
      aeval (productX R V p) (polynomial R V p v) := by
  rw [polynomial,aeval_rename]
  have h : (PiTensorProduct.singleAlgHom v.1 : Component R V p v.1 →ₐ[R] Product R V p).comp
      (aeval (NestedExchangeUniversal.x R (p v.1))) =
      aeval (productX R V p ∘ Sigma.mk v.1) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply,aeval_X]
    rfl
  simpa only [AlgHom.comp_apply,map_mul,productX,productY] using
    (congrArg (PiTensorProduct.singleAlgHom v.1 : Component R V p v.1 →ₐ[R] Product R V p)
      (NestedExchangeUniversal.equation_aeval R (p v.1) v.2)).trans
      (AlgHom.congr_fun h (p v.1 v.2))

def toProduct : Global R V p →ₐ[R] Product R V p :=
  NestedExchangeUniversal.lift R R (polynomial R V p) (Algebra.ofId R _)
    (productX R V p) (productY R V p) (by
      intro v
      rw [aevalTower_ofId]
      exact product_equation R V p v)

omit [Fintype I] in
theorem toProduct_x (v : (i : I) × V i) :
    toProduct R V p (NestedExchangeUniversal.x R (polynomial R V p) v)=productX R V p v :=
  NestedExchangeUniversal.lift_x R R (polynomial R V p) _ _ _ _ v

omit [Fintype I] in
theorem toProduct_y (v : (i : I) × V i) :
    toProduct R V p (NestedExchangeUniversal.y R (polynomial R V p) v)=productY R V p v :=
  NestedExchangeUniversal.lift_y R R (polynomial R V p) _ _ _ _ v

theorem from_to : (fromProduct R V p).comp (toProduct R V p)=AlgHom.id R _ := by
  apply NestedExchangeUniversal.hom_ext R R (polynomial R V p)
  · intro r
    simp only [AlgHom.commutes]
  · intro v
    simp only [AlgHom.comp_apply,AlgHom.id_apply,toProduct_x,productX,fromProduct_single,inclusion_x]
  · intro v
    simp only [AlgHom.comp_apply,AlgHom.id_apply,toProduct_y,productY,fromProduct_single,inclusion_y]

theorem to_from : (toProduct R V p).comp (fromProduct R V p)=AlgHom.id R _ := by
  apply PiTensorProduct.algHom_ext
  intro i
  apply NestedExchangeUniversal.hom_ext R R (p i) (T := Product R V p)
  · intro r
    simp only [AlgHom.commutes]
  · intro v
    simp only [AlgHom.comp_apply,AlgHom.id_apply,fromProduct_single,inclusion_x,toProduct_x,productX]
  · intro v
    simp only [AlgHom.comp_apply,AlgHom.id_apply,fromProduct_single,inclusion_y,toProduct_y,productY]

def equivalence : Global R V p ≃ₐ[R] Product R V p :=
  AlgEquiv.ofAlgHom (toProduct R V p) (fromProduct R V p) (to_from R V p) (from_to R V p)

#print axioms Component
#print axioms polynomial
#print axioms Global
#print axioms Product
#print axioms inclusion
#print axioms inclusion_x
#print axioms inclusion_y
#print axioms fromProduct
#print axioms fromProduct_single
#print axioms productX
#print axioms productY
#print axioms product_equation
#print axioms toProduct
#print axioms toProduct_x
#print axioms toProduct_y
#print axioms from_to
#print axioms to_from
#print axioms equivalence
end Verification.NestedExchangeComponents
