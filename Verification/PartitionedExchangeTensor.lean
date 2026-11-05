/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.NestedExchangeComponents

/-!
# Partitioned Exchange Tensor

Disjoint exchange equations with disjoint coefficient algebras form a
finite tensor product over the ground ring, not over a shared coefficient ring.
-/
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.PartitionedExchangeTensor
open Classical MvPolynomial
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable (R : Type*) [CommRing R] {I : Type*} [Fintype I]
variable (S : I → Type*) [∀ i,CommRing (S i)] [∀ i,Algebra R (S i)]
variable (V : I → Type*) (p : ∀ i,V i → MvPolynomial (V i) (S i))
abbrev Coeff := ⨂[R] i,S i
abbrev Component (i : I) := NestedExchangeUniversal.Ring (S i) (p i)
abbrev Product := ⨂[R] i,Component S V p i

def embed (i : I) : MvPolynomial (V i) (S i) →ₐ[R] MvPolynomial (Sigma V) (Coeff R S) :=
  aevalTower ((IsScalarTower.toAlgHom R (Coeff R S) (MvPolynomial (Sigma V) (Coeff R S))).comp
    (PiTensorProduct.singleAlgHom i)) (fun v=>X ⟨i,v⟩)

def polynomial (v : Sigma V) : MvPolynomial (Sigma V) (Coeff R S) := embed R S V v.1 (p v.1 v.2)
abbrev Global := NestedExchangeUniversal.Ring (Coeff R S) (polynomial R S V p)

variable {T : Type*} [CommRing T] [Algebra R T]
omit [Fintype I] in
theorem evaluate_embed (φ : Coeff R S →ₐ[R] T) (x : Sigma V → T)
    (i : I) (q : MvPolynomial (V i) (S i)) :
    aevalTower φ x (embed R S V i q)=
      aevalTower (φ.comp (PiTensorProduct.singleAlgHom i)) (fun v=>x ⟨i,v⟩) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp only [embed,aevalTower_C,AlgHom.comp_apply,IsScalarTower.toAlgHom_apply]
           exact aevalTower_algebraMap _ _ _
  | add a b ha hb => simp only [map_add,ha,hb]
  | mul_X a v ha =>
    rw [map_mul,map_mul,ha]
    simp only [embed,aevalTower_X,map_mul]

def globalCoefficient (i : I) : S i →ₐ[R] Global R S V p :=
  (IsScalarTower.toAlgHom R (Coeff R S) (Global R S V p)).comp (PiTensorProduct.singleAlgHom i)

def inclusion (i : I) : Component S V p i →ₐ[R] Global R S V p :=
  NestedExchangeUniversal.lift R (S i) (p i) (globalCoefficient R S V p i)
    (fun v=>NestedExchangeUniversal.x (Coeff R S) (polynomial R S V p) ⟨i,v⟩)
    (fun v=>NestedExchangeUniversal.y (Coeff R S) (polynomial R S V p) ⟨i,v⟩) (by
      intro v
      rw [NestedExchangeUniversal.equation_aeval]
      change aevalTower (IsScalarTower.toAlgHom R (Coeff R S) (Global R S V p))
        (NestedExchangeUniversal.x (Coeff R S) (polynomial R S V p)) (embed R S V i (p i v))=_
      exact evaluate_embed R S V _ _ i (p i v))

omit [Fintype I] in
theorem inclusion_x (i : I) (v : V i) : inclusion R S V p i (NestedExchangeUniversal.x (S i) (p i) v)=
    NestedExchangeUniversal.x (Coeff R S) (polynomial R S V p) ⟨i,v⟩ :=
  NestedExchangeUniversal.lift_x R (S i) (p i) _ _ _ _ v

omit [Fintype I] in
theorem inclusion_y (i : I) (v : V i) : inclusion R S V p i (NestedExchangeUniversal.y (S i) (p i) v)=
    NestedExchangeUniversal.y (Coeff R S) (polynomial R S V p) ⟨i,v⟩ :=
  NestedExchangeUniversal.lift_y R (S i) (p i) _ _ _ _ v

omit [Fintype I] in
theorem inclusion_coefficient (i : I) (s : S i) :
    inclusion R S V p i (algebraMap (S i) (Component S V p i) s)=globalCoefficient R S V p i s :=
  NestedExchangeUniversal.lift_coefficient R (S i) (p i) _ _ _ _ s

def fromProduct : Product R S V p →ₐ[R] Global R S V p :=
  FiniteAlgebraCoproduct.lift (Component S V p) (inclusion R S V p)

theorem fromProduct_single (i : I) (a : Component S V p i) :
    fromProduct R S V p (PiTensorProduct.singleAlgHom i a)=inclusion R S V p i a :=
  FiniteAlgebraCoproduct.lift_single _ _ i a

def productCoefficient : Coeff R S →ₐ[R] Product R S V p :=
  FiniteAlgebraCoproduct.lift (R:=R) (T:=Product R S V p) S (fun i=>(PiTensorProduct.singleAlgHom i : Component S V p i →ₐ[R] Product R S V p).comp
    (IsScalarTower.toAlgHom R (S i) (Component S V p i)))

theorem productCoefficient_single (i : I) (a : S i) :
    productCoefficient R S V p (PiTensorProduct.singleAlgHom i a)=
      PiTensorProduct.singleAlgHom i (algebraMap (S i) (Component S V p i) a) :=
  FiniteAlgebraCoproduct.lift_single _ _ i a

def productX (v : Sigma V) : Product R S V p :=
  PiTensorProduct.singleAlgHom v.1 (NestedExchangeUniversal.x (S v.1) (p v.1) v.2)
def productY (v : Sigma V) : Product R S V p :=
  PiTensorProduct.singleAlgHom v.1 (NestedExchangeUniversal.y (S v.1) (p v.1) v.2)

theorem product_evaluation (i : I) (q : MvPolynomial (V i) (S i)) :
    aevalTower (productCoefficient R S V p) (productX R S V p) (embed R S V i q)=
      PiTensorProduct.singleAlgHom i (aeval (NestedExchangeUniversal.x (S i) (p i)) q) := by
  rw [evaluate_embed R S V (productCoefficient R S V p) (productX R S V p) i q]
  induction q using MvPolynomial.induction_on with
  | C a => simp only [aevalTower_C,AlgHom.comp_apply,aeval_C,productCoefficient_single]
  | add a b ha hb => simp only [map_add,ha,hb]
  | mul_X a v ha =>
    simp only [map_mul,aevalTower_X,aeval_X]
    rw [ha]
    rfl

theorem product_equation (v : Sigma V) : productX R S V p v*productY R S V p v=
    aevalTower (productCoefficient R S V p) (productX R S V p) (polynomial R S V p v) := by
  rw [polynomial,product_evaluation]
  simp only [productX,productY,← map_mul,NestedExchangeUniversal.equation_aeval]

def toProduct : Global R S V p →ₐ[R] Product R S V p :=
  NestedExchangeUniversal.lift R (Coeff R S) (polynomial R S V p) (T:=Product R S V p) (productCoefficient R S V p)
    (productX R S V p) (productY R S V p) (product_equation R S V p)

theorem toProduct_x (v : Sigma V) : toProduct R S V p (NestedExchangeUniversal.x (Coeff R S) (polynomial R S V p) v)=productX R S V p v :=
  NestedExchangeUniversal.lift_x R (Coeff R S) (polynomial R S V p) _ _ _ _ v

theorem toProduct_y (v : Sigma V) : toProduct R S V p (NestedExchangeUniversal.y (Coeff R S) (polynomial R S V p) v)=productY R S V p v :=
  NestedExchangeUniversal.lift_y R (Coeff R S) (polynomial R S V p) _ _ _ _ v

theorem toProduct_coefficient (s : Coeff R S) :
    toProduct R S V p (algebraMap (Coeff R S) (Global R S V p) s)=productCoefficient R S V p s :=
  NestedExchangeUniversal.lift_coefficient R (Coeff R S) (polynomial R S V p) _ _ _ _ s

theorem to_from : (toProduct R S V p).comp (fromProduct R S V p)=AlgHom.id R _ := by
  apply PiTensorProduct.algHom_ext
  intro i
  apply NestedExchangeUniversal.hom_ext R (S i) (p i) (T:=Product R S V p)
  · intro s
    simp only [AlgHom.comp_apply,AlgHom.id_apply,fromProduct_single,inclusion_coefficient,
      globalCoefficient,IsScalarTower.toAlgHom_apply,toProduct_coefficient,productCoefficient_single]
  · intro v
    simp only [AlgHom.comp_apply,AlgHom.id_apply,fromProduct_single,inclusion_x,toProduct_x,productX]
  · intro v
    simp only [AlgHom.comp_apply,AlgHom.id_apply,fromProduct_single,inclusion_y,toProduct_y,productY]

theorem coefficient_from : (fromProduct R S V p).comp (productCoefficient R S V p)=
    IsScalarTower.toAlgHom R (Coeff R S) (Global R S V p) := by
  apply PiTensorProduct.algHom_ext
  intro i
  apply AlgHom.ext
  intro s
  simp only [AlgHom.comp_apply,productCoefficient_single,fromProduct_single,inclusion_coefficient,
    globalCoefficient,IsScalarTower.toAlgHom_apply]

theorem from_to : (fromProduct R S V p).comp (toProduct R S V p)=AlgHom.id R _ := by
  apply NestedExchangeUniversal.hom_ext R (Coeff R S) (polynomial R S V p)
  · intro s
    simp only [AlgHom.comp_apply,AlgHom.id_apply,toProduct_coefficient]
    exact AlgHom.congr_fun (coefficient_from R S V p) s
  · intro v
    simp only [AlgHom.comp_apply,AlgHom.id_apply,toProduct_x,productX,fromProduct_single,inclusion_x]
  · intro v
    simp only [AlgHom.comp_apply,AlgHom.id_apply,toProduct_y,productY,fromProduct_single,inclusion_y]

def equivalence : Global R S V p ≃ₐ[R] Product R S V p :=
  AlgEquiv.ofAlgHom (toProduct R S V p) (fromProduct R S V p) (to_from R S V p) (from_to R S V p)

#print axioms Coeff
#print axioms Component
#print axioms Product
#print axioms embed
#print axioms polynomial
#print axioms Global
#print axioms evaluate_embed
#print axioms globalCoefficient
#print axioms inclusion
#print axioms inclusion_x
#print axioms inclusion_y
#print axioms inclusion_coefficient
#print axioms fromProduct
#print axioms fromProduct_single
#print axioms productCoefficient
#print axioms productCoefficient_single
#print axioms productX
#print axioms productY
#print axioms product_evaluation
#print axioms product_equation
#print axioms toProduct
#print axioms toProduct_x
#print axioms toProduct_y
#print axioms toProduct_coefficient
#print axioms to_from
#print axioms coefficient_from
#print axioms from_to
#print axioms equivalence
end Verification.PartitionedExchangeTensor
