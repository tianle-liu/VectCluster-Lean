/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteAlgebraCoproduct
import Verification.ExchangeCharacters

/-!
# Finite Group Algebra Tensor

Laurent coefficient algebras on a finite product of exponent groups are
actual finite tensor products over the ground ring, with each character retained.
-/
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
namespace Verification.FiniteGroupAlgebraTensor
open Classical
open scoped BigOperators TensorProduct
variable (R : Type*) [CommRing R] {I : Type*} [Fintype I]
variable (M : I → Type*) [∀ i,AddCommGroup (M i)]
abbrev Factor (i : I) := MonoidAlgebra R (Multiplicative (M i))
abbrev Total := MonoidAlgebra R (Multiplicative (∀ i,M i))
abbrev Product := ⨂[R] i,Factor R M i

def single (i : I) : M i →+ (∀ j,M j) where
  toFun := Pi.single i
  map_zero' := by simp
  map_add' := Pi.single_add i

def inclusion (i : I) : Factor R M i →ₐ[R] Total R M :=
  MonoidAlgebra.mapDomainAlgHom R R (single M i).toMultiplicative

omit [Fintype I] in
theorem inclusion_monomial (i : I) (m : M i) :
    inclusion R M i (ExchangeCharacters.monomial m)=
      ExchangeCharacters.monomial (Pi.single i m) := by
  exact Finsupp.mapDomain_single

def productMonomial : Multiplicative (∀ i,M i) →* Product R M where
  toFun m := ∏ i,PiTensorProduct.singleAlgHom i (ExchangeCharacters.monomial (m.toAdd i))
  map_one' := by
    change (∏ i,PiTensorProduct.singleAlgHom i (ExchangeCharacters.monomial (0:M i)))=1
    simp only [ExchangeCharacters.monomial_zero,map_one,Finset.prod_const_one]
  map_mul' a b := by
    change (∏ i,PiTensorProduct.singleAlgHom i (ExchangeCharacters.monomial (a.toAdd i+b.toAdd i)))=_
    simp only [ExchangeCharacters.monomial_add,map_mul]
    exact Finset.prod_mul_distrib

def toProduct : Total R M →ₐ[R] Product R M :=
  MonoidAlgebra.liftNCAlgHom (Algebra.ofId R _) (productMonomial R M) (fun _ _=>Commute.all _ _)

theorem toProduct_monomial (m : ∀ i,M i) :
    toProduct R M (ExchangeCharacters.monomial m)=
      ∏ i,PiTensorProduct.singleAlgHom i (ExchangeCharacters.monomial (m i)) := by
  change MonoidAlgebra.liftNC _ _ (MonoidAlgebra.single _ 1)=_
  rw [MonoidAlgebra.liftNC_single]
  change algebraMap R (Product R M) 1 * _=_
  rw [map_one,one_mul]
  rfl

def fromProduct : Product R M →ₐ[R] Total R M :=
  FiniteAlgebraCoproduct.lift (Factor R M) (inclusion R M)

theorem fromProduct_single (i : I) (a : Factor R M i) :
    fromProduct R M (PiTensorProduct.singleAlgHom i a)=inclusion R M i a :=
  FiniteAlgebraCoproduct.lift_single _ _ i a

theorem toProduct_inclusion_monomial (i : I) (m : M i) :
    toProduct R M (inclusion R M i (ExchangeCharacters.monomial m))=
      PiTensorProduct.singleAlgHom i (ExchangeCharacters.monomial m) := by
  rw [inclusion_monomial,toProduct_monomial]
  rw [Finset.prod_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji,ExchangeCharacters.monomial_zero,map_one]
  · simp

theorem from_to : (fromProduct R M).comp (toProduct R M)=AlgHom.id R _ := by
  apply MonoidAlgebra.algHom_ext
  intro m
  change fromProduct R M (toProduct R M (ExchangeCharacters.monomial m.toAdd))=
    ExchangeCharacters.monomial m.toAdd
  rw [toProduct_monomial,map_prod]
  simp_rw [fromProduct_single,inclusion_monomial]
  rw [← ExchangeCharacters.monomial_sum,Finset.univ_sum_single]

theorem to_from : (toProduct R M).comp (fromProduct R M)=AlgHom.id R _ := by
  apply PiTensorProduct.algHom_ext
  intro i
  apply MonoidAlgebra.algHom_ext
  intro m
  change toProduct R M (fromProduct R M (PiTensorProduct.singleAlgHom i
    (ExchangeCharacters.monomial m.toAdd)))=_
  rw [fromProduct_single,toProduct_inclusion_monomial]
  rfl

def equiv : Total R M ≃ₐ[R] Product R M :=
  AlgEquiv.ofAlgHom (toProduct R M) (fromProduct R M) (to_from R M) (from_to R M)

#print axioms Factor
#print axioms Total
#print axioms Product
#print axioms single
#print axioms inclusion
#print axioms inclusion_monomial
#print axioms productMonomial
#print axioms toProduct
#print axioms toProduct_monomial
#print axioms fromProduct
#print axioms fromProduct_single
#print axioms toProduct_inclusion_monomial
#print axioms from_to
#print axioms to_from
#print axioms equiv
end Verification.FiniteGroupAlgebraTensor
