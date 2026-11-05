/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GlobalSmithStratum
import Verification.MonoidAlgebraProducts
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
# Smith Components

The actual Smith fiber and zero-stratum rings split as products over
finite separable fields. Each Laurent-polynomial factor is an integral
domain, so the decomposition concerns rings rather than dimension counts.
-/
noncomputable section
universe u
namespace Verification.SmithComponents
open Verification.GlobalSmithStratum Verification.PartialPowerProduct
open Verification.DiagonalPowerFibers Verification.MonoidAlgebraProducts
open Verification.ActualStratum Verification.ExchangeCharacters
attribute [local instance] MvPolynomial.algebraMvPolynomial

section Products
variable {R I J : Type*} [CommRing R] (S : J → Type*)
  [∀ j, CommRing (S j)] [∀ j, Algebra R (S j)] [Fintype J]

def polynomialProductEquiv : MvPolynomial I (∀ j, S j) ≃ₐ[R] ∀ j, MvPolynomial I (S j) :=
  (AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := R) (∀ j, S j) (I →₀ ℕ)).trans
    ((productEquiv R (Multiplicative (I →₀ ℕ)) S).trans
      (AlgEquiv.piCongrRight (fun j =>
        (AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := R) (S j) (I →₀ ℕ)).symm)))

end Products

variable {k I A K P : Type u} [Field k] [AddCommGroup P]

theorem torus_domain [CommRing A] [IsDomain A] : IsDomain (Laurent A K) := inferInstance

theorem affine_torus_domain [CommRing A] [IsDomain A] :
    IsDomain (MvPolynomial I (Laurent A K)) := inferInstance

theorem character_separable_product (f : P →ₗ[ℤ] (K →₀ ℤ)) (hinj : Function.Injective f)
    (b : Basis I ℤ P) {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) K n)
    (he : ∀ i, IsUnit ((s.a i).natAbs : k)) :
    ∃ (J : Type u) (_ : Finite J) (L : J → Type u) (_ : ∀ i, Field (L i))
      (_ : ∀ i, Algebra k (L i))
      (_ : (MonoidAlgebra k (Multiplicative (K →₀ ℤ)) ⧸
        Verification.PrimitiveCharacters.prescribedIdeal (R := k) f b (fun _ => -1)) ≃ₐ[k]
        ∀ i, Laurent (L i) (FreeIndex (smithEmbedding f s))),
      ∀ i, Module.Finite k (L i) ∧ Algebra.IsSeparable k (L i) := by
  obtain ⟨J,hJ,L,hL,aL,e,hsep⟩ := (Algebra.Etale.iff_exists_algEquiv_prod k _).mp
    (finiteFactor_finite_etale f hinj b s he).2
  letI := hJ
  letI := hL
  letI := aL
  letI : Fintype J := Fintype.ofFinite J
  refine ⟨J,hJ,L,hL,aL,?_,hsep⟩
  exact (smithProductEquiv f hinj b s).trans
    ((coefficientEquiv e).trans
      (productEquiv k (Multiplicative (FreeIndex (smithEmbedding f s) →₀ ℤ)) L))

variable {T : Type u} [Fintype I] [Fintype K]

theorem zero_stratum_separable_product
    (j : T → K) (B : (I ⊕ K) → (I ⊕ T) → ℤ)
    (hB : ∀ a i : I, B (Sum.inl a) (Sum.inl i) = 0)
    (f : P →ₗ[ℤ] (K →₀ ℤ)) (b : Basis I ℤ P)
    (hf : ∀ i, f (b i) = column Finset.univ
      (fun a => B (Sum.inr a) (Sum.inl i)) (fun v => Finsupp.single v 1))
    (hinj : Function.Injective f) {n : ℕ}
    (s : Basis.SmithNormalForm (LinearMap.range f) K n)
    (he : ∀ i, IsUnit ((s.a i).natAbs : k)) :
    ∃ (J : Type u) (_ : Finite J) (L : J → Type u) (_ : ∀ i, Field (L i))
      (_ : ∀ i, Algebra k (L i))
      (_ : GlobalZeroStratum k I K T j B ≃ₐ[k]
        ∀ i, MvPolynomial I (Laurent (L i) (FreeIndex (smithEmbedding f s)))),
      ∀ i, Module.Finite k (L i) ∧ Algebra.IsSeparable k (L i) ∧
        IsDomain (MvPolynomial I (Laurent (L i) (FreeIndex (smithEmbedding f s)))) := by
  obtain ⟨J,hJ,L,hL,aL,e,hsep⟩ := character_separable_product f hinj b s he
  letI := hJ
  letI := hL
  letI := aL
  letI : Fintype J := Fintype.ofFinite J
  refine ⟨J,hJ,L,hL,aL,?_,fun i => ⟨(hsep i).1,(hsep i).2,affine_torus_domain⟩⟩
  exact ((Verification.CharacterStratumAlgebra.globalFiberStratum k I K T j B hB f b hf).trans
    (MvPolynomial.mapAlgEquiv I e)).trans (polynomialProductEquiv (I := I)
      (fun i => Laurent (L i) (FreeIndex (smithEmbedding f s))))

#print axioms polynomialProductEquiv
#print axioms torus_domain
#print axioms affine_torus_domain
#print axioms character_separable_product
#print axioms zero_stratum_separable_product
end Verification.SmithComponents
