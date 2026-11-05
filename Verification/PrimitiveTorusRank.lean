/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualStratum
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Primitive Torus Rank

The rank and affine-scheme form of the original AS zero-stratum
calculation, using the actual quotient lattice rather than a presumed torus.
-/
namespace Verification.PrimitiveTorusRank
open Verification.PrimitiveLattice Verification.ActualStratum
variable {P ι κ : Type*} [AddCommGroup P] [Fintype ι] [Fintype κ]

theorem quotient_rank (f : P →ₗ[ℤ] (κ →₀ ℤ)) (b : Basis ι ℤ P)
    (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    Module.finrank ℤ ((κ →₀ ℤ) ⧸ LinearMap.range f) + Fintype.card ι = Fintype.card κ := by
  letI : Module.Free ℤ P := Module.Free.of_basis b
  letI : Module.Finite ℤ P := Module.Finite.of_basis b
  letI := quotient_free (LinearMap.range f) hs
  obtain ⟨e⟩ := primitive_columns_split f hf hs
  have h := e.finrank_eq
  rw [Module.finrank_prod, Module.finrank_eq_card_basis b,
    Module.finrank_eq_card_basis (Finsupp.basisSingleOne : Basis κ ℤ (κ →₀ ℤ))] at h
  omega

noncomputable def quotientCoordinates (f : P →ₗ[ℤ] (κ →₀ ℤ))
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    ((κ →₀ ℤ) ⧸ LinearMap.range f) ≃ₗ[ℤ]
      (Fin (Module.finrank ℤ ((κ →₀ ℤ) ⧸ LinearMap.range f)) →₀ ℤ) := by
  letI := quotient_free (LinearMap.range f) hs
  exact (Module.finBasis ℤ ((κ →₀ ℤ) ⧸ LinearMap.range f)).repr

noncomputable def quotientTorusEquiv (R : Type*) [CommRing R]
    (f : P →ₗ[ℤ] (κ →₀ ℤ))
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    MonoidAlgebra R (Multiplicative ((κ →₀ ℤ) ⧸ LinearMap.range f)) ≃ₐ[R]
      MonoidAlgebra R (Multiplicative
        (Fin (Module.finrank ℤ ((κ →₀ ℤ) ⧸ LinearMap.range f)) →₀ ℤ)) :=
  MonoidAlgebra.domCongr R R (quotientCoordinates f hs).toAddEquiv.toMultiplicative

universe u
variable (R I K T L : Type u) [CommRing R] [Fintype I] [Fintype K] [AddCommGroup L]

/-- The torus dimension is d-2|I|: here d=|I|+|K|, so n+|I|=|K|. -/
theorem global_zero_stratum_rank
    (j : T → K) (B : (I ⊕ K) → (I ⊕ T) → ℤ)
    (hB : ∀ a i : I, B (Sum.inl a) (Sum.inl i) = 0)
    (f : L →ₗ[ℤ] (K →₀ ℤ)) (b : Basis I ℤ L)
    (hf : ∀ i, f (b i) = Verification.ExchangeCharacters.column Finset.univ
      (fun a => B (Sum.inr a) (Sum.inl i)) (fun k => Finsupp.single k 1))
    (hinj : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    ∃ n : ℕ, n + Fintype.card I = Fintype.card K ∧
      Nonempty (GlobalZeroStratum R I K T j B ≃+*
        MvPolynomial I (MonoidAlgebra R (Multiplicative (Fin n →₀ ℤ)))) := by
  obtain ⟨e⟩ := global_zero_stratum R I K T j B hB f b hf hinj hs
  exact ⟨_, quotient_rank f b hinj hs,
    ⟨e.trans (MvPolynomial.mapEquiv I (quotientTorusEquiv R f hs).toRingEquiv)⟩⟩

open CategoryTheory

theorem global_zero_stratum_spec
    (j : T → K) (B : (I ⊕ K) → (I ⊕ T) → ℤ)
    (hB : ∀ a i : I, B (Sum.inl a) (Sum.inl i) = 0)
    (f : L →ₗ[ℤ] (K →₀ ℤ)) (b : Basis I ℤ L)
    (hf : ∀ i, f (b i) = Verification.ExchangeCharacters.column Finset.univ
      (fun a => B (Sum.inr a) (Sum.inl i)) (fun k => Finsupp.single k 1))
    (hinj : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    ∃ n : ℕ, n + Fintype.card I = Fintype.card K ∧
      Nonempty (AlgebraicGeometry.Spec (CommRingCat.of (GlobalZeroStratum R I K T j B)) ≅
        AlgebraicGeometry.Spec (CommRingCat.of
          (MvPolynomial I (MonoidAlgebra R (Multiplicative (Fin n →₀ ℤ)))))) := by
  obtain ⟨n,hn,⟨e⟩⟩ := global_zero_stratum_rank R I K T L j B hB f b hf hinj hs
  exact ⟨n,hn,⟨AlgebraicGeometry.Scheme.Spec.mapIso e.toCommRingCatIso.symm.op⟩⟩

#print axioms quotient_rank
#print axioms quotientCoordinates
#print axioms quotientTorusEquiv
#print axioms global_zero_stratum_rank
#print axioms global_zero_stratum_spec
end Verification.PrimitiveTorusRank
