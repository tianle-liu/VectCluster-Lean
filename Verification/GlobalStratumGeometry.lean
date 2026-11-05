/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CharacterStratumAlgebra
import Verification.PrimitiveTorusRank
import Verification.TameCharacterSmooth

/-!
# Global Stratum Geometry

Geometry of the actual globally presented zero strata over the base.
The affine-times-character-fiber isomorphism is constructed from the
original polynomial quotient and localization, not supplied as a premise.
-/
namespace Verification.GlobalStratumGeometry
open Verification.ActualStratum Verification.PrimitiveCharacters
open Verification.CharacterStratumAlgebra Verification.PrimitiveTorusRank
universe u
variable (R I K T P : Type u) [CommRing R] [Fintype I] [Fintype K] [AddCommGroup P]
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable (j : T → K) (B : (I ⊕ K) → (I ⊕ T) → ℤ)
  (hB : ∀ a i : I, B (Sum.inl a) (Sum.inl i) = 0)
  (f : P →ₗ[ℤ] (K →₀ ℤ)) (b : Basis I ℤ P)
  (hf : ∀ i, f (b i) = Verification.ExchangeCharacters.column Finset.univ
    (fun a => B (Sum.inr a) (Sum.inl i)) (fun k => Finsupp.single k 1))
  (hinj : Function.Injective f)
include hB b hf hinj

/-- AS strata as algebras over the original coefficient ring. -/
theorem primitive_stratum
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    Nonempty (GlobalZeroStratum R I K T j B ≃ₐ[R]
      MvPolynomial I (MonoidAlgebra R (Multiplicative ((K →₀ ℤ) ⧸ LinearMap.range f)))) := by
  obtain ⟨e⟩ := primitive_prescribed_fiber (R := R) f hinj hs b (fun _ => -1)
  exact ⟨(globalFiberStratum R I K T j B hB f b hf).trans (MvPolynomial.mapAlgEquiv I e)⟩

/-- The dimension of the split torus factor is derived from the original columns. -/
theorem primitive_stratum_rank
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    ∃ n : ℕ, n + Fintype.card I = Fintype.card K ∧
      Nonempty (GlobalZeroStratum R I K T j B ≃ₐ[R]
        MvPolynomial I (MonoidAlgebra R (Multiplicative (Fin n →₀ ℤ)))) := by
  obtain ⟨e⟩ := primitive_stratum R I K T P j B hB f b hf hinj hs
  exact ⟨_, quotient_rank f b hinj hs,
    ⟨e.trans (MvPolynomial.mapAlgEquiv I (quotientTorusEquiv R f hs))⟩⟩

/-- Tame Smith factors give smoothness of the actual locally closed stratum. -/
theorem stratum_smooth_smith {n : ℕ}
    (s : Basis.SmithNormalForm (LinearMap.range f) K n)
    (he : ∀ i, IsUnit ((s.a i).natAbs : R)) :
    Algebra.Smooth R (GlobalZeroStratum R I K T j B) := by
  let A := MonoidAlgebra R (Multiplicative (K →₀ ℤ)) ⧸ prescribedIdeal (R := R) f b (fun _ => -1)
  letI : Algebra.Smooth R A :=
    Verification.TameCharacterSmooth.smith_prescribed_smooth f hinj b s (fun _ => -1) he
  letI : Algebra.Smooth A (MvPolynomial I A) := {}
  letI : Algebra.Smooth R (MvPolynomial I A) := Algebra.Smooth.comp R A (MvPolynomial I A)
  exact Algebra.Smooth.of_equiv (globalFiberStratum R I K T j B hB f b hf).symm

/-- Under saturation the stratum is smooth over every coefficient ring. -/
theorem primitive_stratum_smooth
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    Algebra.Smooth R (GlobalZeroStratum R I K T j B) := by
  obtain ⟨n,_,⟨e⟩⟩ := primitive_stratum_rank R I K T P j B hB f b hf hinj hs
  let A := MonoidAlgebra R (Multiplicative (Fin n →₀ ℤ))
  letI : Algebra.Smooth R (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) :=
    Verification.TorusSmooth.torus_smooth R (ULift.{u} (Fin n))
  let d : (Fin n →₀ ℤ) ≃ₗ[ℤ] (ULift.{u} (Fin n) →₀ ℤ) :=
    Finsupp.domLCongr Equiv.ulift.symm
  letI : Algebra.Smooth R A := Algebra.Smooth.of_equiv
    (MonoidAlgebra.domCongr R R d.toAddEquiv.toMultiplicative).symm
  letI : Algebra.Smooth A (MvPolynomial I A) := {}
  letI : Algebra.Smooth R (MvPolynomial I A) := Algebra.Smooth.comp R A (MvPolynomial I A)
  exact Algebra.Smooth.of_equiv e.symm

#print axioms primitive_stratum
#print axioms primitive_stratum_rank
#print axioms stratum_smooth_smith
#print axioms primitive_stratum_smooth
end Verification.GlobalStratumGeometry
