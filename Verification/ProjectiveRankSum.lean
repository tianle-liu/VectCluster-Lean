/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ProjectiveConstantRank
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Projective Rank Sum

Rank additivity for genuine finite projective module decompositions,
proved using the actual localization/tensor-product equivalence.
-/
noncomputable section
namespace Verification.ProjectiveRankSum
open Verification.ActualProjectiveSplitting
variable {R : Type} [CommRing R]
variable (S : Submonoid R)
variable {M N : Type} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

def localizedEquiv (e : M ≃ₗ[R] N) : LocalizedModule S M ≃ₗ[Localization S] LocalizedModule S N :=
  (LocalizedModule.equivTensorProduct S M).trans
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Localization S) (Localization S)) e).trans
      (LocalizedModule.equivTensorProduct S N).symm)

def localizedProduct : LocalizedModule S (M × N) ≃ₗ[Localization S]
    (LocalizedModule S M × LocalizedModule S N) :=
  (LocalizedModule.equivTensorProduct S (M × N)).trans
    ((TensorProduct.prodRight R (Localization S) (Localization S) M N).trans
      ((LocalizedModule.equivTensorProduct S M).symm.prodCongr
        (LocalizedModule.equivTensorProduct S N).symm))

variable [IsDomain R]

omit [IsDomain R] in
theorem rank_sum (P Q N : Bundle R) (e : P.object ≃ₗ[R] (Q.object × N.object))
    (p : PrimeSpectrum R) : Module.rankAtStalk P.object p=
      Module.rankAtStalk Q.object p+Module.rankAtStalk N.object p := by
  letI := Q.finite
  letI := N.finite
  letI := Q.projective
  letI := N.projective
  letI : Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl Q.object) :=
    Module.free_of_flat_of_isLocalRing
  letI : Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl N.object) :=
    Module.free_of_flat_of_isLocalRing
  have he := ((localizedEquiv p.asIdeal.primeCompl e).trans
    (localizedProduct (M := Q.object) (N := N.object) p.asIdeal.primeCompl)).finrank_eq
  rw [Module.finrank_prod] at he
  exact he

theorem rank_numbers {P Q N : Bundle R} (e : P.object ≃ₗ[R] (Q.object × N.object))
    {r q n : ℕ} (hP : HasRank P r) (hQ : HasRank Q q) (hN : HasRank N n) : r=q+n := by
  let p : PrimeSpectrum R := ⟨⊥,Ideal.bot_prime⟩
  have he := rank_sum P Q N e p
  rw [hP p,hQ p,hN p] at he
  exact he

#print axioms localizedEquiv
#print axioms localizedProduct
#print axioms rank_sum
#print axioms rank_numbers
end Verification.ProjectiveRankSum
