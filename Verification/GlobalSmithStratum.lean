/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GlobalStratumGeometry
import Verification.PartialPowerProduct
import Verification.PartialPowerReindex
import Verification.SignedCharacters
import Verification.SmithRanks

/-!
# Global Smith Stratum

The full Smith product presentation of an actual global zero stratum.
The finite factor, its signs, and the dimension of its free torus are
constructed from the original column lattice and its Smith normal form.
-/
noncomputable section
universe u
namespace Verification.GlobalSmithStratum
open Verification.PrimitiveCharacters Verification.SmithCharacters
open Verification.DiagonalPowerFibers Verification.PartialPowerProduct
open Verification.PartialPowerReindex Verification.ActualStratum Verification.ExchangeCharacters
variable {R I K T P : Type u} [CommRing R] [AddCommGroup P]
attribute [local instance] MvPolynomial.algebraMvPolynomial

def smithEmbedding (f : P →ₗ[ℤ] (K →₀ ℤ)) {n : ℕ}
    (s : Basis.SmithNormalForm (LinearMap.range f) K n) : ULift.{u} (Fin n) ↪ K :=
  reindexEmbedding s.f Equiv.ulift

def smithExponent (f : P →ₗ[ℤ] (K →₀ ℤ)) {n : ℕ}
    (s : Basis.SmithNormalForm (LinearMap.range f) K n) (i : ULift.{u} (Fin n)) : ℕ :=
  (s.a i.down).natAbs

def smithValue (f : P →ₗ[ℤ] (K →₀ ℤ)) (hinj : Function.Injective f)
    (b : Basis I ℤ P) {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) K n)
    (i : ULift.{u} (Fin n)) : Rˣ :=
  positiveConstant (s.a i.down)
    (smithConstants f hinj s (basisCharacter b (fun _ => -1)) i.down)

abbrev FiniteFactor (f : P →ₗ[ℤ] (K →₀ ℤ)) (hinj : Function.Injective f)
    (b : Basis I ℤ P) {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) K n) :=
  PowerAlgebra (smithExponent f s) (smithValue (R := R) f hinj b s)

theorem smithExponent_positive (f : P →ₗ[ℤ] (K →₀ ℤ)) {n : ℕ}
    (s : Basis.SmithNormalForm (LinearMap.range f) K n) (i : ULift.{u} (Fin n)) :
    0 < smithExponent f s i := Int.natAbs_pos.mpr (smith_coefficient_ne_zero s i.down)

def smithProductEquiv (f : P →ₗ[ℤ] (K →₀ ℤ)) (hinj : Function.Injective f)
    (b : Basis I ℤ P) {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) K n) :
    (MonoidAlgebra R (Multiplicative (K →₀ ℤ)) ⧸ prescribedIdeal (R := R) f b (fun _ => -1)) ≃ₐ[R]
      Laurent (FiniteFactor (R := R) f hinj b s) (FreeIndex (smithEmbedding f s)) :=
  ((Ideal.quotientEquivAlgOfEq R (prescribedIdeal_eq f b (fun _ => -1))).trans
    (Verification.TameCharacterSmooth.smithPositiveEquiv f hinj b s
      (basisCharacter b (fun _ => -1)))).trans
    ((reindexEquiv s.f (fun i => (s.a i).natAbs)
      (fun i => positiveConstant (s.a i)
        (smithConstants f hinj s (basisCharacter b (fun _ => -1)) i))
      (Equiv.ulift : ULift.{u} (Fin _) ≃ Fin _)).trans
      (productEquiv (smithEmbedding f s) (smithExponent f s)
        (smithValue (R := R) f hinj b s) (smithExponent_positive f s)))

theorem finiteFactor_finite_etale (f : P →ₗ[ℤ] (K →₀ ℤ)) (hinj : Function.Injective f)
    (b : Basis I ℤ P) {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) K n)
    (he : ∀ i, IsUnit ((s.a i).natAbs : R)) :
    Module.Finite R (FiniteFactor (R := R) f hinj b s) ∧
      Algebra.Etale R (FiniteFactor (R := R) f hinj b s) :=
  power_finite_etale _ _ (smithExponent_positive f s) (fun i => he i.down)

theorem free_rank [Fintype I] [Fintype K]
    (f : P →ₗ[ℤ] (K →₀ ℤ)) (hinj : Function.Injective f)
    (b : Basis I ℤ P) {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) K n) :
    Nat.card (FreeIndex (smithEmbedding f s)) + Fintype.card I = Fintype.card K := by
  simp only [FreeIndex, smithEmbedding, reindex_range]
  exact Verification.SmithRanks.smith_free_rank f hinj b s

def globalSmithEquiv [Fintype I] [Fintype K]
    (j : T → K) (B : (I ⊕ K) → (I ⊕ T) → ℤ)
    (hB : ∀ a i : I, B (Sum.inl a) (Sum.inl i) = 0)
    (f : P →ₗ[ℤ] (K →₀ ℤ)) (b : Basis I ℤ P)
    (hf : ∀ i, f (b i) = column Finset.univ
      (fun a => B (Sum.inr a) (Sum.inl i)) (fun k => Finsupp.single k 1))
    (hinj : Function.Injective f) {n : ℕ}
    (s : Basis.SmithNormalForm (LinearMap.range f) K n) :
    GlobalZeroStratum R I K T j B ≃ₐ[R]
      MvPolynomial I (Laurent (FiniteFactor (R := R) f hinj b s) (FreeIndex (smithEmbedding f s))) :=
  (Verification.CharacterStratumAlgebra.globalFiberStratum R I K T j B hB f b hf).trans
    (MvPolynomial.mapAlgEquiv I (smithProductEquiv f hinj b s))

section Field
variable {k : Type u} [Field k] [Fintype I] [Fintype K]

omit [Fintype I] [Fintype K] in
theorem smithValue_sign (f : P →ₗ[ℤ] (K →₀ ℤ)) (hinj : Function.Injective f)
    (b : Basis I ℤ P) {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) K n)
    (i : ULift.{u} (Fin n)) :
    (smithValue (R := k) f hinj b s i : k) = 1 ∨ (smithValue (R := k) f hinj b s i : k) = -1 :=
  Verification.SignedCharacters.smith_negative_constant_is_sign f hinj b s i.down

/-- All parts of the original Smith zero-stratum algebra presentation,
including the finite etale factor, its signs, and both coordinate counts. -/
theorem global_smith_stratum
    (j : T → K) (B : (I ⊕ K) → (I ⊕ T) → ℤ)
    (hB : ∀ a i : I, B (Sum.inl a) (Sum.inl i) = 0)
    (f : P →ₗ[ℤ] (K →₀ ℤ)) (b : Basis I ℤ P)
    (hf : ∀ i, f (b i) = column Finset.univ
      (fun a => B (Sum.inr a) (Sum.inl i)) (fun v => Finsupp.single v 1))
    (hinj : Function.Injective f) {n : ℕ}
    (s : Basis.SmithNormalForm (LinearMap.range f) K n)
    (he : ∀ i, IsUnit ((s.a i).natAbs : k)) :
    n = Fintype.card I ∧
    Nat.card (FreeIndex (smithEmbedding f s)) + Fintype.card I = Fintype.card K ∧
    (∀ i, (smithValue (R := k) f hinj b s i : k) = 1 ∨
      (smithValue (R := k) f hinj b s i : k) = -1) ∧
    Module.Finite k (FiniteFactor (R := k) f hinj b s) ∧
    Algebra.Etale k (FiniteFactor (R := k) f hinj b s) ∧
    Nonempty (GlobalZeroStratum k I K T j B ≃ₐ[k]
      MvPolynomial I (Laurent (FiniteFactor (R := k) f hinj b s)
        (FreeIndex (smithEmbedding f s)))) := by
  obtain ⟨hfinite,hetale⟩ := finiteFactor_finite_etale f hinj b s he
  exact ⟨Verification.SmithRanks.smith_source_rank f hinj b s, free_rank f hinj b s,
    smithValue_sign f hinj b s, hfinite, hetale, ⟨globalSmithEquiv j B hB f b hf hinj s⟩⟩
end Field

#print axioms smithEmbedding
#print axioms smithExponent
#print axioms smithValue
#print axioms FiniteFactor
#print axioms smithExponent_positive
#print axioms smithProductEquiv
#print axioms finiteFactor_finite_etale
#print axioms free_rank
#print axioms globalSmithEquiv
#print axioms smithValue_sign
#print axioms global_smith_stratum
end Verification.GlobalSmithStratum
