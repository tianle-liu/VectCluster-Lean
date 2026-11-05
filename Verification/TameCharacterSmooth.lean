/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PartialPowerSmooth
import Verification.TorusSmooth

/-!
# Tame Character Smooth

Smoothness of the actual character-equation quotient in the tame
Smith case. The proof combines lattice Smith coordinates, equality of
equation ideals, and lifting on the explicit partial-power quotient.
This is an affine-ring statement; the identification with the original
cluster chart and the global normal-frame assertion are separate steps.
-/

noncomputable section
universe u v
namespace Verification.TameCharacterSmooth
open MonoidAlgebra
open Verification.PrimitiveCharacters Verification.SmithCharacters

variable {R M P ι : Type u} {κ : Type v}
  [CommRing R] [AddCommGroup M] [AddCommGroup P]

theorem partial_smooth [Fintype ι] [Finite κ]
    (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ)
    (hpos : ∀ k, 0 < e k) (he : ∀ k, IsUnit (e k : R)) :
    Algebra.Smooth R (PartialPowerSmooth.PartialAlgebra j e b) := by
  letI := TorusSmooth.torus_smooth R ι
  exact PartialPowerSmooth.partial_smooth j e b hpos he

def smithPositiveEquiv (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    (b : Basis κ ℤ P) {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n)
    (c : Multiplicative P →* Rˣ) :
    (MonoidAlgebra R (Multiplicative M) ⧸ columnIdeal f b c) ≃ₐ[R]
      PartialPowerSmooth.PartialAlgebra s.f (fun i => (s.a i).natAbs)
        (fun i => positiveConstant (s.a i) (smithConstants f hf s c i)) :=
  (smithFiberEquiv f hf b s c).trans
    (Ideal.quotientEquivAlgOfEq R (diagonalIdeal_eq_positiveIdeal s.f s.a
      (smithConstants f hf s c)))

theorem smith_character_smooth [Fintype ι]
    (f : P →ₗ[ℤ] M) (hf : Function.Injective f) (b : Basis κ ℤ P)
    {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n)
    (c : Multiplicative P →* Rˣ) (he : ∀ i, IsUnit ((s.a i).natAbs : R)) :
    Algebra.Smooth R (MonoidAlgebra R (Multiplicative M) ⧸ columnIdeal f b c) := by
  letI := partial_smooth s.f (fun i => (s.a i).natAbs)
    (fun i => positiveConstant (s.a i) (smithConstants f hf s c i))
    (fun i => Int.natAbs_pos.mpr (smith_coefficient_ne_zero s i)) he
  exact Algebra.Smooth.of_equiv (smithPositiveEquiv f hf b s c).symm

theorem smith_prescribed_smooth [Fintype ι]
    (f : P →ₗ[ℤ] M) (hf : Function.Injective f) (b : Basis κ ℤ P)
    {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n)
    (c : κ → Rˣ) (he : ∀ i, IsUnit ((s.a i).natAbs : R)) :
    Algebra.Smooth R (MonoidAlgebra R (Multiplicative M) ⧸ prescribedIdeal f b c) := by
  letI := smith_character_smooth f hf b s (basisCharacter b c) he
  exact Algebra.Smooth.of_equiv (Ideal.quotientEquivAlgOfEq R (prescribedIdeal_eq f b c)).symm

theorem independent_character_smooth_charZero {k : Type u} [Field k] [CharZero k] [Fintype ι]
    (bM : Basis ι ℤ M) (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    (bP : Basis κ ℤ P) (c : κ → kˣ) :
    Algebra.Smooth k (MonoidAlgebra k (Multiplicative M) ⧸ prescribedIdeal f bP c) := by
  obtain ⟨n,s⟩ := (LinearMap.range f).smithNormalForm bM
  apply smith_prescribed_smooth f hf bP s c
  intro i
  exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr
    (Int.natAbs_ne_zero.mpr (smith_coefficient_ne_zero s i)))

theorem smith_prescribed_smooth_char {k : Type u} [Field k] [Fintype ι]
    (p : ℕ) [CharP k p] (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    (bP : Basis κ ℤ P) {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n)
    (c : κ → kˣ) (he : ∀ i, ¬ p ∣ (s.a i).natAbs) :
    Algebra.Smooth k (MonoidAlgebra k (Multiplicative M) ⧸ prescribedIdeal f bP c) := by
  apply smith_prescribed_smooth f hf bP s c
  intro i
  exact isUnit_iff_ne_zero.mpr ((CharP.cast_eq_zero_iff k p _).not.mpr (he i))

#print axioms partial_smooth
#print axioms smithPositiveEquiv
#print axioms smith_character_smooth
#print axioms smith_prescribed_smooth
#print axioms independent_character_smooth_charZero
#print axioms smith_prescribed_smooth_char
end Verification.TameCharacterSmooth
