/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PowerTensorProduct
import Verification.PartialPowerProduct
import Verification.PartialPowerReindex
import Verification.CharacterMapSmooth

/-!
# Character Map Flat

Independent character maps are flat without tameness. Their actual
source algebra over the target torus is the already proved character graph
quotient, whose Smith presentation is a free module over the target.
-/
noncomputable section
universe u v
namespace Verification.CharacterMapFlat
open Verification.DiagonalPowerFibers Verification.PartialPowerProduct
open Verification.PrimitiveCharacters Verification.SmithCharacters
open Verification.CharacterMapSmooth
variable {R M P ι : Type u} {κ : Type v}
  [CommRing R] [AddCommGroup M] [AddCommGroup P]

theorem partial_free {J : Type u} [Finite J]
    (j : J ↪ ι) (e : J → ℕ) (b : J → Rˣ) (he : ∀ i, 0 < e i) :
    Module.Free R (Verification.PartialPowerSmooth.PartialAlgebra j e b) := by
  classical
  letI := Fintype.ofFinite J
  letI := Verification.PowerTensorProduct.power_free e b he
  letI : Module.Free R (ProductAlgebra j e b) := by
    change Module.Free R (Multiplicative (FreeIndex j →₀ ℤ) →₀ PowerAlgebra e b)
    infer_instance
  exact Module.Free.of_equiv (productEquiv j e b he).symm.toLinearEquiv

theorem smith_character_free (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    (b : Basis κ ℤ P) {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n)
    (c : Multiplicative P →* Rˣ) :
    Module.Free R (MonoidAlgebra R (Multiplicative M) ⧸ columnIdeal f b c) := by
  let d := (Verification.TameCharacterSmooth.smithPositiveEquiv f hf b s c).trans
    (Verification.PartialPowerReindex.reindexEquiv s.f (fun i => (s.a i).natAbs)
      (fun i => positiveConstant (s.a i) (smithConstants f hf s c i))
      (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n))
  letI : Module.Free R (Verification.PartialPowerSmooth.PartialAlgebra
      (Verification.PartialPowerReindex.reindexEmbedding s.f Equiv.ulift)
      ((fun i => (s.a i).natAbs) ∘ Equiv.ulift)
      ((fun i => positiveConstant (s.a i) (smithConstants f hf s c i)) ∘ Equiv.ulift)) :=
    partial_free _ _ _ (fun i => Int.natAbs_pos.mpr (smith_coefficient_ne_zero s i.down))
  exact Module.Free.of_equiv d.symm.toLinearEquiv

section GivenCharacter
variable [Algebra (Torus R P) (Torus R M)] [IsScalarTower R (Torus R P) (Torus R M)]

theorem free_of_character (f : P →ₗ[ℤ] M) (b : Basis κ ℤ P)
    (hchar : ∀ p, algebraMap (Torus R P) (Torus R M)
      (MonoidAlgebra.of R (Multiplicative P) (Multiplicative.ofAdd p)) =
        MonoidAlgebra.of R (Multiplicative M) (Multiplicative.ofAdd (f p)))
    (hf : Function.Injective f) {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n) :
    Module.Free (Torus R P) (Torus R M) := by
  letI := smith_character_free f hf b s (universalCharacter R P)
  exact Module.Free.of_equiv (graphEquiv f b hchar).toLinearEquiv

theorem flat_of_character (f : P →ₗ[ℤ] M) (b : Basis κ ℤ P)
    (hchar : ∀ p, algebraMap (Torus R P) (Torus R M)
      (MonoidAlgebra.of R (Multiplicative P) (Multiplicative.ofAdd p)) =
        MonoidAlgebra.of R (Multiplicative M) (Multiplicative.ofAdd (f p)))
    (hf : Function.Injective f) {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n) :
    Module.Flat (Torus R P) (Torus R M) := by
  letI := free_of_character f b hchar hf s
  infer_instance
end GivenCharacter

theorem characterMap_flat (f : P →ₗ[ℤ] M) (hf : Function.Injective f) (b : Basis κ ℤ P)
    {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n) :
    letI := (characterMap (R := R) f).toRingHom.toAlgebra
    Module.Flat (Torus R P) (Torus R M) := by
  letI := (characterMap (R := R) f).toRingHom.toAlgebra
  exact flat_of_character f b (characterMap_monomial f) hf s

#print axioms partial_free
#print axioms smith_character_free
#print axioms free_of_character
#print axioms flat_of_character
#print axioms characterMap_flat
end Verification.CharacterMapFlat
