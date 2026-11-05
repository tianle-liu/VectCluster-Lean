/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimitiveCharacters
import Verification.CharacterMapSmooth

/-!
# Torus Translation

A translation of an actual split-torus coordinate ring and extension of
prescribed scalar values on a primitive independent character family.
-/
noncomputable section
universe u
namespace Verification.TorusTranslation
open MonoidAlgebra Verification.CharacterMapSmooth
variable {R M P : Type u} [CommRing R] [AddCommGroup M] [AddCommGroup P]

def scalarCharacter (c : Multiplicative M →* Rˣ) : Multiplicative M →* Torus R M :=
  (algebraMap R (Torus R M)).toMonoidHom.comp ((Units.coeHom R).comp c)

def translationHom (c : Multiplicative M →* Rˣ) : Torus R M →ₐ[R] Torus R M :=
  MonoidAlgebra.lift R _ _ (scalarCharacter c * of R (Multiplicative M))

theorem translationHom_monomial (c : Multiplicative M →* Rˣ) (m : Multiplicative M) :
    translationHom c (of R (Multiplicative M) m) =
      algebraMap R (Torus R M) (c m : R) * of R (Multiplicative M) m := by
  simp [translationHom, scalarCharacter]

theorem translationHom_inv_comp (c : Multiplicative M →* Rˣ) :
    (translationHom c⁻¹).comp (translationHom c) = AlgHom.id R (Torus R M) := by
  apply MonoidAlgebra.algHom_ext
  intro m
  change translationHom c⁻¹ (translationHom c (of R (Multiplicative M) m)) =
    of R (Multiplicative M) m
  simp only [AlgHom.comp_apply, translationHom_monomial, map_mul, AlgHom.commutes,
    AlgHom.id_apply, MonoidHom.inv_apply]
  rw [← mul_assoc, ← map_mul]
  simp

def translation (c : Multiplicative M →* Rˣ) : Torus R M ≃ₐ[R] Torus R M :=
  AlgEquiv.ofAlgHom (translationHom c) (translationHom c⁻¹)
    (by simpa only [inv_inv] using translationHom_inv_comp c⁻¹) (translationHom_inv_comp c)

theorem translation_monomial (c : Multiplicative M →* Rˣ) (m : Multiplicative M) :
    translation c (of R (Multiplicative M) m) =
      algebraMap R (Torus R M) (c m : R) * of R (Multiplicative M) m :=
  translationHom_monomial c m

theorem primitive_character_extension [Module.Finite ℤ M]
    (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f))
    (c : Multiplicative P →* Rˣ) :
    ∃ d : Multiplicative M →* Rˣ, ∀ p,
      d (Multiplicative.ofAdd (f p)) = c (Multiplicative.ofAdd p) := by
  obtain ⟨e, he⟩ := Verification.PrimitiveLattice.primitive_columns_split_compatible f hf hs
  let r := (LinearMap.fst ℤ P (M ⧸ LinearMap.range f)).comp e.toLinearMap
  refine ⟨c.comp r.toAddMonoidHom.toMultiplicative, ?_⟩
  intro p
  change c (Multiplicative.ofAdd ((e (f p)).1)) = c (Multiplicative.ofAdd p)
  rw [he]

theorem primitive_translation [Module.Finite ℤ M]
    (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f))
    (c : Multiplicative P →* Rˣ) :
    ∃ e : Torus R M ≃ₐ[R] Torus R M, ∀ p,
      e (of R (Multiplicative M) (Multiplicative.ofAdd (f p))) =
        algebraMap R (Torus R M) (c (Multiplicative.ofAdd p) : R) *
          of R (Multiplicative M) (Multiplicative.ofAdd (f p)) := by
  obtain ⟨d, hd⟩ := primitive_character_extension f hf hs c
  exact ⟨translation d, fun p => by rw [translation_monomial, hd]⟩

#print axioms scalarCharacter
#print axioms translationHom
#print axioms translationHom_monomial
#print axioms translationHom_inv_comp
#print axioms translation
#print axioms translation_monomial
#print axioms primitive_character_extension
#print axioms primitive_translation
end Verification.TorusTranslation
