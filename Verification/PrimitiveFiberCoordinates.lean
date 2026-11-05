/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimitiveCharacters

/-!
# Primitive Fiber Coordinates

Coordinate formula for the primitive translated character fiber.
Every original torus monomial becomes a unit scalar times the monomial
of its quotient-lattice class; the scalar is constructed from a section.
-/
noncomputable section
namespace Verification.PrimitiveFiberCoordinates
open MonoidAlgebra Verification.PrimitiveCharacters Verification.CharacterGenerators
open Verification.SplitTorusFiber Verification.PrimitiveLattice
variable {R M P Q ι : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup P] [AddCommGroup Q]

theorem splitting_monomial
    (e : M ≃ₗ[ℤ] (P × Q)) (f : P →ₗ[ℤ] M)
    (he : ∀ p, e (f p) = (p,0)) (b : Basis ι ℤ P)
    (c : Multiplicative P →* Rˣ) (m : M) :
    fiberEquivOfSplitting e f he b c
      (Ideal.Quotient.mk (columnIdeal f b c) (of R _ (Multiplicative.ofAdd m))) =
      algebraMap R _ (c (Multiplicative.ofAdd (e m).1) : R) *
        of R _ (Multiplicative.ofAdd (e m).2) := by
  change generatedFiberEquiv c (fun i => Multiplicative.ofAdd (b i)) (basis_generates b)
    (Ideal.Quotient.mk _ ((domCongr R R (groupSplitting e))
      (of R _ (Multiplicative.ofAdd m)))) = _
  have hm : (domCongr R R (groupSplitting e)) (of R _ (Multiplicative.ofAdd m)) =
      of R (Multiplicative P × Multiplicative Q)
        (Multiplicative.ofAdd (e m).1, Multiplicative.ofAdd (e m).2) := by
    change (domCongr R R (groupSplitting e)) (Finsupp.single _ 1) = Finsupp.single _ 1
    rw [domCongr_single]
    rfl
  rw [hm]
  change specialize c (of R (Multiplicative P × Multiplicative Q)
    (Multiplicative.ofAdd (e m).1, Multiplicative.ofAdd (e m).2)) = _
  exact specialize_monomial c _ _

def extensionCharacter (e : M ≃ₗ[ℤ] (P × Q)) (c : Multiplicative P →* Rˣ) :
    Multiplicative M →* Rˣ :=
  c.comp (((LinearMap.fst ℤ P Q).comp e.toLinearMap).toAddMonoidHom.toMultiplicative)

theorem extensionCharacter_apply (e : M ≃ₗ[ℤ] (P × Q)) (c : Multiplicative P →* Rˣ) (m : M) :
    extensionCharacter e c (Multiplicative.ofAdd m) = c (Multiplicative.ofAdd (e m).1) := rfl

theorem primitive_monomials [Module.Finite ℤ M]
    (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f))
    (b : Basis ι ℤ P) (c : Multiplicative P →* Rˣ) :
    ∃ (e : (MonoidAlgebra R (Multiplicative M) ⧸ columnIdeal f b c) ≃ₐ[R]
      MonoidAlgebra R (Multiplicative (M ⧸ LinearMap.range f)))
      (d : Multiplicative M →* Rˣ),
      (∀ p, d (Multiplicative.ofAdd (f p)) = c (Multiplicative.ofAdd p)) ∧
      ∀ m, e (Ideal.Quotient.mk _ (of R _ (Multiplicative.ofAdd m))) =
        algebraMap R _ (d (Multiplicative.ofAdd m) : R) *
          of R _ (Multiplicative.ofAdd ((LinearMap.range f).mkQ m)) := by
  obtain ⟨t,ht⟩ := quotient_section (LinearMap.range f) hs
  let s := columnSplitting f hf t ht
  have hsf : ∀ p, s (f p) = (p,0) := columnSplitting_apply f hf t ht
  refine ⟨fiberEquivOfSplitting s f hsf b c, extensionCharacter s c, ?_, ?_⟩
  · intro p
    rw [extensionCharacter_apply, hsf]
  · intro m
    rw [splitting_monomial, extensionCharacter_apply]
    rfl

#print axioms splitting_monomial
#print axioms extensionCharacter
#print axioms extensionCharacter_apply
#print axioms primitive_monomials
end Verification.PrimitiveFiberCoordinates
