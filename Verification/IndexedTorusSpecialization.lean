/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TorusCoordinateSpecialization

/-!
# Indexed Torus Specialization

The coordinate specialization theorem for an injectively indexed family
of pinned Laurent generators. The remaining coordinate names are retained.
-/
noncomputable section
namespace Verification.IndexedTorusSpecialization
open Verification.OriginalTorus Verification.FinsuppTorusUniversal
variable (R κ σ : Type) [CommRing R] (e : σ → κ) (he : Function.Injective e) (v : σ → Rˣ)

def rangeValue (p : Set.range e) : Rˣ := v ((Equiv.ofInjective e he).symm p)

def ideal : Ideal (Torus R κ) := Ideal.span (Set.range
  (fun i : σ => torusCoordinate R κ (e i)-algebraMap R _ (v i : R)))
abbrev Quotient := Torus R κ ⧸ ideal R κ σ e v

theorem rangeValue_apply (i : σ) : rangeValue R κ σ e he v ⟨e i,Set.mem_range_self i⟩=v i := by
  rw [rangeValue,Equiv.ofInjective_symm_apply]

theorem ideal_eq : ideal R κ σ e v=TorusCoordinateSpecialization.ideal R κ (Set.range e) (rangeValue R κ σ e he v) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    apply Ideal.subset_span
    refine ⟨⟨e i,Set.mem_range_self i⟩,?_⟩
    dsimp only
    rw [rangeValue_apply]
  · apply Ideal.span_le.mpr
    rintro _ ⟨p,rfl⟩
    apply Ideal.subset_span
    refine ⟨(Equiv.ofInjective e he).symm p,?_⟩
    dsimp only
    rw [Equiv.apply_ofInjective_symm he p]
    rfl

def specializationEquiv : Quotient R κ σ e v ≃ₐ[R] Torus R {i // i ∉ Set.range e} :=
  (Ideal.quotientEquivAlgOfEq R (ideal_eq R κ σ e he v)).trans
    (TorusCoordinateSpecialization.specializationEquiv R κ (Set.range e) (rangeValue R κ σ e he v))

theorem specialization_coordinate (i : κ) :
    specializationEquiv R κ σ e he v (Ideal.Quotient.mk (ideal R κ σ e v) (torusCoordinate R κ i))=
      (TorusCoordinateSpecialization.targetUnit R κ (Set.range e) (rangeValue R κ σ e he v) i : Torus R {i // i ∉ Set.range e}) :=
  TorusCoordinateSpecialization.specialization_coordinate R κ (Set.range e) (rangeValue R κ σ e he v) i

theorem specialization_free (i : {i // i ∉ Set.range e}) :
    specializationEquiv R κ σ e he v (Ideal.Quotient.mk (ideal R κ σ e v) (torusCoordinate R κ i.val))=
      torusCoordinate R _ i := by
  rw [specialization_coordinate,TorusCoordinateSpecialization.targetUnit,dif_neg i.property]
  rfl

theorem specialization_pinned (i : σ) :
    specializationEquiv R κ σ e he v (Ideal.Quotient.mk (ideal R κ σ e v) (torusCoordinate R κ (e i)))=
      algebraMap R _ (v i : R) := by
  rw [specialization_coordinate,TorusCoordinateSpecialization.targetUnit,dif_pos (Set.mem_range_self i)]
  rw [rangeValue_apply]
  rfl

#print axioms rangeValue
#print axioms ideal
#print axioms Quotient
#print axioms rangeValue_apply
#print axioms ideal_eq
#print axioms specializationEquiv
#print axioms specialization_coordinate
#print axioms specialization_free
#print axioms specialization_pinned
end Verification.IndexedTorusSpecialization
