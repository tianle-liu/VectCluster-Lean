/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FinsuppTorusUniversal

/-!
# Torus Coordinate Specialization

Specializing any subset of Laurent coordinate units to specified scalar
units gives the Laurent algebra on the complementary coordinates, with
explicit maps in both directions and exact formulas on every generator.
-/
noncomputable section
namespace Verification.TorusCoordinateSpecialization
open Classical Verification.OriginalTorus Verification.FinsuppTorusUniversal
variable (R κ : Type) [CommRing R] (P : Set κ) (v : P → Rˣ)

def ideal : Ideal (Torus R κ) := Ideal.span (Set.range
  (fun p : P => torusCoordinate R κ p.val-algebraMap R _ (v p : R)))
abbrev Quotient := Torus R κ ⧸ ideal R κ P v

def targetUnit (i : κ) : (Torus R {i // i ∉ P})ˣ :=
  if hi : i ∈ P then Units.map (algebraMap R _).toMonoidHom (v ⟨i,hi⟩)
  else unit R _ ⟨i,hi⟩

def forward : Quotient R κ P v →ₐ[R] Torus R {i // i ∉ P} :=
  Ideal.Quotient.liftₐ (ideal R κ P v) (lift R κ (targetUnit R κ P v)) (by
    change ideal R κ P v ≤ RingHom.ker (lift R κ (targetUnit R κ P v)).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨p,rfl⟩
    change lift R κ (targetUnit R κ P v) (_-_)=0
    rw [map_sub,lift_coordinate,AlgHom.commutes,targetUnit,dif_pos p.property]
    exact sub_self _)

def quotientCoordinate (i : κ) : Quotient R κ P v :=
  Ideal.Quotient.mk (ideal R κ P v) (torusCoordinate R κ i)

def quotientUnit (i : κ) : (Quotient R κ P v)ˣ :=
  Units.map (Ideal.Quotient.mk (ideal R κ P v)).toMonoidHom (unit R κ i)

theorem quotient_relation (p : P) : quotientCoordinate R κ P v p.val=algebraMap R _ (v p : R) := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (ideal R κ P v) (torusCoordinate R κ p.val)-
    Ideal.Quotient.mk (ideal R κ P v) (algebraMap R _ (v p : R))=0
  rw [← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self p))

theorem forward_coordinate (i : κ) : forward R κ P v (quotientCoordinate R κ P v i)=
    (targetUnit R κ P v i : Torus R {i // i ∉ P}) := lift_coordinate R κ _ i

def backward : Torus R {i // i ∉ P} →ₐ[R] Quotient R κ P v :=
  lift R _ (fun i => quotientUnit R κ P v i.val)

theorem backward_coordinate (i : {i // i ∉ P}) : backward R κ P v (torusCoordinate R _ i)=
    quotientCoordinate R κ P v i.val := lift_coordinate R _ _ i

theorem backward_target (i : κ) : backward R κ P v (targetUnit R κ P v i : Torus R {i // i ∉ P})=
    quotientCoordinate R κ P v i := by
  classical
  rw [targetUnit]
  split_ifs with hi
  · change backward R κ P v (algebraMap R _ (v ⟨i,hi⟩ : R))=_
    rw [AlgHom.commutes]
    exact (quotient_relation R κ P v ⟨i,hi⟩).symm
  · exact backward_coordinate R κ P v ⟨i,hi⟩

theorem forward_backward : (forward R κ P v).comp (backward R κ P v)=AlgHom.id R _ := by
  apply FinsuppTorusUniversal.hom_ext
  intro i
  change forward R κ P v (backward R κ P v (torusCoordinate R _ i))=torusCoordinate R _ i
  rw [backward_coordinate,forward_coordinate,targetUnit,dif_neg i.property]
  rfl

theorem backward_forward : (backward R κ P v).comp (forward R κ P v)=AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  apply FinsuppTorusUniversal.hom_ext
  intro i
  change backward R κ P v (forward R κ P v (quotientCoordinate R κ P v i))=quotientCoordinate R κ P v i
  rw [forward_coordinate,backward_target]

def specializationEquiv : Quotient R κ P v ≃ₐ[R] Torus R {i // i ∉ P} :=
  AlgEquiv.ofAlgHom (forward R κ P v) (backward R κ P v)
    (forward_backward R κ P v) (backward_forward R κ P v)

theorem specialization_coordinate (i : κ) : specializationEquiv R κ P v (quotientCoordinate R κ P v i)=
    (targetUnit R κ P v i : Torus R {i // i ∉ P}) := forward_coordinate R κ P v i

#print axioms ideal
#print axioms Quotient
#print axioms targetUnit
#print axioms forward
#print axioms quotientCoordinate
#print axioms quotientUnit
#print axioms quotient_relation
#print axioms forward_coordinate
#print axioms backward
#print axioms backward_coordinate
#print axioms backward_target
#print axioms forward_backward
#print axioms backward_forward
#print axioms specializationEquiv
#print axioms specialization_coordinate
end Verification.TorusCoordinateSpecialization
