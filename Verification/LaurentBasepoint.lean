/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualTransverseBasepoint

/-!
# Laurent Basepoint

The actual u=1 retraction of a Laurent line over any coefficient algebra.
These maps fix the basepoint used in contraction, before applying a theory.
-/
noncomputable section
namespace Verification.LaurentBasepoint
open CategoryTheory Opposite
universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

abbrev Laurent := Localization.Away (Polynomial.X : Polynomial A)

def polynomialOne : Polynomial A →ₐ[R] A := (Polynomial.aeval (1 : A)).restrictScalars R

theorem polynomialOne_unit (m : Submonoid.powers (Polynomial.X : Polynomial A)) :
    IsUnit (polynomialOne R A m) := by
  obtain ⟨n,hn⟩ := m.2
  rw [← hn,map_pow]
  change IsUnit ((Polynomial.aeval (1 : A) Polynomial.X) ^ n)
  rw [Polynomial.aeval_X,one_pow]
  exact isUnit_one

def atOne : Laurent A →ₐ[R] A := IsLocalization.liftAlgHom (polynomialOne_unit R A)

def coefficient : A →ₐ[R] Laurent A := IsScalarTower.toAlgHom R A (Laurent A)

theorem atOne_polynomial (p : Polynomial A) :
    atOne R A (algebraMap (Polynomial A) (Laurent A) p) = polynomialOne R A p :=
  IsLocalization.lift_eq _ _

theorem atOne_parameter :
    atOne R A (algebraMap (Polynomial A) (Laurent A) Polynomial.X) = 1 := by
  rw [atOne_polynomial]
  exact Polynomial.aeval_X _

theorem atOne_coefficient : (atOne R A).comp (coefficient R A) = AlgHom.id R A := by
  ext a
  change atOne R A (algebraMap A (Laurent A) a) = a
  rw [IsScalarTower.algebraMap_apply A (Polynomial A) (Laurent A),atOne_polynomial]
  exact Polynomial.aeval_C _ _

variable {D : Type*} [Category D] (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ D)

def projection : F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Laurent A))) ⟶
    F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) A)) := F.map (coefficient R A).toUnder.op

def sectionMap : F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) A)) ⟶
    F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Laurent A))) := F.map (atOne R A).toUnder.op

theorem section_projection : sectionMap R A F ≫ projection R A F = 𝟙 _ := by
  unfold sectionMap projection
  rw [← CategoryTheory.Functor.map_comp]
  change F.map ((atOne R A).comp (coefficient R A)).toUnder.op = 𝟙 _
  rw [atOne_coefficient]
  exact F.map_id _

#print axioms Laurent
#print axioms polynomialOne
#print axioms polynomialOne_unit
#print axioms atOne
#print axioms coefficient
#print axioms atOne_polynomial
#print axioms atOne_parameter
#print axioms atOne_coefficient
#print axioms projection
#print axioms sectionMap
#print axioms section_projection
end Verification.LaurentBasepoint
