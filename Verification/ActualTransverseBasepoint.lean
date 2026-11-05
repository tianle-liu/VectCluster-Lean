/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualTransverseCone
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Actual Transverse Basepoint

The actual u=1 section of the open transverse line, used for the
manuscript's contraction splitting. The maps are on its literal Laurent
localization, and their retraction identity is proved before applying a theory.
-/
noncomputable section
namespace Verification.ActualTransverseBasepoint
open CategoryTheory Opposite
open Verification.ActualOpenChart Verification.ActualTransverseLocalization
open Verification.ExchangeTransverseSlice
universe u
variable (R ι κ τ : Type u) [CommRing R] [Fintype κ]
variable (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)

def polynomialOne : Slice (characters R ι κ τ B) →ₐ[R] Fiber (characters R ι κ τ B) :=
  (Polynomial.aeval (1 : Fiber (characters R ι κ τ B))).restrictScalars R

theorem polynomialOne_unit (m : Submonoid.powers (Polynomial.X : Slice (characters R ι κ τ B))) :
    IsUnit (polynomialOne R ι κ τ B m) := by
  obtain ⟨n,hn⟩ := m.2
  rw [← hn, map_pow]
  change IsUnit ((Polynomial.aeval (1 : Fiber (characters R ι κ τ B)) Polynomial.X) ^ n)
  rw [Polynomial.aeval_X, one_pow]
  exact isUnit_one

def atOne : OpenTarget R ι κ τ B →ₐ[R] Fiber (characters R ι κ τ B) :=
  IsLocalization.liftAlgHom (polynomialOne_unit R ι κ τ B)

def coefficient : Fiber (characters R ι κ τ B) →ₐ[R] OpenTarget R ι κ τ B :=
  IsScalarTower.toAlgHom R (Fiber (characters R ι κ τ B)) (OpenTarget R ι κ τ B)

theorem atOne_polynomial (p : Slice (characters R ι κ τ B)) :
    atOne R ι κ τ B (algebraMap (Slice (characters R ι κ τ B)) (OpenTarget R ι κ τ B) p) =
      polynomialOne R ι κ τ B p := IsLocalization.lift_eq _ _

theorem atOne_parameter :
    atOne R ι κ τ B (algebraMap (Slice (characters R ι κ τ B)) (OpenTarget R ι κ τ B) Polynomial.X) = 1 := by
  rw [atOne_polynomial]
  exact Polynomial.aeval_X _

theorem atOne_coefficient : (atOne R ι κ τ B).comp (coefficient R ι κ τ B) =
    AlgHom.id R (Fiber (characters R ι κ τ B)) := by
  ext a
  change atOne R ι κ τ B
    (algebraMap (Fiber (characters R ι κ τ B)) (OpenTarget R ι κ τ B) a) = a
  rw [IsScalarTower.algebraMap_apply (Fiber (characters R ι κ τ B))
    (Slice (characters R ι κ τ B)) (OpenTarget R ι κ τ B), atOne_polynomial]
  exact Polynomial.aeval_C _ _

variable {D : Type*} [Category D] (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ D)

def projection :
    F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (OpenTarget R ι κ τ B))) ⟶
      F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Fiber (characters R ι κ τ B)))) :=
  F.map (coefficient R ι κ τ B).toUnder.op

def sectionMap :
    F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Fiber (characters R ι κ τ B)))) ⟶
      F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (OpenTarget R ι κ τ B))) :=
  F.map (atOne R ι κ τ B).toUnder.op

theorem section_projection : sectionMap R ι κ τ B F ≫ projection R ι κ τ B F = 𝟙 _ := by
  unfold sectionMap projection
  rw [← Functor.map_comp]
  change F.map ((atOne R ι κ τ B).comp (coefficient R ι κ τ B)).toUnder.op = 𝟙 _
  rw [atOne_coefficient]
  exact F.map_id _

def lineProjection :
    F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Slice (characters R ι κ τ B)))) ⟶
      F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Fiber (characters R ι κ τ B)))) :=
  F.map (IsScalarTower.toAlgHom R (Fiber (characters R ι κ τ B))
    (Slice (characters R ι κ τ B))).toUnder.op

theorem open_line_projection {A : Type*} [Category A] [Preadditive A] [CategoryTheory.Limits.HasBinaryBiproducts A]
    (G : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex A ℤ) :
    ActualTransverseCone.sliceOpen R ι κ τ B G ≫ lineProjection R ι κ τ B G =
      projection R ι κ τ B G := by
  unfold ActualTransverseCone.sliceOpen lineProjection projection
  rw [← Functor.map_comp]
  rfl

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
#print axioms lineProjection
#print axioms open_line_projection
end Verification.ActualTransverseBasepoint
