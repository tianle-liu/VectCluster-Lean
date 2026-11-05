/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AffineRelativeThom
import Verification.ActualAdjacentTorusBoundary
import Verification.PolynomialSectionIso
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Localized Affine Thom Invariance

Uniform affine homotopy invariance for relative Thom objects after
localization. This ordinary input ranges over all smooth affine algebras;
the shifted and one-variable forms are derived by actual coordinate maps.
-/
noncomputable section
namespace Verification.LocalizedAffineThomInvariance
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C]
  [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D] [HasShift D ℤ]
variable (L : DerivedCategory C ⥤ D) [L.CommShift ℤ]
variable (R : Type) [CommRing R] (G : Scheme ⥤ CochainComplex C ℤ)

structure Standard where
  projection : ∀ (A ν μ : Type) [CommRing A] [Algebra R A] [Fintype ν] [Fintype μ],
    Algebra.Smooth R A → IsIso (PolynomialSectionIso.projectionMap R A μ
      (AffineRelativeThom.theory R ν G ⋙ DerivedCategory.Q ⋙ L))

variable (H : Standard L R G)
variable (A ν μ : Type) [CommRing A] [Algebra R A] [Fintype ν] [Fintype μ]

include H in
theorem shifted_projection (h : Algebra.Smooth R A) :
    IsIso (PolynomialSectionIso.projectionMap R A μ
      (ActualAdjacentTorusBoundary.shiftedTheory R (AffineRelativeThom.theory R ν G) ⋙ L)) := by
  let f := (AffineRelativeThom.theory R ν G).map (PolynomialSectionIso.constant R A μ).toUnder.op
  have hi : IsIso ((DerivedCategory.Q ⋙ L).map f) := H.projection A ν μ h
  letI := hi
  have hs : IsIso (((DerivedCategory.Q ⋙ L) ⋙ CategoryTheory.shiftFunctor D (1 : ℤ)).map f) := by
    change IsIso (((DerivedCategory.Q ⋙ L).map f)⟦(1 : ℤ)⟧')
    infer_instance
  exact (NatIso.isIso_map_iff ((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)) f).mpr hs

include H in
omit [HasShift D ℤ] [L.CommShift ℤ] [Fintype μ] in
theorem polynomial_projection (h : Algebra.Smooth R A) :
    IsIso ((AffineRelativeThom.theory R ν G ⋙ DerivedCategory.Q ⋙ L).map
      (IsScalarTower.toAlgHom R A (Polynomial A)).toUnder.op) := by
  let T := AffineRelativeThom.theory R ν G ⋙ DerivedCategory.Q ⋙ L
  let e : MvPolynomial PUnit A ≃ₐ[R] Polynomial A :=
    (MvPolynomial.pUnitAlgEquiv A).restrictScalars R
  have he : e.toAlgHom.comp (PolynomialSectionIso.constant R A PUnit) =
      IsScalarTower.toAlgHom R A (Polynomial A) := by
    apply AlgHom.ext
    intro a
    exact (MvPolynomial.pUnitAlgEquiv A).commutes a
  have hf : T.map (IsScalarTower.toAlgHom R A (Polynomial A)).toUnder.op =
      T.map e.toUnder.op.hom ≫ PolynomialSectionIso.projectionMap R A PUnit T := by
    unfold PolynomialSectionIso.projectionMap
    rw [← Functor.map_comp]
    change T.map (IsScalarTower.toAlgHom R A (Polynomial A)).toUnder.op =
      T.map (e.toAlgHom.comp (PolynomialSectionIso.constant R A PUnit)).toUnder.op
    rw [he]
  letI : IsIso (PolynomialSectionIso.projectionMap R A PUnit T) := H.projection A ν PUnit h
  rw [hf]
  infer_instance

#print axioms Standard
#print axioms shifted_projection
#print axioms polynomial_projection
end Verification.LocalizedAffineThomInvariance
