/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalizedActualTransverse
import Verification.LocalizedTorusContraction
import Verification.LocalizedAffineThomInvariance
import Verification.ActualOldTorusSmooth

/-!
# Original Localized Torus Contraction

The literal original adjacent boundary, with its actual new-first normal
frame, is the Laurent basepoint contraction followed by the actual fiber
restriction. All affine projection isomorphisms are consequences of uniform
localized affine homotopy invariance and proved smoothness of the actual rings.
-/
noncomputable section
namespace Verification.OriginalLocalizedTorusContraction
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Verification.IndependentBasicOpen Verification.IndependentChartIndex
open Verification.IndependentOpenCoordinates Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {Z : Type*} [Category Z] [Preadditive Z] [HasZeroObject Z] [HasShift Z ℤ]
variable [∀ m : ℤ, (CategoryTheory.shiftFunctor Z m).Additive] [Pretriangulated Z]
variable (L : DerivedCategory C ⥤ Z) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (J : Finset (Fin n)) (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Selected n J)
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (P : LocalizedCoordinatePurity.Standard L R G)
variable (N : LocalizedNormalizedFlag.Standard L R G E P)
variable (H : LocalizedAffineThomInvariance.Standard L R G)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hJ : Independent (laterWeights κ n B) J)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B J))
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B J)))
local notation "Sel" => Selected n J
local notation "K" => Other n J ⊕ κ
local notation "Rest" => Other n J
local notation "D" => matrix κ n J B
local notation "F" => AffineRelativeThom.theory R (CoordinateFlag.Old (Selected n J) v) G
local notation "T" => AffineRelativeThom.theory R (FlagNormalCoordinates.Normals (Selected n J) v) G ⋙ DerivedCategory.Q ⋙ L
local notation "S" => ActualAdjacentTorusBoundary.shiftedTheory R F ⋙ L
local notation "Q" => LocalizedActualFlag.principal L R n J v G E P N
local notation "hD" => matrix_zero_block κ n J B hpos hneg hsupport hJ
local notation "Fib" => ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R Sel K Rest D)
local notation "OldT" => ActualTorusFace.OldTorus R Sel K Rest D v

include H hpos hneg hsupport hJ hf hs

omit [Preadditive Z] [HasZeroObject Z] [∀ m : ℤ, (CategoryTheory.shiftFunctor Z m).Additive]
  [Pretriangulated Z] [L.Additive] [L.IsTriangulated] [Nontrivial R] [HasShift Z ℤ] [L.CommShift ℤ] in
theorem closed_projection : IsIso (PolynomialSectionIso.projectionMap R Fib Sel T) := by
  exact H.projection Fib (FlagNormalCoordinates.Normals Sel v) Sel
    (ActualTransversePairSmooth.pair_smooth_AS R Sel K Rest Sum.inl D hD hf hs v).1

omit [Preadditive Z] [HasZeroObject Z] [∀ m : ℤ, (CategoryTheory.shiftFunctor Z m).Additive]
  [Pretriangulated Z] [L.Additive] [L.IsTriangulated] [Nontrivial R] in
theorem old_projection : IsIso (PolynomialSectionIso.projectionMap R OldT
    (LocalTransverseOpen.Old v) S) := by
  exact LocalizedAffineThomInvariance.shifted_projection L R G H OldT
    (CoordinateFlag.Old Sel v) (LocalTransverseOpen.Old v)
    (ActualOldTorusSmooth.old_smooth R Sel K Rest Sum.inl D hD v hf hs)

omit [Preadditive Z] [HasZeroObject Z] [∀ m : ℤ, (CategoryTheory.shiftFunctor Z m).Additive]
  [Pretriangulated Z] [L.Additive] [L.IsTriangulated] [Nontrivial R] [HasShift Z ℤ] [L.CommShift ℤ] in
theorem line_projection : IsIso (L.map (DerivedCategory.Q.map
    (ActualTransverseBasepoint.lineProjection R Sel K Rest D F))) := by
  exact LocalizedAffineThomInvariance.polynomial_projection L R G H Fib
    (CoordinateFlag.Old Sel v)
    (ActualTransversePairSmooth.pair_smooth_AS R Sel K Rest Sum.inl D hD hf hs v).1

def closedIso :
    (T).obj (op (CommRingCat.mkUnder (CommRingCat.of R) Fib)) ≅
    (T).obj (op (CommRingCat.mkUnder (CommRingCat.of R)
      (ActualTransverseLocalization.ClosedSource R Sel K Rest Sum.inl D v))) := by
  letI := closed_projection L R κ n J B v G H hpos hneg hsupport hJ hf hs
  exact LocalizedSlicePurity.closedIso R Sel K Rest Sum.inl D hD v T

def oldIso :
    (S).obj (op (CommRingCat.mkUnder (CommRingCat.of R) OldT)) ≅
    (S).obj (op (CommRingCat.mkUnder (CommRingCat.of R)
      (ActualTransverseLocalization.OpenSource R Sel K Rest Sum.inl D v))) := by
  letI := old_projection L R κ n J B v G H hpos hneg hsupport hJ hf hs
  exact ActualTorusFace.oldIso R Sel K Rest Sum.inl D hD v S

def fiberThomIso : (T).obj (op (CommRingCat.mkUnder (CommRingCat.of R) Fib)) ≅
    L.obj (DerivedCategory.Q.obj
      ((kernel (ActualTransverseBasepoint.projection R Sel K Rest D F))⟦(1 : ℤ)⟧)) := by
  letI := line_projection L R κ n J B v G H hpos hneg hsupport hJ hf hs
  exact LocalizedTorusContraction.thomContractionIso R Sel K Rest Sum.inl D hD v hf hs L F T Q

def torusNormalIso : L.obj (CoordinatePurityInput.normalThom
    (BasicOpen R κ n J B) Sel (selectedCoordinate R κ n J B) G) ≅
    (T).obj (op (CommRingCat.mkUnder (CommRingCat.of R) Fib)) :=
  LocalizedActualTransverse.normalIso L R κ n J B v G ≪≫
    (closedIso L R κ n J B v G H hpos hneg hsupport hJ hf hs).symm

variable (M : Z)
omit [L.Additive] [Nontrivial R] in
theorem adjacent_on_sections
    (a : (S).obj (op (CommRingCat.mkUnder (CommRingCat.of R) OldT)) ⟶ M) :
    (LocalizedActualTransverse.normalIso L R κ n J B v G).hom ≫
      LocalizedActualTransverse.adjacentBoundary L R κ n J B v G E P N
        hpos hneg hsupport hJ hf hs ≫
      (oldIso L R κ n J B v G H hpos hneg hsupport hJ hf hs).inv ≫ a =
    (torusNormalIso L R κ n J B v G H hpos hneg hsupport hJ hf hs).hom ≫
      (fiberThomIso L R κ n J B v G E P N H hpos hneg hsupport hJ hf hs).hom ≫
      L.map (DerivedCategory.Q.map ((ActualTorusReducedRestriction.reducedRestriction
        R Sel K Rest D v F)⟦(1 : ℤ)⟧')) ≫
      LocalizedTorusContraction.oldContraction R Sel K Rest D v L F M a := by
  letI := closed_projection L R κ n J B v G H hpos hneg hsupport hJ hf hs
  letI := old_projection L R κ n J B v G H hpos hneg hsupport hJ hf hs
  letI := line_projection L R κ n J B v G H hpos hneg hsupport hJ hf hs
  have h := LocalizedTorusContraction.boundary_on_sections R Sel K Rest Sum.inl D hD v hf hs L F T Q M a
  have hh := congrArg (fun f =>
    (LocalizedActualTransverse.normalIso L R κ n J B v G).hom ≫
      (LocalizedSlicePurity.closedIso R Sel K Rest Sum.inl D hD v T).inv ≫ f) h
  simpa only [LocalizedTorusContraction.torusBoundary, torusNormalIso,
    closedIso, oldIso, fiberThomIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc] using hh

#print axioms closed_projection
#print axioms old_projection
#print axioms line_projection
#print axioms closedIso
#print axioms oldIso
#print axioms fiberThomIso
#print axioms torusNormalIso
#print axioms adjacent_on_sections
end Verification.OriginalLocalizedTorusContraction
