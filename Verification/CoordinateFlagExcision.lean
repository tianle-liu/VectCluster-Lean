/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinateFlag
import Verification.OpenOneExcision

/-!
# Coordinate Flag Excision

The old-support cone in an actual coordinate flag can be excised to
the original principal open x_v nonzero. The covering condition is proved
from the literal coordinate opens, and the positive boundary is retained.
-/
noncomputable section
namespace Verification.CoordinateFlagExcision
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.CoordinateFlag
variable (A ι : Type) [CommRing A] [Fintype ι] [DecidableEq ι] (x : ι → A) (v : ι)

omit [Fintype ι] [DecidableEq ι] in
theorem principal_le : PrimeSpectrum.basicOpen (x v) ≤ fullComplement A ι x :=
  le_iSup (fun i => PrimeSpectrum.basicOpen (x i)) v

omit [Fintype ι] [DecidableEq ι] in
theorem full_cover : fullComplement A ι x ≤ oldComplement A ι x v ⊔ PrimeSpectrum.basicOpen (x v) := by
  intro p hp
  change p ∈ (⨆ i,PrimeSpectrum.basicOpen (x i) : TopologicalSpace.Opens (PrimeSpectrum A)) at hp
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  change p ∈ oldComplement A ι x v ∨ p ∈ PrimeSpectrum.basicOpen (x v)
  by_cases h : i = v
  · right
    simpa only [h] using hi
  · left
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i,h⟩,hi⟩

universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
local notation "X" => Spec (CommRingCat.of A)
local notation "F" => Scheme.restrictFunctor (Spec (CommRingCat.of A)) ⋙ Over.forget (Spec (CommRingCat.of A)) ⋙ G

def principalCone : DerivedCategory C :=
  OpenConeExcision.localCone X F (oldComplement A ι x v)
    (fun _ : PUnit => PrimeSpectrum.basicOpen (x v)) PUnit.unit

def relativeIso : principalCone A ι x v G ≅ oldRelative A ι x v G :=
  OpenOneExcision.relativeIso G E X (oldComplement A ι x v) (fullComplement A ι x)
    (complement_le A ι x v) (PrimeSpectrum.basicOpen (x v)) (principal_le A ι x v) (full_cover A ι x v)

omit [Fintype ι] [DecidableEq ι] in
theorem relativeIso_boundary : (relativeIso A ι x v G E).hom ≫ TransverseDerivedBoundary.boundary (firstArrow A ι x v G) =
    TransverseDerivedBoundary.boundary (OpenConeExcision.localArrow X F (oldComplement A ι x v)
      (fun _ : PUnit => PrimeSpectrum.basicOpen (x v)) PUnit.unit) ≫
      DerivedCategory.Q.map (((F).map (homOfLE (inf_le_left : oldComplement A ι x v ⊓
        PrimeSpectrum.basicOpen (x v) ≤ oldComplement A ι x v)))⟦(1 : ℤ)⟧') :=
  OpenOneExcision.relativeIso_boundary G E X (oldComplement A ι x v) (fullComplement A ι x)
    (complement_le A ι x v) (PrimeSpectrum.basicOpen (x v)) (principal_le A ι x v) (full_cover A ι x v)

#print axioms principal_le
#print axioms full_cover
#print axioms principalCone
#print axioms relativeIso
#print axioms relativeIso_boundary
end Verification.CoordinateFlagExcision
