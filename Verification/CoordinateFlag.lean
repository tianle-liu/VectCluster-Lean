/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinatePurityInput
import Verification.TransverseConeBoundary

/-!
# Coordinate Flag

Literal coordinate flags and their support connecting maps. The old
closed subscheme, its principal open, and the final closed subscheme are
actual quotients/localizations. The boundary is constructed from genuine
open-scheme cone maps, before invoking any purity comparison.
-/
noncomputable section
namespace Verification.CoordinateFlag
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
variable (A ι : Type) [CommRing A] [Fintype ι] [DecidableEq ι]
variable (x : ι → A) (v : ι)

abbrev Old := {i : ι // i ≠ v}
def oldCoordinate (i : Old ι v) : A := x i.val
def oldIdeal : Ideal A := ConormalFrame.ideal (oldCoordinate A ι x v)
abbrev ClosedOld := A ⧸ oldIdeal A ι x v

def parameter : ClosedOld A ι x v := Ideal.Quotient.mk (oldIdeal A ι x v) (x v)
abbrev OpenOld := Localization.Away (parameter A ι x v)
def finalIdeal : Ideal (ClosedOld A ι x v) := Ideal.span ({parameter A ι x v} : Set _)
abbrev ClosedAll := ClosedOld A ι x v ⧸ finalIdeal A ι x v

def oldComplement : (Spec (CommRingCat.of A)).Opens :=
  CoordinatePurityInput.puncture A (Old ι v) (oldCoordinate A ι x v)
def fullComplement : (Spec (CommRingCat.of A)).Opens := CoordinatePurityInput.puncture A ι x

omit [Fintype ι] [DecidableEq ι] in
theorem complement_le : oldComplement A ι x v ≤ fullComplement A ι x := by
  apply iSup_le
  intro i
  exact le_iSup (fun j => PrimeSpectrum.basicOpen (x j)) i.val

def oldToFull : (oldComplement A ι x v).toScheme ⟶ (fullComplement A ι x).toScheme :=
  (Spec (CommRingCat.of A)).homOfLE (complement_le A ι x v)
def fullToAmbient : (fullComplement A ι x).toScheme ⟶ Spec (CommRingCat.of A) :=
  (fullComplement A ι x).ι

omit [Fintype ι] [DecidableEq ι] in
theorem open_triangle : oldToFull A ι x v ≫ fullToAmbient A ι x = (oldComplement A ι x v).ι :=
  Scheme.homOfLE_ι _ _

universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)

def firstArrow := G.map (oldToFull A ι x v)
def secondArrow := G.map (fullToAmbient A ι x)
def oldRelative : DerivedCategory C := DerivedCategory.Q.obj (mappingCone (firstArrow A ι x v G))
def fullRelative : DerivedCategory C := DerivedCategory.Q.obj (mappingCone (secondArrow A ι x G))

def boundary : fullRelative A ι x G ⟶
    DerivedCategory.Q.obj ((mappingCone (firstArrow A ι x v G))⟦(1 : ℤ)⟧) :=
  DerivedCategory.Q.map (TransverseConeBoundary.boundary (secondArrow A ι x G) ≫
    (mappingCone.inr (firstArrow A ι x v G))⟦(1 : ℤ)⟧')

#print axioms Old
#print axioms oldCoordinate
#print axioms oldIdeal
#print axioms ClosedOld
#print axioms parameter
#print axioms OpenOld
#print axioms finalIdeal
#print axioms ClosedAll
#print axioms oldComplement
#print axioms fullComplement
#print axioms complement_le
#print axioms oldToFull
#print axioms fullToAmbient
#print axioms open_triangle
#print axioms firstArrow
#print axioms secondArrow
#print axioms oldRelative
#print axioms fullRelative
#print axioms boundary
end Verification.CoordinateFlag
