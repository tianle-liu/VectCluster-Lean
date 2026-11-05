/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OrderedFlagNormalCoordinates
import Verification.CoordinatePairTransport
import Verification.ThomPermutationInput

/-!
# Ordered Flag Thom Factorization

The actual derived normal-coordinate comparison, including its
punctured-scheme map, factors as the increasing-frame comparison followed
by the insertion permutation. This lifts the proved ring factorization
through genuine functorial maps of localization cones.
-/
noncomputable section
namespace Verification.OrderedFlagThomFactorization
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.OrderedFlagNormalCoordinates
variable (ι : Type) [Fintype ι] [LinearOrder ι] (v : ι)
variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (x : ι → A)

local notation "S" => CoordinateFlag.ClosedAll A ι x v
local notation "Q" => A ⧸ ConormalFrame.ideal x
local notation "F" => Fin (count ι v)
local notation "N" => FlagNormalCoordinates.Normals ι v

theorem numbering_normal (i : F) :
    normalNumbering ι v R A x (MvPolynomial.X (normalOrder ι v i)) = MvPolynomial.X i := by
  simp [normalNumbering,MvPolynomial.renameEquiv_apply]

theorem increasing_normal (i : F) :
    orderedEquiv ι v R A x (MvPolynomial.X (increasing ι v i)) = MvPolynomial.X i := by
  simp [orderedEquiv,MvPolynomial.mapAlgEquiv_apply,MvPolynomial.renameEquiv_apply]

theorem insertion_normal (i : F) :
    insertionEquiv ι v R A x (MvPolynomial.X ((insertion ι v).symm i)) = MvPolynomial.X i := by
  simp [insertionEquiv,MvPolynomial.renameEquiv_apply]

universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)

def newFirstIso : CoordinatePurityInput.normalThom A ι x G ≅ LocalizedThomSections.thom G S N :=
  CoordinatePairTransport.relativeIso MvPolynomial.X MvPolynomial.X (FlagNormalCoordinates.indexEquiv ι v)
    (FlagNormalCoordinates.algebraEquiv R A ι x v).toRingEquiv
    (FlagNormalCoordinates.algebraEquiv_normal R A ι x v) G

def numberingIso : LocalizedThomSections.thom G S N ≅ LocalizedThomSections.thom G S F :=
  CoordinatePairTransport.relativeIso MvPolynomial.X MvPolynomial.X (normalOrder ι v)
    (normalNumbering ι v R A x).toRingEquiv (numbering_normal ι v R A x) G

def increasingIso : CoordinatePurityInput.normalThom A ι x G ≅ LocalizedThomSections.thom G S F :=
  CoordinatePairTransport.relativeIso MvPolynomial.X MvPolynomial.X (increasing ι v)
    (orderedEquiv ι v R A x).toRingEquiv (increasing_normal ι v R A x) G

theorem coordinate_factorization :
    (newFirstIso ι v R A x G).hom ≫ (numberingIso ι v R A x G).hom =
      (increasingIso ι v R A x G).hom ≫
        (ThomPermutationInput.permutationIso G S F (insertion ι v).symm).hom := by
  change (CoordinatePairTransport.relativeIso _ _ _ _ _ G).hom ≫
    (CoordinatePairTransport.relativeIso _ _ _ _ _ G).hom =
    (CoordinatePairTransport.relativeIso _ _ _ _ _ G).hom ≫
    (CoordinatePairTransport.relativeIso MvPolynomial.X MvPolynomial.X (insertion ι v).symm
      (insertionEquiv ι v R A x).toRingEquiv (insertion_normal ι v R A x) G).hom
  rw [CoordinatePairTransport.relative_comp,CoordinatePairTransport.relative_comp]
  have hi : (normalOrder ι v).trans (FlagNormalCoordinates.indexEquiv ι v) =
      (insertion ι v).symm.trans (increasing ι v) := by
    ext i
    simp [normalOrder,newFirst]
  have he : (FlagNormalCoordinates.algebraEquiv R A ι x v).toRingEquiv.trans
      (normalNumbering ι v R A x).toRingEquiv =
      (orderedEquiv ι v R A x).toRingEquiv.trans (insertionEquiv ι v R A x).toRingEquiv :=
    congrArg AlgEquiv.toRingEquiv (algebra_factorization ι v R A x)
  congr 2

theorem actual_thom_factorization :
    (FlagNormalCoordinates.thomIso R A ι x v G).hom ≫
      (RelativeProductConeNaturality.derivedIso R S N G).hom ≫ (numberingIso ι v R A x G).hom =
    (increasingIso ι v R A x G).hom ≫
      (ThomPermutationInput.permutationIso G S F (insertion ι v).symm).hom := by
  have h : (FlagNormalCoordinates.thomIso R A ι x v G).hom =
      (newFirstIso ι v R A x G).hom ≫ (RelativeProductConeNaturality.derivedIso R S N G).inv := by
    simp only [FlagNormalCoordinates.thomIso,newFirstIso,CoordinatePairTransport.relativeIso,
      Iso.trans_hom,Iso.symm_hom,Category.assoc]
  rw [h]
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
  exact coordinate_factorization ι v R A x G

#print axioms numbering_normal
#print axioms increasing_normal
#print axioms insertion_normal
#print axioms newFirstIso
#print axioms numberingIso
#print axioms increasingIso
#print axioms coordinate_factorization
#print axioms actual_thom_factorization
end Verification.OrderedFlagThomFactorization
