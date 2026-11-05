/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinateFlagTotalQuotient
import Verification.CoordinatePairReindex
import Verification.RelativeProductConeNaturality
import Verification.AffineRelativeThom
import Mathlib.Logic.Equiv.Option

/-!
# Flag Normal Coordinates

Literal normal coordinates for a flag: the newly inserted normal is
first (none), followed by the old normals. The coefficient quotient and
all normal variables are carried by actual algebra equivalences.
-/
noncomputable section
namespace Verification.FlagNormalCoordinates
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex Opposite
open Verification.CoordinateFlag Verification.CoordinatePurityInput
variable (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι] (x : ι → A) (v : ι)

abbrev Normals := Option (Old ι v)
def indexEquiv : Normals ι v ≃ ι := Equiv.optionSubtypeNe v

theorem indexEquiv_new : indexEquiv ι v none = v := rfl
theorem indexEquiv_old (i : Old ι v) : indexEquiv ι v (some i) = i.val := rfl

def algebraEquiv : MvPolynomial ι (A ⧸ ConormalFrame.ideal x) ≃ₐ[R]
    MvPolynomial (Normals ι v) (ClosedAll A ι x v) :=
  (MvPolynomial.mapAlgEquiv ι (CoordinateFlagTotalQuotient.equiv R A ι x v).symm).trans
    ((MvPolynomial.renameEquiv (ClosedAll A ι x v) (indexEquiv ι v).symm).restrictScalars R)

theorem algebraEquiv_normal (i : Normals ι v) :
    algebraEquiv R A ι x v (MvPolynomial.X (indexEquiv ι v i)) = MvPolynomial.X i := by
  simp [algebraEquiv,MvPolynomial.mapAlgEquiv_apply,MvPolynomial.renameEquiv_apply]

universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)

def thomIso : normalThom A ι x G ≅
    DerivedCategory.Q.obj ((AffineRelativeThom.theory R (Normals ι v) G).obj
      (op (CommRingCat.mkUnder (CommRingCat.of R) (ClosedAll A ι x v)))) :=
  CoordinatePairReindex.relativeIso (MvPolynomial ι (A ⧸ ConormalFrame.ideal x)) ι (Normals ι v)
    MvPolynomial.X (indexEquiv ι v) G ≪≫
    CoordinatePairEquiv.relativeIso (MvPolynomial.X ∘ indexEquiv ι v) MvPolynomial.X
      (algebraEquiv R A ι x v).toRingEquiv (algebraEquiv_normal R A ι x v) G ≪≫
        (RelativeProductConeNaturality.derivedIso R (ClosedAll A ι x v) (Normals ι v) G).symm

#print axioms Normals
#print axioms indexEquiv
#print axioms indexEquiv_new
#print axioms indexEquiv_old
#print axioms algebraEquiv
#print axioms algebraEquiv_normal
#print axioms thomIso
end Verification.FlagNormalCoordinates
