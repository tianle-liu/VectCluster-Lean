/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AffineShiftedThomSections

/-!
# Affine Suspended Evaluation

Canonical suspension commutes with precomposition before affine Thom evaluation.
-/
noncomputable section
namespace Verification.AffineSuspendedEvaluation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
variable [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R S ι : Type) [CommRing R] [CommRing S] [Algebra R S]
variable [Fintype ι] [LinearOrder ι] (r : ℕ) (hr : Fintype.card ι = r)
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)


variable (hs : Algebra.Smooth R S) (j : ℤ)
local notation "F" => AffineRelativeThom.theory R ι G
local notation "B" => op (CommRingCat.mkUnder (CommRingCat.of R) S)

omit [J.Additive] [L.Additive] in
theorem evaluate_precompose {Y : D}
    (f : L.obj (DerivedCategory.Q.obj ((F).obj B)) ⟶ Y)
    (a : Y ⟶ J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r : ℤ)) (M j)))) :
    AffineShiftedThomSections.shiftedEvaluate J L G R S ι r hr site M N V hs j
      ((((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).app ((F).obj B)).hom ≫
        f⟦(1 : ℤ)⟧' ≫ StrictPositiveCoefficientTests.suspendTest J r (M j) Y a) =
    AffineShiftedThomSections.evaluate J L G R S ι r hr site M N V hs j (f ≫ a) := by
  change AffineShiftedThomSections.evaluate J L G R S ι r hr site M N V hs j
    ((StrictPositiveCoefficientTests.suspendTest J r (M j) _).symm
      ((((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).app ((F).obj B)).inv ≫
        ((((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).app ((F).obj B)).hom ≫
          f⟦(1 : ℤ)⟧' ≫ StrictPositiveCoefficientTests.suspendTest J r (M j) Y a))) = _
  rw [Iso.inv_hom_id_assoc,AffineShiftedThomSections.inverse_suspend_naturality,
    AddEquiv.symm_apply_apply]

#print axioms evaluate_precompose
end Verification.AffineSuspendedEvaluation
