/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictPositiveCoefficientTests
import Verification.OrderedThomSections
import Verification.AffineRelativeThom

/-!
# Affine Shifted Thom Sections

Shifted affine relative-Thom tests are evaluated on the coefficient
sheaf using the actual affine cone isomorphism, explicit normal numbering,
and canonical suspension. No compatibility with a cluster boundary is input.
-/
noncomputable section
namespace Verification.AffineShiftedThomSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
variable [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ]

omit [J.Additive] in
theorem suspend_naturality (r : ℕ) (M : A) {X Y : D} (f : X ⟶ Y)
    (a : Y ⟶ J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r : ℤ)) M))) :
    StrictPositiveCoefficientTests.suspendTest J r M X (f ≫ a) =
      f⟦(1 : ℤ)⟧' ≫ StrictPositiveCoefficientTests.suspendTest J r M Y a := by
  apply (StrictCoefficientBoundaryEvaluation.shiftTest J r M _).injective
  rw [StrictPositiveCoefficientTests.deshift_suspend,
    StrictCoefficientBoundaryEvaluation.shiftTest_precomp, StrictPositiveCoefficientTests.deshift_suspend]
  have h := (shiftFunctorCompIsoId D (1 : ℤ) (-1) (by omega)).hom.naturality f
  have hn : f⟦(1 : ℤ)⟧'⟦(-1 : ℤ)⟧' ≫ (shiftShiftNeg Y (1 : ℤ)).hom =
      (shiftShiftNeg X (1 : ℤ)).hom ≫ f := by
    simpa only [shiftShiftNeg, shiftEquiv, shiftEquiv', Iso.symm_hom, Iso.app_hom,
      Functor.comp_map, Functor.id_map] using h
  simpa only [Category.assoc] using congrArg (fun t => t ≫ a) hn.symm

omit [J.Additive] in
theorem inverse_suspend_naturality (r : ℕ) (M : A) {X Y : D} (f : X ⟶ Y)
    (a : Y⟦(1 : ℤ)⟧ ⟶ J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-((r+1 : ℕ) : ℤ)) M))) :
    (StrictPositiveCoefficientTests.suspendTest J r M X).symm (f⟦(1 : ℤ)⟧' ≫ a) =
      f ≫ (StrictPositiveCoefficientTests.suspendTest J r M Y).symm a := by
  apply (StrictPositiveCoefficientTests.suspendTest J r M X).injective
  rw [AddEquiv.apply_symm_apply, suspend_naturality, AddEquiv.apply_symm_apply]

variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R S ι : Type) [CommRing R] [CommRing S] [Algebra R S]
variable [Fintype ι] [LinearOrder ι] (r : ℕ) (hr : Fintype.card ι = r)
local notation "F" => AffineRelativeThom.theory R ι G
local notation "B" => op (CommRingCat.mkUnder (CommRingCat.of R) S)

def affineIso : L.obj (DerivedCategory.Q.obj ((F).obj B)) ≅
    L.obj (LocalizedThomSections.thom G S ι) :=
  L.mapIso (RelativeProductConeNaturality.derivedIso R S ι G)

variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hs : Algebra.Smooth R S) (j : ℤ)

def evaluate :
    (L.obj (DerivedCategory.Q.obj ((F).obj B)) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r : ℤ)) (M j)))) ≃+
    (N (j-r)).val.obj (op (Spec (CommRingCat.of S))) :=
  (LocalizedThomSections.precompose (affineIso L G R S ι)).trans
    (OrderedThomSections.evaluate ι r hr S J L G R site M N V hs j)

def shiftedEvaluate :
    (L.obj (DerivedCategory.Q.obj (((F).obj B)⟦(1 : ℤ)⟧)) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-((r+1 : ℕ) : ℤ)) (M j)))) ≃+
    (N (j-r)).val.obj (op (Spec (CommRingCat.of S))) :=
  (LocalizedThomSections.precompose (((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).app ((F).obj B))).trans
    ((StrictPositiveCoefficientTests.suspendTest J r (M j) _).symm.trans
      (evaluate J L G R S ι r hr site M N V hs j))

variable (S' : Type) [CommRing S'] [Algebra R S'] (f : S →ₐ[R] S')

omit [Preadditive D] [HasShift D ℤ] [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive]
  [L.Additive] [L.CommShift ℤ] [Fintype ι] [LinearOrder ι] in
theorem affine_base_square :
    (DerivedCategory.Q ⋙ L).map ((F).map f.toUnder.op) ≫ (affineIso L G R S ι).hom =
      (affineIso L G R S' ι).hom ≫ L.map (LocalizedThomSections.thomMap G f.toRingHom) := by
  have h := congrArg L.map (RelativeProductConeNaturality.derived_naturality R S S' ι G f)
  simpa only [affineIso, Functor.mapIso_hom, Functor.map_comp] using h

#print axioms suspend_naturality
#print axioms inverse_suspend_naturality
#print axioms affineIso
#print axioms evaluate
#print axioms shiftedEvaluate
#print axioms affine_base_square
end Verification.AffineShiftedThomSections
