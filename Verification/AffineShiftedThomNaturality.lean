/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AffineShiftedThomSections
import Verification.OrderedThomMapNaturality

/-!
# Affine Shifted Thom Naturality

Evaluation of shifted actual affine-Thom tests commutes with every
coefficient algebra map. The statement combines actual cone naturality,
canonical shift naturality, and ordinary coefficient-sheaf naturality.
-/
noncomputable section
namespace Verification.AffineShiftedThomNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
variable [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R S S' ι : Type) [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Fintype ι] [LinearOrder ι]
variable (r : ℕ) (hr : Fintype.card ι = r) (f : S →ₐ[R] S')
local notation "F" => AffineRelativeThom.theory R ι G
local notation "b" => op (CommRingCat.mkUnder (CommRingCat.of R) S)
local notation "b'" => op (CommRingCat.mkUnder (CommRingCat.of R) S')

omit [Preadditive D] [HasShift D ℤ] [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive]
  [L.Additive] [L.CommShift ℤ] [Fintype ι] [LinearOrder ι] in
theorem affine_inverse_square :
    (AffineShiftedThomSections.affineIso L G R S' ι).inv ≫ (DerivedCategory.Q ⋙ L).map ((F).map f.toUnder.op) =
      L.map (LocalizedThomSections.thomMap G f.toRingHom) ≫ (AffineShiftedThomSections.affineIso L G R S ι).inv := by
  apply (cancel_epi (AffineShiftedThomSections.affineIso L G R S' ι).hom).mp
  apply (cancel_mono (AffineShiftedThomSections.affineIso L G R S ι).hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  exact AffineShiftedThomSections.affine_base_square L G R S ι S' f

variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (hs : Algebra.Smooth R S) (hs' : Algebra.Smooth R S') (j : ℤ)

include hV in
omit [HasShift D ℤ] [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive]
  [J.CommShift ℤ] [L.CommShift ℤ] [J.Additive] [L.Additive] in
theorem evaluate_naturality
    (a : L.obj (DerivedCategory.Q.obj ((F).obj b)) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r : ℤ)) (M j)))) :
    AffineShiftedThomSections.evaluate J L G R S' ι r hr site M N V hs' j
      ((DerivedCategory.Q ⋙ L).map ((F).map f.toUnder.op) ≫ a) =
    (N (j-r)).val.map (Spec.map (CommRingCat.ofHom f.toRingHom)).op
      (AffineShiftedThomSections.evaluate J L G R S ι r hr site M N V hs j a) := by
  change OrderedThomSections.evaluate ι r hr S' J L G R site M N V hs' j
    ((AffineShiftedThomSections.affineIso L G R S' ι).inv ≫ ((DerivedCategory.Q ⋙ L).map ((F).map f.toUnder.op) ≫ a)) = _
  rw [← Category.assoc, affine_inverse_square, Category.assoc]
  exact OrderedThomMapNaturality.evaluate_naturality ι r hr J L G R site M N V hV f hs hs' j _

include hV in
omit [J.Additive] [L.Additive] in
theorem shifted_evaluate_naturality
    (a : L.obj (DerivedCategory.Q.obj (((F).obj b)⟦(1 : ℤ)⟧)) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-((r+1 : ℕ) : ℤ)) (M j)))) :
    AffineShiftedThomSections.shiftedEvaluate J L G R S' ι r hr site M N V hs' j
      ((DerivedCategory.Q ⋙ L).map (((F).map f.toUnder.op)⟦(1 : ℤ)⟧') ≫ a) =
    (N (j-r)).val.map (Spec.map (CommRingCat.ofHom f.toRingHom)).op
      (AffineShiftedThomSections.shiftedEvaluate J L G R S ι r hr site M N V hs j a) := by
  change AffineShiftedThomSections.evaluate J L G R S' ι r hr site M N V hs' j
    ((StrictPositiveCoefficientTests.suspendTest J r (M j) _).symm
      ((((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).app ((F).obj b')).inv ≫
        ((DerivedCategory.Q ⋙ L).map (((F).map f.toUnder.op)⟦(1 : ℤ)⟧') ≫ a))) = _
  simp only [Iso.app_inv]
  rw [← Category.assoc, ← (DerivedCategory.Q ⋙ L).commShiftIso_inv_naturality, Category.assoc,
    AffineShiftedThomSections.inverse_suspend_naturality]
  exact evaluate_naturality J L G R S S' ι r hr f site M N V hV hs hs' j _

#print axioms affine_inverse_square
#print axioms evaluate_naturality
#print axioms shifted_evaluate_naturality
end Verification.AffineShiftedThomNaturality
