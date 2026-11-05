/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AffineSheafContraction

/-!
# Sheaf Reduced Projection

Actual kernel projection is subtraction of the constant term at u=1.
-/
noncomputable section
namespace Verification.SheafReducedProjection
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


def coefficientPullback (q : ℤ) :
    (N q).val.obj (op (Spec (CommRingCat.of S))) →+
    (N q).val.obj (op (Spec (CommRingCat.of (LaurentBasepoint.Laurent S)))) where
  toFun a := (N q).val.map (Spec.map (CommRingCat.ofHom (LaurentBasepoint.coefficient R S).toRingHom)).op a
  map_zero' := map_zero _
  map_add' a b := map_add _ a b

variable [Algebra.Smooth R S] (j : ℤ)
set_option quotPrecheck false
local notation "F" => AffineRelativeThom.theory R ι G
local notation "Coef" => J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-((r+1 : ℕ) : ℤ)) (M j)))
local notation "baseEval" => AffineShiftedThomSections.shiftedEvaluate J L G R S ι r hr site M N V inferInstance j
local notation "laurentEval" => AffineShiftedThomSections.shiftedEvaluate J L G R (LaurentBasepoint.Laurent S) ι r hr site M N V
  (ActualOldFiberSmooth.laurent_smooth R S) j
local notation "point" => LocalizedSplitHomContraction.atBasepoint (LaurentBasepoint.sectionMap R S F) L (1 : ℤ) Coef
local notation "π" => LaurentBasepoint.projection R S F
local notation "σ" => LaurentBasepoint.sectionMap R S F
local notation "hσ" => LaurentBasepoint.section_projection R S F

include hV in
omit [J.Additive] in
theorem contraction_value
    (a : L.obj (DerivedCategory.Q.obj
      (((F).obj (op (CommRingCat.mkUnder (CommRingCat.of R) (LaurentBasepoint.Laurent S))))⟦(1 : ℤ)⟧)) ⟶ Coef) :
    (AffineSheafContraction.contractionEquiv J L G R S ι r hr site M N V hV j
      (LocalizedSplitHomContraction.contraction (π) L (1 : ℤ) Coef a)).val =
    (laurentEval) a - coefficientPullback R S site N (j-r)
      (AffineSheafContraction.sheafAtOne R S site N (j-r) ((laurentEval) a)) := by
  change (laurentEval) (LocalizedSplitHomContraction.extend (π) (σ) (hσ) L (1 : ℤ) Coef
    (LocalizedSplitHomContraction.contraction (π) L (1 : ℤ) Coef a)) = _
  have h := congrArg (fun b => (laurentEval) b)
    (LocalizedSplitHomContraction.decomposition (π) (σ) (hσ) L (1 : ℤ) Coef a)
  dsimp only at h
  rw [map_add] at h
  have hb := AffineShiftedThomNaturality.shifted_evaluate_naturality J L G R S
    (LaurentBasepoint.Laurent S) ι r hr (LaurentBasepoint.coefficient R S)
    site M N V hV inferInstance (ActualOldFiberSmooth.laurent_smooth R S) j ((point) a)
  change (laurentEval) (LocalizedSplitHomContraction.baseExtend (π) L (1 : ℤ) Coef ((point) a)) =
    coefficientPullback R S site N (j-r) ((baseEval) ((point) a)) at hb
  rw [hb,AffineSheafContraction.naturality_atOne J L G R S ι r hr site M N V hV j] at h
  exact eq_sub_of_add_eq h.symm

#print axioms coefficientPullback
#print axioms contraction_value
end Verification.SheafReducedProjection
