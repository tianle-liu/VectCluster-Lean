/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AffineShiftedThomNaturality
import Verification.ActualLocalizedReducedSections
import Verification.ActualOldFiberSmooth

/-!
# Affine Sheaf Contraction

The reduced localized affine-Thom tests are the actual coefficient
sheaf's kernel of evaluation at u=1. This identifies the contraction group
from representability and naturality, rather than assuming its identification.
-/
noncomputable section
namespace Verification.AffineSheafContraction
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

def sheafAtOne (q : ℤ) :
    (N q).val.obj (op (Spec (CommRingCat.of (LaurentBasepoint.Laurent S)))) →+
    (N q).val.obj (op (Spec (CommRingCat.of S))) where
  toFun a := (N q).val.map (Spec.map (CommRingCat.ofHom (LaurentBasepoint.atOne R S).toRingHom)).op a
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
local notation "ε" => sheafAtOne R S site N (j-r)

include hV in
omit [J.Additive] [L.Additive] in
theorem naturality_atOne
    (a : L.obj (DerivedCategory.Q.obj
      (((F).obj (op (CommRingCat.mkUnder (CommRingCat.of R) (LaurentBasepoint.Laurent S))))⟦(1 : ℤ)⟧)) ⟶ Coef) :
    (baseEval) ((point) a) = (ε) ((laurentEval) a) := by
  exact AffineShiftedThomNaturality.shifted_evaluate_naturality J L G R (LaurentBasepoint.Laurent S) S ι r hr
    (LaurentBasepoint.atOne R S) site M N V hV (ActualOldFiberSmooth.laurent_smooth R S) inferInstance j a

def kernelEvaluation : ActualLocalizedReducedSections.sections R S F L (1 : ℤ) Coef ≃+ (ε).ker where
  toFun a := ⟨(laurentEval) a.val, by
    have h := naturality_atOne J L G R S ι r hr site M N V hV j a.val
    have ha : (point) a.val = 0 := a.property
    rw [ha, map_zero] at h
    exact h.symm⟩
  invFun a := ⟨(laurentEval).symm a.val, by
    apply (baseEval).injective
    rw [map_zero]
    have h := naturality_atOne J L G R S ι r hr site M N V hV j ((laurentEval).symm a.val)
    rw [AddEquiv.apply_symm_apply] at h
    exact h.trans a.property⟩
  left_inv a := by apply Subtype.ext; exact (laurentEval).symm_apply_apply a.val
  right_inv a := by apply Subtype.ext; exact (laurentEval).apply_symm_apply a.val
  map_add' a b := by
    apply Subtype.ext
    change (laurentEval) (a.val+b.val) = (laurentEval) a.val + (laurentEval) b.val
    exact (laurentEval).map_add a.val b.val

def contractionEquiv :
    (L.obj (DerivedCategory.Q.obj ((kernel (LaurentBasepoint.projection R S F))⟦(1 : ℤ)⟧)) ⟶ Coef) ≃+
    (ε).ker :=
  (ActualLocalizedReducedSections.equiv R S F L (1 : ℤ) Coef).trans
    (kernelEvaluation J L G R S ι r hr site M N V hV j)

#print axioms sheafAtOne
#print axioms naturality_atOne
#print axioms kernelEvaluation
#print axioms contractionEquiv
end Verification.AffineSheafContraction
