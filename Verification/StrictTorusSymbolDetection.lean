/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictTorusSymbolInput
import Verification.FiniteSummandBoundaryDetection

/-!
# Strict Torus Symbol Detection

Actual standard strict-cell arrows are determined by their positive
Milnor-Witt projection tests. The integer projection is proved zero from
ordinary vanishing of the positive contractions of the integer sheaf.
Consequently the equality acts on Hom into every strict coefficient object.
-/
noncomputable section
namespace Verification.StrictTorusSymbolDetection
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.StrictSingleModel Verification.BinaryWordCoordinates
open Verification.StrictTorusSymbolInput
attribute [local instance] Abelian.hasFiniteBiproducts
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ) (R : Type) [CommRing R]
variable (T : StrictLocalizedCells.TorusCells J L G R)
variable (Z : A) (M : ℤ → A)

omit [HasDerivedCategory A] in
theorem integer_zero (hZ : ∀ k : ℤ,0<k → Subsingleton (M k ⟶ Z))
    (r n : ℕ) (hr : 0<r) {X : A} (e : X ≅ ⨁ (summand Z M r n)) (f : X ⟶ Z) : f=0 := by
  apply (cancel_epi e.inv).1
  apply biproduct.hom_ext'
  intro i
  have hpos:=degree_positive r n hr i
  have hh : Subsingleton (summand Z M r n i ⟶ Z) := by
    unfold summand
    rw [if_neg (ne_of_gt hpos)]
    exact hZ _ hpos
  exact hh.elim _ _

variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (H : Standard J L G R T Z M site N W V)
variable (ι τ κ ι' τ' κ' : Type)
variable [Fintype ι] [Fintype τ] [Fintype κ] [LinearOrder κ]
variable [Fintype ι'] [Fintype τ'] [Fintype κ'] [LinearOrder κ']

omit [HasFiniteBiproducts D] [L.Additive] in
theorem detect_total (hr : 0<Fintype.card ι)
    (d m : (T.cell ι τ κ).term ⟶ (T.cell ι' τ' κ').term)
    (h : ∀ (i : Index (Fintype.card κ'))
      (hi : degree (Fintype.card ι') (Fintype.card κ') i≠0),
      GradedSectionTotal.includeDegree (W.grading (CommRingCat.of (TorusThomInput.BaseRing R τ κ)))
        (degree (Fintype.card ι') (Fintype.card κ') i-Fintype.card ι)
        (sectionTest J L G R T M ι τ κ site N V _
          (d ≫ positiveProjection J L G R T Z M ι' τ' κ' (H.split ι' τ' κ') i hi)) =
      GradedSectionTotal.includeDegree (W.grading (CommRingCat.of (TorusThomInput.BaseRing R τ κ)))
        (degree (Fintype.card ι') (Fintype.card κ') i-Fintype.card ι)
        (sectionTest J L G R T M ι τ κ site N V _
          (m ≫ positiveProjection J L G R T Z M ι' τ' κ' (H.split ι' τ' κ') i hi))) : d=m := by
  apply (cancel_mono (H.split ι' τ' κ').hom).1
  apply biproduct.hom_ext
  intro i
  by_cases hi : degree (Fintype.card ι') (Fintype.card κ') i=0
  · have he : summand Z M (Fintype.card ι') (Fintype.card κ') i=Z := if_pos hi
    apply (cancel_mono (eqToHom he)).1
    exact (integer_zero Z M H.integer_contraction _ _ hr (H.split ι τ κ) _).trans
      (integer_zero Z M H.integer_contraction _ _ hr (H.split ι τ κ) _).symm
  · have hs:=GradedSectionTotal.includeDegree_injective
      (W.grading (CommRingCat.of (TorusThomInput.BaseRing R τ κ)))
      (degree (Fintype.card ι') (Fintype.card κ') i-Fintype.card ι) (h i hi)
    have hh:=(sectionTest J L G R T M ι τ κ site N V _).injective hs
    apply (cancel_mono (eqToHom (if_neg hi))).1
    simpa only [positiveProjection,projection,Category.assoc] using hh

#print axioms integer_zero
#print axioms detect_total
end Verification.StrictTorusSymbolDetection
