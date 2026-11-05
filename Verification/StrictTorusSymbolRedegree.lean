/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictTorusSymbolInput
import Verification.OrderedThomEvaluation

/-!
# Strict Torus Symbol Redegree

The ordinary symbol projection normalization is unchanged by an
explicit cardinal rewrite of the single strict degree.
-/
noncomputable section
namespace Verification.StrictTorusSymbolRedegree
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.StrictSingleModel Verification.StrictTorusSymbolInput
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
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (H : Standard J L G R T Z M site N W V)
variable (ι τ κ : Type) [Fintype ι] [Fintype τ] [Fintype κ] [LinearOrder κ]
variable (r : ℕ) (hr : Fintype.card ι=r)

def cell : Cell J (-(r : ℤ)) (L.obj (TorusThomInput.thom R ι τ κ G)) :=
  redegree (T.cell ι τ κ) (by rw [hr])

def termIso : (cell J L G R T ι τ κ r hr).term ≅ (T.cell ι τ κ).term := by
  cases hr
  exact Iso.refl _

def split : (cell J L G R T ι τ κ r hr).term ≅
    ⨁ (summand Z M (Fintype.card ι) (Fintype.card κ)) :=
  termIso J L G R T ι τ κ r hr ≪≫ H.split ι τ κ

def projection (i : BinaryWordCoordinates.Index (Fintype.card κ))
    (hi : degree (Fintype.card ι) (Fintype.card κ) i≠0) :
    (cell J L G R T ι τ κ r hr).term ⟶ M (degree (Fintype.card ι) (Fintype.card κ) i) :=
  (termIso J L G R T ι τ κ r hr).hom ≫
    positiveProjection J L G R T Z M ι τ κ (H.split ι τ κ) i hi

omit [HasFiniteBiproducts D] [L.Additive] in
theorem symbols (i : BinaryWordCoordinates.Index (Fintype.card κ))
    (hi : degree (Fintype.card ι) (Fintype.card κ) i≠0) :
    GradedSectionTotal.includeDegree (W.grading (CommRingCat.of (TorusThomInput.BaseRing R τ κ)))
      (degree (Fintype.card ι) (Fintype.card κ) i-r)
      (OrderedThomEvaluation.degreeEvaluation J L G R site M N V
        (TorusThomInput.BaseRing R τ κ) r ι hr (baseSmooth R τ κ) _
        (StrictCellTests.testAddEquiv J (cell J L G R T ι τ κ r hr) _
          (projection J L G R T Z M site N W V H ι τ κ r hr i hi)))=
    OrderedBinaryWords.word (Fintype.card κ)
      (fun k=>(W.symbols (CommRingCat.of (TorusThomInput.BaseRing R τ κ))).symbol (baseUnit R τ κ k)) i := by
  cases hr
  simpa only [OrderedThomEvaluation.degreeEvaluation,cell,StrictSingleModel.redegree,
    projection,termIso,Iso.refl_hom,Category.id_comp] using H.positive_symbols ι τ κ i hi

#print axioms cell
#print axioms termIso
#print axioms split
#print axioms projection
#print axioms symbols
end Verification.StrictTorusSymbolRedegree
