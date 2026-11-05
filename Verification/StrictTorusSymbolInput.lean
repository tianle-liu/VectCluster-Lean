/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictLocalizedCells
import Verification.LocalizedThomSections
import Verification.GradedMilnorWittSheaf
import Verification.GradedBinaryCoefficientTree
import Verification.TorusModelWordBasis

/-!
# Strict Torus Symbol Input

Ordinary universal symbol normalization for standard split torus--Thom
objects. All bases, affine factors and normal ranks are arbitrary. Only
positive-weight projections are evaluated in Milnor-Witt sheaves; the
weight-zero integer object remains separate. No exchange data, filtration,
boundary or family-specific matrix occurs in this reference interface.
-/
noncomputable section
namespace Verification.StrictTorusSymbolInput
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.StrictSingleModel Verification.BinaryWordCoordinates
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

def degree (r n : ℕ) (i : Index n) : ℤ := (r : ℤ)+GradedBinaryCoefficientTree.weight n i

theorem weight_nonneg (n : ℕ) (i : Index n) : 0≤GradedBinaryCoefficientTree.weight n i := by
  induction n with
  | zero => exact le_refl 0
  | succ n ih =>
    rcases i with ⟨b,i⟩
    cases b
    · exact ih i
    · change 0≤1+GradedBinaryCoefficientTree.weight n i
      have hh:=ih i
      omega

theorem degree_positive (r n : ℕ) (hr : 0<r) (i : Index n) : 0<degree r n i := by
  have hh:=weight_nonneg n i
  unfold degree
  omega

def summand (r n : ℕ) (i : Index n) : A := if degree r n i=0 then Z else M (degree r n i)

variable (ι τ κ : Type) [Fintype ι] [Fintype τ] [Fintype κ] [LinearOrder κ]

def baseSmooth : Algebra.Smooth R (TorusThomInput.BaseRing R τ κ) := by
  letI := TorusSmooth.torus_smooth R κ
  letI : Algebra.Smooth (OriginalTorus.Torus R κ) (TorusThomInput.BaseRing R τ κ) := {}
  exact Algebra.Smooth.comp R (OriginalTorus.Torus R κ) (TorusThomInput.BaseRing R τ κ)

def baseUnit (i : Fin (Fintype.card κ)) : (TorusThomInput.BaseRing R τ κ)ˣ :=
  Units.map (MvPolynomial.C : OriginalTorus.Torus R κ →+* TorusThomInput.BaseRing R τ κ).toMonoidHom
    (FinsuppTorusUniversal.unit R κ (TorusModelWordBasis.ordering κ i))

variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (V : LocalizedThomSections.Standard J L G R site M N)

def projection (e : (T.cell ι τ κ).term ≅ ⨁ (summand Z M (Fintype.card ι) (Fintype.card κ)))
    (i : Index (Fintype.card κ)) :
    (T.cell ι τ κ).term ⟶ summand Z M (Fintype.card ι) (Fintype.card κ) i :=
  e.hom ≫ biproduct.π _ i

def positiveProjection
    (e : (T.cell ι τ κ).term ≅ ⨁ (summand Z M (Fintype.card ι) (Fintype.card κ)))
    (i : Index (Fintype.card κ)) (hi : degree (Fintype.card ι) (Fintype.card κ) i≠0) :
    (T.cell ι τ κ).term ⟶ M (degree (Fintype.card ι) (Fintype.card κ) i) :=
  projection J L G R T Z M ι τ κ e i ≫ eqToHom (if_neg hi)

def sectionTest (j : ℤ) :
    ((T.cell ι τ κ).term ⟶ M j) ≃+
      SheafGradedLaurentResidue.Section site N
        (CommRingCat.of (TorusThomInput.BaseRing R τ κ)) (j-Fintype.card ι) :=
  (StrictCellTests.testAddEquiv J (T.cell ι τ κ) (M j)).trans
    (V.evaluate (TorusThomInput.BaseRing R τ κ) ι (baseSmooth R τ κ) j)

structure Standard where
  split : ∀ (ι τ κ : Type) [Fintype ι] [Fintype τ] [Fintype κ] [LinearOrder κ],
    (T.cell ι τ κ).term ≅ ⨁ (summand Z M (Fintype.card ι) (Fintype.card κ))
  positive_symbols : ∀ (ι τ κ : Type) [Fintype ι] [Fintype τ] [Fintype κ] [LinearOrder κ]
    (i : Index (Fintype.card κ)) (hi : degree (Fintype.card ι) (Fintype.card κ) i≠0),
    GradedSectionTotal.includeDegree (W.grading (CommRingCat.of (TorusThomInput.BaseRing R τ κ)))
      (degree (Fintype.card ι) (Fintype.card κ) i-Fintype.card ι)
      (sectionTest J L G R T M ι τ κ site N V _
        (positiveProjection J L G R T Z M ι τ κ (split ι τ κ) i hi)) =
    OrderedBinaryWords.word (Fintype.card κ)
      (fun k => (W.symbols (CommRingCat.of (TorusThomInput.BaseRing R τ κ))).symbol (baseUnit R τ κ k)) i
  integer_contraction : ∀ k : ℤ,0<k → Subsingleton (M k ⟶ Z)

#print axioms degree
#print axioms weight_nonneg
#print axioms degree_positive
#print axioms summand
#print axioms baseSmooth
#print axioms baseUnit
#print axioms projection
#print axioms positiveProjection
#print axioms sectionTest
#print axioms Standard
end Verification.StrictTorusSymbolInput
