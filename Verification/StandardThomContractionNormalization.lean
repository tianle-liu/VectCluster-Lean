/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StandardLineThomContraction
import Verification.AffineSheafContraction
import Verification.LocalizedAffineThomInvariance

/-!
# Standard Thom Contraction Normalization

Uniform ordinary Thom/suspension representability normalization.
The coefficient grading identifies the genuine u=1 kernel with the next
contraction sheaf. The additional reference compatibility is only for the
standard (A1,Gm) pair over every smooth algebra and arbitrary normal rank.
It fixes relative rank normalizations absent from base naturality alone.
No exchange matrix, stratum, flag attachment, or cellular differential
occurs in this reference interface.
-/
noncomputable section
namespace Verification.StandardThomContractionNormalization
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [Pretriangulated D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [CommRing R]
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (H : LocalizedAffineThomInvariance.Standard L R G)

structure Grading where
  contract : ∀ (S : Type) [CommRing S] [Algebra R S], Algebra.Smooth R S → ∀ q : ℤ,
    (AffineSheafContraction.sheafAtOne R S site N q).ker ≃+
      (N (q-1)).val.obj (op (Spec (CommRingCat.of S)))

def degreeCast (S : Type) [CommRing S] (q q' : ℤ) (h : q=q') :
    (N q).val.obj (op (Spec (CommRingCat.of S))) ≃+
      (N q').val.obj (op (Spec (CommRingCat.of S))) := by
  subst q'
  exact AddEquiv.refl _

def lower (K : Grading R site N) (S : Type) [CommRing S] [Algebra R S]
    (hs : Algebra.Smooth R S) (r : ℕ) (j : ℤ) :
    (AffineSheafContraction.sheafAtOne R S site N (j-r)).ker ≃+
      (N (j-(r+1 : ℕ))).val.obj (op (Spec (CommRingCat.of S))) :=
  (K.contract S hs (j-r)).trans (degreeCast site N S _ _ (by omega))

variable (μ : Type) [Fintype μ] [LinearOrder μ] (r : ℕ) (hr : Fintype.card μ = r)
set_option quotPrecheck false
local notation "F" => AffineRelativeThom.theory R μ G
local notation "T" => AffineRelativeThom.theory R (Option μ) G ⋙ DerivedCategory.Q ⋙ L
variable (P : LocalizedPrincipalPurity.Standard L R
  (AffineRelativeThom.theory R μ G)
  (AffineRelativeThom.theory R (Option μ) G ⋙ DerivedCategory.Q ⋙ L))

def lineIso (S : Type) [CommRing S] [Algebra R S] (hs : Algebra.Smooth R S) :
    (T).obj (op (CommRingCat.mkUnder (CommRingCat.of R) S)) ≅
      L.obj (DerivedCategory.Q.obj ((kernel (LaurentBasepoint.projection R S F))⟦(1 : ℤ)⟧)) := by
  letI := hs
  letI : IsIso (L.map (DerivedCategory.Q.map (StandardLineThomContraction.lineProjection R S F))) :=
    LocalizedAffineThomInvariance.polynomial_projection L R G H S μ hs
  exact StandardLineThomContraction.thomIso R S L F T P

local instance optionOrder : LinearOrder (Option μ) := inferInstanceAs (LinearOrder (WithBot μ))

structure Standard (K : Grading R site N) : Prop where
  standard_line : ∀ (S : Type) [CommRing S] [Algebra R S] (hs : Algebra.Smooth R S)
    (j : ℤ)
    (a : L.obj (DerivedCategory.Q.obj ((kernel (LaurentBasepoint.projection R S F))⟦(1 : ℤ)⟧)) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-((r+1 : ℕ) : ℤ)) (M j)))),
    AffineShiftedThomSections.evaluate J L G R S (Option μ) (r+1)
      (by simp only [Fintype.card_option, hr]) site M N V hs j
      ((lineIso (L := L) (G := G) (R := R) H μ P S hs).hom ≫ a) =
    lower R site N K S hs r j
      (by
        letI := hs
        exact AffineSheafContraction.contractionEquiv J L G R S μ r hr site M N V hV j a)


#print axioms Grading
#print axioms degreeCast
#print axioms lower
#print axioms lineIso
#print axioms optionOrder
#print axioms Standard
end Verification.StandardThomContractionNormalization
