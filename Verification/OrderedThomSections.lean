/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinatePairTransport
import Verification.LocalizedThomSections
import Mathlib.Data.Finset.Sort

/-!
# Ordered Thom Sections

Thom evaluation in the explicitly increasing order on a finite normal
frame. All coefficients are evaluated on Fin r after a genuine coordinate
transport, so no cross-index convention is assumed of the input evaluator.
-/
noncomputable section
namespace Verification.OrderedThomSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable (ι : Type) [Fintype ι] [LinearOrder ι] (r : ℕ) (hr : Fintype.card ι = r)

def numbering : Fin r ≃ ι := (Fintype.orderIsoFinOfCardEq ι hr).toEquiv

variable (S : Type) [CommRing S]

theorem rename_normal (i : Fin r) :
    MvPolynomial.renameEquiv S (numbering ι r hr).symm
      (MvPolynomial.X (numbering ι r hr i)) = MvPolynomial.X i := by
  simp [MvPolynomial.renameEquiv_apply]

universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ)

def thomIso : LocalizedThomSections.thom G S ι ≅ LocalizedThomSections.thom G S (Fin r) :=
  CoordinatePairTransport.relativeIso MvPolynomial.X MvPolynomial.X (numbering ι r hr)
    (MvPolynomial.renameEquiv S (numbering ι r hr).symm).toRingEquiv
    (rename_normal ι r hr S) G

variable (R : Type) [CommRing R] [Algebra R S]
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (T : LocalizedThomSections.Standard J L G R site M N)

def evaluate (hs : Algebra.Smooth R S) (j : ℤ) :
    (L.obj (LocalizedThomSections.thom G S ι) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r : ℤ)) (M j)))) ≃+
    (N (j-r)).val.obj (Opposite.op (Spec (CommRingCat.of S))) := by
  refine (LocalizedThomSections.precompose (L.mapIso (thomIso ι r hr S G))).trans ?_
  have e := T.evaluate S (Fin r) hs j
  rw [Fintype.card_fin] at e
  exact e

#print axioms numbering
#print axioms rename_normal
#print axioms thomIso
#print axioms evaluate
end Verification.OrderedThomSections
