/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OrderedThomBaseChange
import Verification.OrderedFlagNumbering

/-!
# Ordered Flag Base Factorization

Separate the genuine flag's increasing normal comparison into the
canonical increasing numbering and the actual coefficient quotient
isomorphism. This is the base identification needed for ordinary
Thom-evaluation naturality.
-/
noncomputable section
namespace Verification.OrderedFlagBaseFactorization
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.OrderedFlagNormalCoordinates Verification.OrderedFlagThomFactorization
variable (ι : Type) [Fintype ι] [LinearOrder ι] (v : ι)
variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (x : ι → A)
local notation "S" => CoordinateFlag.ClosedAll A ι x v
local notation "Q" => A ⧸ ConormalFrame.ideal x
local notation "e" => AlgEquiv.toRingEquiv (AlgEquiv.symm (CoordinateFlagTotalQuotient.equiv R A ι x v))
local notation "F" => Fin (count ι v)

theorem ring_factorization :
    (MvPolynomial.renameEquiv Q
      (OrderedThomSections.numbering ι (count ι v) (OrderedFlagNumbering.card_count ι v)).symm).toRingEquiv.trans
      (MvPolynomial.mapEquiv F e) = (orderedEquiv ι v R A x).toRingEquiv := by
  rw [← OrderedThomBaseChange.coefficient_numbering]
  simp only [orderedEquiv,OrderedFlagNumbering.increasing_numbering]
  rfl

universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)

theorem increasing_base :
    (OrderedThomSections.thomIso ι (count ι v) (OrderedFlagNumbering.card_count ι v) Q G).hom ≫
      (OrderedThomBaseChange.baseIso e G F).hom = (increasingIso ι v R A x G).hom := by
  rw [OrderedThomBaseChange.base_transport]
  simp only [OrderedThomSections.thomIso]
  rw [CoordinatePairTransport.relative_comp]
  have hi : (Equiv.refl F).trans
      (OrderedThomSections.numbering ι (count ι v) (OrderedFlagNumbering.card_count ι v)) =
      increasing ι v := (OrderedFlagNumbering.increasing_numbering ι v).symm
  have he := ring_factorization ι v R A x
  unfold increasingIso
  congr 2


theorem increasing_inverse : (increasingIso ι v R A x G).inv =
    (OrderedThomBaseChange.baseIso e G F).inv ≫
      (OrderedThomSections.thomIso ι (count ι v) (OrderedFlagNumbering.card_count ι v) Q G).inv := by
  apply (cancel_epi (increasingIso ι v R A x G).hom).mp
  rw [Iso.hom_inv_id,← increasing_base ι v R A x G]
  simp only [Category.assoc,Iso.hom_inv_id_assoc,Iso.hom_inv_id]

#print axioms ring_factorization
#print axioms increasing_base
#print axioms increasing_inverse
end Verification.OrderedFlagBaseFactorization
