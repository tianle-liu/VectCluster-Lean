/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OrderedThomSections
import Verification.CoordinatePairEquivMap

/-!
# Ordered Thom Base Change

Increasing Thom coordinates commute with actual coefficient-ring
isomorphisms. Evaluation therefore has the usual base pullback
naturality without any cross-index normalization input.
-/
noncomputable section
namespace Verification.OrderedThomBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable (ι : Type) [Fintype ι] [LinearOrder ι] (r : ℕ) (hr : Fintype.card ι = r)
variable {S T : Type} [CommRing S] [CommRing T] (e : S ≃+* T)

theorem map_normal (α : Type) (i : α) : MvPolynomial.mapEquiv α e (MvPolynomial.X i) = MvPolynomial.X i :=
  MvPolynomial.map_X _ _

theorem coefficient_numbering :
    (MvPolynomial.mapEquiv ι e).trans
      (MvPolynomial.renameEquiv T (OrderedThomSections.numbering ι r hr).symm).toRingEquiv =
    (MvPolynomial.renameEquiv S (OrderedThomSections.numbering ι r hr).symm).toRingEquiv.trans
      (MvPolynomial.mapEquiv (Fin r) e) := by
  apply RingEquiv.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [MvPolynomial.mapEquiv_apply,MvPolynomial.renameEquiv_apply]
  · intro i
    simp [MvPolynomial.mapEquiv_apply,MvPolynomial.renameEquiv_apply]

universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ)

def baseIso (α : Type) : LocalizedThomSections.thom G S α ≅ LocalizedThomSections.thom G T α :=
  CoordinatePairEquiv.relativeIso MvPolynomial.X MvPolynomial.X
    (MvPolynomial.mapEquiv α e) (map_normal e α) G

theorem base_inv (α : Type) : (baseIso e G α).inv = LocalizedThomSections.thomMap G e.toRingHom :=
  CoordinatePairEquivMap.relative_inv _ _ _ _ G

theorem base_transport (α : Type) : (baseIso e G α).hom =
    (CoordinatePairTransport.relativeIso MvPolynomial.X MvPolynomial.X (Equiv.refl α)
      (MvPolynomial.mapEquiv α e) (map_normal e α) G).hom := by
  have ho : (CoordinatePairTransport.openIso MvPolynomial.X MvPolynomial.X (Equiv.refl α)
      (MvPolynomial.mapEquiv α e) (map_normal e α)).hom =
      (CoordinatePairEquiv.punctureIso MvPolynomial.X MvPolynomial.X
        (MvPolynomial.mapEquiv α e) (map_normal e α)).hom := by
    apply (cancel_mono (CoordinatePurityInput.puncture (MvPolynomial α T) α MvPolynomial.X).ι).mp
    rw [CoordinatePairTransport.open_square,← CoordinatePairEquiv.puncture_square]
  simp only [baseIso,CoordinatePairEquiv.relativeIso,ConeDerivedComparison.coneIso,asIso_hom,
    CoordinatePairTransport.relativeIso_hom,ho]


theorem thom_square : (baseIso e G ι).hom ≫ (OrderedThomSections.thomIso ι r hr T G).hom =
    (OrderedThomSections.thomIso ι r hr S G).hom ≫ (baseIso e G (Fin r)).hom := by
  simp only [base_transport,OrderedThomSections.thomIso]
  rw [CoordinatePairTransport.relative_comp,CoordinatePairTransport.relative_comp]
  have hi : (OrderedThomSections.numbering ι r hr).trans (Equiv.refl ι) =
      (Equiv.refl (Fin r)).trans (OrderedThomSections.numbering ι r hr) := rfl
  have he := coefficient_numbering ι r hr e
  congr 2

#print axioms map_normal
#print axioms coefficient_numbering
#print axioms baseIso
#print axioms base_inv
#print axioms base_transport
#print axioms thom_square
end Verification.OrderedThomBaseChange
