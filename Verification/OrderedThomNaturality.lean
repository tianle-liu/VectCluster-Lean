/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OrderedThomBaseChange
import Verification.OrderedThomEvaluation

/-!
# Ordered Thom Naturality

Ordered evaluation intertwines genuine coefficient-ring isomorphisms
with ordinary pullback on the coefficient sheaf.
-/
noncomputable section
namespace Verification.OrderedThomNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable (ι : Type) [Fintype ι] [LinearOrder ι] (r : ℕ) (hr : Fintype.card ι = r)
variable {S S' : Type} [CommRing S] [CommRing S'] (e : S ≃+* S')
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ)

theorem inverse_square :
    (OrderedThomSections.thomIso ι r hr S' G).inv ≫ (OrderedThomBaseChange.baseIso e G ι).inv =
    (OrderedThomBaseChange.baseIso e G (Fin r)).inv ≫ (OrderedThomSections.thomIso ι r hr S G).inv := by
  apply (cancel_epi (OrderedThomSections.thomIso ι r hr S' G).hom).mp
  apply (cancel_epi (OrderedThomBaseChange.baseIso e G ι).hom).mp
  simp only [Iso.hom_inv_id_assoc,Iso.hom_inv_id]
  rw [← Category.assoc,OrderedThomBaseChange.thom_square]
  simp only [Category.assoc,Iso.hom_inv_id_assoc,Iso.hom_inv_id]

variable (R : Type) [CommRing R] [Algebra R S] [Algebra R S']
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)

include hV in
omit [J.Additive] [L.Additive] in
theorem evaluate_naturality (f : S ≃ₐ[R] S')
    (hs : Algebra.Smooth R S) (hs' : Algebra.Smooth R S') (j : ℤ)
    (a : L.obj (LocalizedThomSections.thom G S ι) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r : ℤ)) (M j)))) :
    OrderedThomSections.evaluate ι r hr S' J L G R site M N V hs' j
      (L.map (LocalizedThomSections.thomMap G f.toRingEquiv.toRingHom) ≫ a) =
    (N (j-r)).val.map (Spec.map (CommRingCat.ofHom f.toRingEquiv.toRingHom)).op
      (OrderedThomSections.evaluate ι r hr S J L G R site M N V hs j a) := by
  rw [OrderedThomEvaluation.evaluate_apply,OrderedThomEvaluation.evaluate_apply]
  rw [← OrderedThomBaseChange.base_inv f.toRingEquiv G ι]
  rw [← Category.assoc,← Functor.map_comp,inverse_square,Functor.map_comp,Category.assoc,
    OrderedThomBaseChange.base_inv]
  exact OrderedThomEvaluation.fin_naturality J L G R site M N V S r hV S' hs hs' f.toAlgHom j _

#print axioms inverse_square
#print axioms evaluate_naturality
end Verification.OrderedThomNaturality
