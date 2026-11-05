/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OrderedThomNaturality
import Verification.StrictLocalizedCoordinateTransport

/-!
# Ordered Explicit Coordinate Evaluation

An explicitly changed smooth base, followed by increasing normal
numbering, evaluates to ordinary pullback of the original section.
-/
noncomputable section
namespace Verification.OrderedExplicitCoordinateEvaluation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable (ι : Type) [Fintype ι] [LinearOrder ι] (r : ℕ) (hr : Fintype.card ι=r)
variable {S S' : Type} [CommRing S] [CommRing S']
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [CommRing R] [Algebra R S] [Algebra R S']
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)

include hV in
omit [J.Additive] [L.Additive] in
theorem evaluate (e : S ≃ₐ[R] S')
    (hs : Algebra.Smooth R S) (hs' : Algebra.Smooth R S') (j : ℤ)
    (a : L.obj (LocalizedThomSections.thom G S' (Fin r)) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r : ℤ)) (M j)))) :
    (N (j-r)).val.map (Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom)).op
      (OrderedThomSections.evaluate ι r hr S J L G R site M N V hs j
        (L.map ((OrderedThomBaseChange.baseIso e.toRingEquiv G ι).hom ≫
          (OrderedThomSections.thomIso ι r hr S' G).hom) ≫ a))=
      OrderedThomEvaluation.finEvaluate J L G R site M N V S' r hs' j a := by
  have h := OrderedThomNaturality.evaluate_naturality ι r hr J L G R site M N V hV e hs hs' j
    (L.map ((OrderedThomBaseChange.baseIso e.toRingEquiv G ι).hom ≫
      (OrderedThomSections.thomIso ι r hr S' G).hom) ≫ a)
  rw [← OrderedThomBaseChange.base_inv] at h
  simp only [CategoryTheory.Functor.map_comp,Category.assoc] at h
  rw [← CategoryTheory.Functor.map_comp_assoc,Iso.inv_hom_id,CategoryTheory.Functor.map_id,Category.id_comp] at h
  rw [OrderedThomEvaluation.evaluate_apply] at h
  rw [← CategoryTheory.Functor.map_comp_assoc,Iso.inv_hom_id,CategoryTheory.Functor.map_id,Category.id_comp] at h
  simpa only [CategoryTheory.Functor.map_comp,Category.assoc] using h.symm

#print axioms evaluate
end Verification.OrderedExplicitCoordinateEvaluation
