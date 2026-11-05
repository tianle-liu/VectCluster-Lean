/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ReindexedThomMap
import Verification.OrderedThomMapNaturality

/-!
# Ordered Reindexed Thom Naturality

Ordered Thom evaluation is natural under a coefficient map and an
increasing change of normal index set. The compatibility is proved on the
actual scheme and open maps, and then on their derived localization cones.
-/
noncomputable section
namespace Verification.OrderedReindexedThomNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.CoordinatePurityInput
variable (ι κ : Type) [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
variable (r : ℕ) (hi : Fintype.card ι=r) (hk : Fintype.card κ=r)
variable (e : κ ≃ ι)
variable (he : ∀ i,e (OrderedThomSections.numbering κ r hk i)=OrderedThomSections.numbering ι r hi i)
variable {S T : Type} [CommRing S] [CommRing T] (f : S →+* T)
local notation "ni" => OrderedThomSections.numbering ι r hi
local notation "nk" => OrderedThomSections.numbering κ r hk

include he in
theorem scheme_square : (OrderedThomMapNaturality.orderScheme κ r hk T).hom ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin r) f)) =
    Spec.map (CommRingCat.ofHom (ReindexedThomMap.polynomialMap e f)) ≫
      (OrderedThomMapNaturality.orderScheme ι r hi S).hom := by
  have he' (i : Fin r) : e.symm (ni i)=nk i := by rw [← he i,e.symm_apply_apply]
  have hh : (ReindexedThomMap.polynomialMap e f).comp
      ((MvPolynomial.renameEquiv S (ni).symm).symm.toRingHom) =
      ((MvPolynomial.renameEquiv T (nk).symm).symm.toRingHom).comp
        (MvPolynomial.map (σ := Fin r) f) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [MvPolynomial.renameEquiv_apply,ReindexedThomMap.polynomialMap]
    · intro i
      simp [MvPolynomial.renameEquiv_apply,ReindexedThomMap.polynomialMap,he']
  have hc := congrArg (fun g : MvPolynomial (Fin r) S →+* MvPolynomial κ T =>
    Spec.map (CommRingCat.ofHom g)) hh
  simpa only [OrderedThomMapNaturality.orderScheme,CoordinatePairEquiv.schemeIso,
    Functor.mapIso_hom,CommRingCat.ofHom_comp,Spec.map_comp] using hc.symm

include he in
theorem open_square : (OrderedThomMapNaturality.orderOpen κ r hk T).hom ≫
    CoordinatePairMap.punctureMap MvPolynomial.X MvPolynomial.X
      (MvPolynomial.map (σ := Fin r) f) (fun i => MvPolynomial.map_X _ i) =
    ReindexedThomMap.openMap e f ≫ (OrderedThomMapNaturality.orderOpen ι r hi S).hom := by
  apply (cancel_mono (puncture (MvPolynomial (Fin r) S) (Fin r) MvPolynomial.X).ι).mp
  simp only [Category.assoc,← CoordinatePairMap.puncture_square]
  simp only [OrderedThomMapNaturality.orderOpen,← Category.assoc,CoordinatePairTransport.open_square]
  have hs := scheme_square ι κ r hi hk e he f
  simp only [OrderedThomMapNaturality.orderScheme] at hs
  rw [Category.assoc,hs,← Category.assoc,ReindexedThomMap.open_square]

universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ)

include he in
theorem thom_square : (OrderedThomSections.thomIso κ r hk T G).hom ≫
    LocalizedThomSections.thomMap (ι := Fin r) G f =
    ReindexedThomMap.map e f G ≫ (OrderedThomSections.thomIso ι r hi S G).hom := by
  rw [ReindexedThomMap.cone_map]
  simp only [OrderedThomSections.thomIso,CoordinatePairTransport.relativeIso_hom,
    LocalizedThomSections.thomMap,CoordinatePairMap.relativeMap,
    TransverseDerivedBoundary.coneMap,TransverseConeBoundary.coneMap,
    ← Functor.map_comp,← mappingCone.map_comp]
  have ho := open_square ι κ r hi hk e he f
  have hs := scheme_square ι κ r hi hk e he f
  simp only [OrderedThomMapNaturality.orderOpen,OrderedThomMapNaturality.orderScheme] at ho hs
  simp only [ho,hs]

include he in
theorem inverse_square : (OrderedThomSections.thomIso κ r hk T G).inv ≫
    ReindexedThomMap.map e f G =
    LocalizedThomSections.thomMap (ι := Fin r) G f ≫ (OrderedThomSections.thomIso ι r hi S G).inv := by
  apply (cancel_epi (OrderedThomSections.thomIso κ r hk T G).hom).mp
  apply (cancel_mono (OrderedThomSections.thomIso ι r hi S G).hom).mp
  simp only [Category.assoc,Iso.hom_inv_id_assoc,Iso.inv_hom_id,Category.comp_id]
  exact (thom_square ι κ r hi hk e he f G).symm

variable (R : Type) [CommRing R] [Algebra R S] [Algebra R T]
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)

include he hV in
omit [J.Additive] [L.Additive] in
theorem evaluate_naturality (g : S →ₐ[R] T)
    (hs : Algebra.Smooth R S) (ht : Algebra.Smooth R T) (j : ℤ)
    (a : L.obj (LocalizedThomSections.thom G S ι) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r : ℤ)) (M j)))) :
    OrderedThomSections.evaluate κ r hk T J L G R site M N V ht j
      (L.map (ReindexedThomMap.map e g.toRingHom G) ≫ a) =
    (N (j-r)).val.map (Spec.map (CommRingCat.ofHom g.toRingHom)).op
      (OrderedThomSections.evaluate ι r hi S J L G R site M N V hs j a) := by
  rw [OrderedThomEvaluation.evaluate_apply,OrderedThomEvaluation.evaluate_apply]
  rw [← Category.assoc,← Functor.map_comp,inverse_square ι κ r hi hk e he,
    Functor.map_comp,Category.assoc]
  exact OrderedThomEvaluation.fin_naturality J L G R site M N V S r hV T hs ht g j _

#print axioms scheme_square
#print axioms open_square
#print axioms thom_square
#print axioms inverse_square
#print axioms evaluate_naturality
end Verification.OrderedReindexedThomNaturality
