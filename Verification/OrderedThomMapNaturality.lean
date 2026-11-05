/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OrderedThomEvaluation

/-!
# Ordered Thom Map Naturality

Increasing normal numbering commutes with every coefficient algebra
map, including the Laurent base point and closed-fiber restriction.
-/
noncomputable section
namespace Verification.OrderedThomMapNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.CoordinatePurityInput
variable (ι : Type) [Fintype ι] [LinearOrder ι] (r : ℕ) (hr : Fintype.card ι = r)
variable {S T : Type} [CommRing S] [CommRing T] (f : S →+* T)
local notation "num" => OrderedThomSections.numbering ι r hr

def orderOpen (A : Type) [CommRing A] := CoordinatePairTransport.openIso
  (MvPolynomial.X : ι → MvPolynomial ι A) MvPolynomial.X num
  (MvPolynomial.renameEquiv A (num).symm).toRingEquiv
  (OrderedThomSections.rename_normal ι r hr A)

def orderScheme (A : Type) [CommRing A] := CoordinatePairEquiv.schemeIso
  (MvPolynomial.renameEquiv A (num).symm).toRingEquiv

theorem scheme_square : (orderScheme ι r hr T).hom ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin r) f)) =
    Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := ι) f)) ≫ (orderScheme ι r hr S).hom := by
  have hh : (MvPolynomial.map (σ := ι) f).comp
      ((MvPolynomial.renameEquiv S (num).symm).symm.toRingHom) =
      ((MvPolynomial.renameEquiv T (num).symm).symm.toRingHom).comp
        (MvPolynomial.map (σ := Fin r) f) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [MvPolynomial.renameEquiv_apply]
    · intro i
      simp [MvPolynomial.renameEquiv_apply]
  have hc := congrArg (fun g : MvPolynomial (Fin r) S →+* MvPolynomial ι T =>
    Spec.map (CommRingCat.ofHom g)) hh
  simpa only [orderScheme,CoordinatePairEquiv.schemeIso,Functor.mapIso_hom,
    CommRingCat.ofHom_comp,Spec.map_comp] using hc.symm

theorem open_square : (orderOpen ι r hr T).hom ≫
    CoordinatePairMap.punctureMap MvPolynomial.X MvPolynomial.X
      (MvPolynomial.map (σ := Fin r) f) (fun i => MvPolynomial.map_X _ i) =
    CoordinatePairMap.punctureMap MvPolynomial.X MvPolynomial.X
      (MvPolynomial.map (σ := ι) f) (fun i => MvPolynomial.map_X _ i) ≫ (orderOpen ι r hr S).hom := by
  apply (cancel_mono (puncture (MvPolynomial (Fin r) S) (Fin r) MvPolynomial.X).ι).mp
  simp only [Category.assoc,← CoordinatePairMap.puncture_square]
  simp only [orderOpen,← Category.assoc,CoordinatePairTransport.open_square]
  have hs := scheme_square ι r hr f
  simp only [orderScheme] at hs
  rw [Category.assoc,hs,← Category.assoc,CoordinatePairMap.puncture_square]

universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ)

theorem thom_square : (OrderedThomSections.thomIso ι r hr T G).hom ≫
    LocalizedThomSections.thomMap (ι := Fin r) G f =
    LocalizedThomSections.thomMap (ι := ι) G f ≫ (OrderedThomSections.thomIso ι r hr S G).hom := by
  simp only [OrderedThomSections.thomIso,CoordinatePairTransport.relativeIso_hom,
    LocalizedThomSections.thomMap,CoordinatePairMap.relativeMap,
    TransverseDerivedBoundary.coneMap,TransverseConeBoundary.coneMap,
    ← Functor.map_comp,← mappingCone.map_comp]
  have ho := open_square ι r hr f
  have hs := scheme_square ι r hr f
  simp only [orderOpen,orderScheme] at ho hs
  simp only [ho,hs]


theorem inverse_square : (OrderedThomSections.thomIso ι r hr T G).inv ≫
    LocalizedThomSections.thomMap (ι := ι) G f =
    LocalizedThomSections.thomMap (ι := Fin r) G f ≫ (OrderedThomSections.thomIso ι r hr S G).inv := by
  apply (cancel_epi (OrderedThomSections.thomIso ι r hr T G).hom).mp
  apply (cancel_mono (OrderedThomSections.thomIso ι r hr S G).hom).mp
  simp only [Category.assoc,Iso.hom_inv_id_assoc,Iso.inv_hom_id,Category.comp_id]
  exact (thom_square ι r hr f G).symm

variable (R : Type) [CommRing R] [Algebra R S] [Algebra R T]
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)

include hV in
omit [J.Additive] [L.Additive] in
theorem evaluate_naturality (g : S →ₐ[R] T)
    (hs : Algebra.Smooth R S) (ht : Algebra.Smooth R T) (j : ℤ)
    (a : L.obj (LocalizedThomSections.thom G S ι) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r : ℤ)) (M j)))) :
    OrderedThomSections.evaluate ι r hr T J L G R site M N V ht j
      (L.map (LocalizedThomSections.thomMap G g.toRingHom) ≫ a) =
    (N (j-r)).val.map (Spec.map (CommRingCat.ofHom g.toRingHom)).op
      (OrderedThomSections.evaluate ι r hr S J L G R site M N V hs j a) := by
  rw [OrderedThomEvaluation.evaluate_apply,OrderedThomEvaluation.evaluate_apply]
  rw [← Category.assoc,← Functor.map_comp,inverse_square,Functor.map_comp,Category.assoc]
  exact OrderedThomEvaluation.fin_naturality J L G R site M N V S r hV T hs ht g j _

#print axioms orderOpen
#print axioms orderScheme
#print axioms scheme_square
#print axioms open_square
#print axioms thom_square
#print axioms inverse_square
#print axioms evaluate_naturality
end Verification.OrderedThomMapNaturality
