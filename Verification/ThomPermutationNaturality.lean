/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OrderedThomEvaluation
import Verification.ThomPermutationInput

/-!
# Thom Permutation Naturality

Coordinate permutations commute with every coefficient algebra map.
The ordinary permutation degree law then forces the orientation action
to commute with base change; no extra orientation naturality is assumed.
-/
noncomputable section
namespace Verification.ThomPermutationNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.CoordinatePurityInput
variable (ι : Type) (e : Equiv.Perm ι)
variable {S T : Type} [CommRing S] [CommRing T] (f : S →+* T)
local notation "num" => e

def orderOpen (A : Type) [CommRing A] := CoordinatePairTransport.openIso
  (MvPolynomial.X : ι → MvPolynomial ι A) MvPolynomial.X num
  (MvPolynomial.renameEquiv A (num).symm).toRingEquiv
  (fun i => by simp [MvPolynomial.renameEquiv_apply])

def orderScheme (A : Type) [CommRing A] := CoordinatePairEquiv.schemeIso
  (MvPolynomial.renameEquiv A (num).symm).toRingEquiv

theorem scheme_square : (orderScheme ι e T).hom ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := ι) f)) =
    Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := ι) f)) ≫ (orderScheme ι e S).hom := by
  have hh : (MvPolynomial.map (σ := ι) f).comp
      ((MvPolynomial.renameEquiv S (num).symm).symm.toRingHom) =
      ((MvPolynomial.renameEquiv T (num).symm).symm.toRingHom).comp
        (MvPolynomial.map (σ := ι) f) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [MvPolynomial.renameEquiv_apply]
    · intro i
      simp [MvPolynomial.renameEquiv_apply]
  have hc := congrArg (fun g : MvPolynomial (ι) S →+* MvPolynomial ι T =>
    Spec.map (CommRingCat.ofHom g)) hh
  simpa only [orderScheme,CoordinatePairEquiv.schemeIso,Functor.mapIso_hom,
    CommRingCat.ofHom_comp,Spec.map_comp] using hc.symm

theorem open_square : (orderOpen ι e T).hom ≫
    CoordinatePairMap.punctureMap MvPolynomial.X MvPolynomial.X
      (MvPolynomial.map (σ := ι) f) (fun i => MvPolynomial.map_X _ i) =
    CoordinatePairMap.punctureMap MvPolynomial.X MvPolynomial.X
      (MvPolynomial.map (σ := ι) f) (fun i => MvPolynomial.map_X _ i) ≫ (orderOpen ι e S).hom := by
  apply (cancel_mono (puncture (MvPolynomial (ι) S) (ι) MvPolynomial.X).ι).mp
  simp only [Category.assoc,← CoordinatePairMap.puncture_square]
  simp only [orderOpen,← Category.assoc,CoordinatePairTransport.open_square]
  have hs := scheme_square ι e f
  simp only [orderScheme] at hs
  rw [Category.assoc,hs,← Category.assoc,CoordinatePairMap.puncture_square]

universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ)

theorem thom_square : (ThomPermutationInput.permutationIso G T ι e).hom ≫
    LocalizedThomSections.thomMap (ι := ι) G f =
    LocalizedThomSections.thomMap (ι := ι) G f ≫ (ThomPermutationInput.permutationIso G S ι e).hom := by
  change (CoordinatePairTransport.relativeIso MvPolynomial.X MvPolynomial.X e
    (MvPolynomial.renameEquiv T e.symm).toRingEquiv _ G).hom ≫ _ =
      _ ≫ (CoordinatePairTransport.relativeIso MvPolynomial.X MvPolynomial.X e
        (MvPolynomial.renameEquiv S e.symm).toRingEquiv _ G).hom
  simp only [CoordinatePairTransport.relativeIso_hom,
    LocalizedThomSections.thomMap,CoordinatePairMap.relativeMap,
    TransverseDerivedBoundary.coneMap,TransverseConeBoundary.coneMap,
    ← Functor.map_comp,← mappingCone.map_comp]
  have ho := open_square ι e f
  have hs := scheme_square ι e f
  simp only [orderOpen,orderScheme] at ho hs
  simp only [ho,hs]

variable (R : Type) [CommRing R] [Algebra R S] [Algebra R T]
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)

variable [Fintype ι] [DecidableEq ι]
variable (O : ThomPermutationInput.Standard J L G R site M N V)

include hV in
omit [J.Additive] [L.Additive] in
theorem evaluation_base_change (g : S →ₐ[R] T)
    (hs : Algebra.Smooth R S) (ht : Algebra.Smooth R T) (j : ℤ)
    (a : L.obj (LocalizedThomSections.thom G S ι) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(Fintype.card ι : ℤ)) (M j)))) :
    (N (j-Fintype.card ι)).val.map (Spec.map (CommRingCat.ofHom g.toRingHom)).op
      (O.orientation S (j-Fintype.card ι) (Equiv.Perm.sign e) (V.evaluate S ι hs j a)) =
    O.orientation T (j-Fintype.card ι) (Equiv.Perm.sign e)
      ((N (j-Fintype.card ι)).val.map (Spec.map (CommRingCat.ofHom g.toRingHom)).op
        (V.evaluate S ι hs j a)) := by
  rw [← O.permutation,← hV.base_change,← hV.base_change,← O.permutation T ι ht e j]
  congr 1
  rw [← Category.assoc,← Functor.map_comp,← thom_square,Functor.map_comp,Category.assoc]

include hV in
omit [J.Additive] [L.Additive] in
theorem orientation_sign_naturality (g : S →ₐ[R] T)
    (hs : Algebra.Smooth R S) (ht : Algebra.Smooth R T) (j : ℤ)
    (a : (N (j-Fintype.card ι)).val.obj (Opposite.op (Spec (CommRingCat.of S)))) :
    (N (j-Fintype.card ι)).val.map (Spec.map (CommRingCat.ofHom g.toRingHom)).op
      (O.orientation S (j-Fintype.card ι) (Equiv.Perm.sign e) a) =
    O.orientation T (j-Fintype.card ι) (Equiv.Perm.sign e)
      ((N (j-Fintype.card ι)).val.map (Spec.map (CommRingCat.ofHom g.toRingHom)).op a) := by
  obtain ⟨b,rfl⟩ := (V.evaluate S ι hs j).surjective a
  exact evaluation_base_change ι e J L G R site M N V hV O g hs ht j b

#print axioms orderOpen
#print axioms orderScheme
#print axioms scheme_square
#print axioms open_square
#print axioms thom_square
#print axioms evaluation_base_change
#print axioms orientation_sign_naturality
end Verification.ThomPermutationNaturality
