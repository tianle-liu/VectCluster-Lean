/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OrderedThomSections

/-!
# Ordered Thom Evaluation

Explicit evaluation on a numbered frame, with the cardinal cast
retained consistently in ordinary base naturality.
-/
noncomputable section
namespace Verification.OrderedThomEvaluation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [CommRing R]
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (S : Type) [CommRing S] [Algebra R S] (r : ℕ)

def degreeEvaluation (ι : Type) [Fintype ι] (hr : Fintype.card ι = r)
    (hs : Algebra.Smooth R S) (j : ℤ) :
    (L.obj (LocalizedThomSections.thom G S ι) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r : ℤ)) (M j)))) ≃+
    (N (j-r)).val.obj (Opposite.op (Spec (CommRingCat.of S))) := by
  cases hr
  exact V.evaluate S ι hs j

def rewriteEvaluation (ι : Type) [Fintype ι] (hr : Fintype.card ι = r)
    (hs : Algebra.Smooth R S) (j : ℤ) :
    (L.obj (LocalizedThomSections.thom G S ι) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r : ℤ)) (M j)))) ≃+
    (N (j-r)).val.obj (Opposite.op (Spec (CommRingCat.of S))) := by
  have e := V.evaluate S ι hs j
  rw [hr] at e
  exact e

omit [J.Additive] [L.Additive] in
theorem rewrite_eq_degree (ι : Type) [Fintype ι] (hr : Fintype.card ι = r)
    (hs : Algebra.Smooth R S) (j : ℤ) :
    rewriteEvaluation J L G R site M N V S r ι hr hs j =
      degreeEvaluation J L G R site M N V S r ι hr hs j := by
  cases hr
  rfl

def finEvaluate (hs : Algebra.Smooth R S) (j : ℤ) :
    (L.obj (LocalizedThomSections.thom G S (Fin r)) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r : ℤ)) (M j)))) ≃+
    (N (j-r)).val.obj (Opposite.op (Spec (CommRingCat.of S))) := by
  exact rewriteEvaluation J L G R site M N V S r (Fin r) (Fintype.card_fin r) hs j

omit [J.Additive] [L.Additive] in
theorem evaluate_apply (ι : Type) [Fintype ι] [LinearOrder ι]
    (hr : Fintype.card ι = r) (hs : Algebra.Smooth R S) (j : ℤ)
    (a : L.obj (LocalizedThomSections.thom G S ι) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r : ℤ)) (M j)))) :
    OrderedThomSections.evaluate ι r hr S J L G R site M N V hs j a =
    finEvaluate J L G R site M N V S r hs j
      (L.map (OrderedThomSections.thomIso ι r hr S G).inv ≫ a) := rfl

variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (S' : Type) [CommRing S'] [Algebra R S']

include hV in
omit [J.Additive] [L.Additive] in
theorem degree_naturality (ι : Type) [Fintype ι] (hr : Fintype.card ι = r)
    (hs : Algebra.Smooth R S) (hs' : Algebra.Smooth R S')
    (f : S →ₐ[R] S') (j : ℤ)
    (a : L.obj (LocalizedThomSections.thom G S ι) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r : ℤ)) (M j)))) :
    degreeEvaluation J L G R site M N V S' r ι hr hs' j
      (L.map (LocalizedThomSections.thomMap G f.toRingHom) ≫ a) =
    (N (j-r)).val.map (Spec.map (CommRingCat.ofHom f.toRingHom)).op
      (degreeEvaluation J L G R site M N V S r ι hr hs j a) := by
  cases hr
  exact hV.base_change S S' ι hs hs' f j a

include hV in
omit [J.Additive] [L.Additive] in
theorem fin_naturality (hs : Algebra.Smooth R S) (hs' : Algebra.Smooth R S')
    (f : S →ₐ[R] S') (j : ℤ)
    (a : L.obj (LocalizedThomSections.thom G S (Fin r)) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r : ℤ)) (M j)))) :
    finEvaluate J L G R site M N V S' r hs' j
      (L.map (LocalizedThomSections.thomMap G f.toRingHom) ≫ a) =
    (N (j-r)).val.map (Spec.map (CommRingCat.ofHom f.toRingHom)).op
      (finEvaluate J L G R site M N V S r hs j a) := by
  simp only [finEvaluate,rewrite_eq_degree]
  exact degree_naturality J L G R site M N V S r hV S' (Fin r) (Fintype.card_fin r) hs hs' f j a

#print axioms degreeEvaluation
#print axioms rewriteEvaluation
#print axioms rewrite_eq_degree
#print axioms finEvaluate
#print axioms evaluate_apply
#print axioms degree_naturality
#print axioms fin_naturality
end Verification.OrderedThomEvaluation
