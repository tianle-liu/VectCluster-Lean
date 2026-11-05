/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AffineShiftedThomSections

/-!
# Affine Thom Evaluation Instances

Explicit instance transport for the finite normal frame used in affine
Thom evaluation. This eliminates duplicate finite-enumeration dictionaries.
-/
noncomputable section
namespace Verification.AffineThomEvaluationInstances
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
variable [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R S ι : Type) [CommRing R] [CommRing S] [Algebra R S] (r : ℕ)
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hs : Algebra.Smooth R S) (j : ℤ)
local notation "F" => AffineRelativeThom.theory R ι G
local notation "B" => op (CommRingCat.mkUnder (CommRingCat.of R) S)

def evaluateWith (fi : Fintype ι) (lo : LinearOrder ι) (hr : @Fintype.card ι fi=r) :
    (L.obj (DerivedCategory.Q.obj ((F).obj B)) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r : ℤ)) (M j)))) ≃+
    (N (j-r)).val.obj (op (Spec (CommRingCat.of S))) := by
  letI := fi
  letI := lo
  exact AffineShiftedThomSections.evaluate J L G R S ι r hr site M N V hs j

omit [J.Additive] [L.Additive] [HasShift D ℤ]
  [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.CommShift ℤ] [L.CommShift ℤ] in
theorem evaluate_instances (fi₁ fi₂ : Fintype ι) (lo₁ lo₂ : LinearOrder ι) (hlo : lo₁=lo₂)
    (hr₁ : @Fintype.card ι fi₁=r) (hr₂ : @Fintype.card ι fi₂=r) :
    evaluateWith J L G R S ι r site M N V hs j fi₁ lo₁ hr₁ =
    evaluateWith J L G R S ι r site M N V hs j fi₂ lo₂ hr₂ := by
  cases Subsingleton.elim fi₁ fi₂
  cases hlo
  rfl

def shiftedEvaluateWith (fi : Fintype ι) (lo : LinearOrder ι) (hr : @Fintype.card ι fi=r) :
    (L.obj (DerivedCategory.Q.obj (((F).obj B)⟦(1 : ℤ)⟧)) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-((r+1 : ℕ) : ℤ)) (M j)))) ≃+
    (N (j-r)).val.obj (op (Spec (CommRingCat.of S))) := by
  letI := fi
  letI := lo
  exact AffineShiftedThomSections.shiftedEvaluate J L G R S ι r hr site M N V hs j

omit [J.Additive] [L.Additive] in
theorem shifted_evaluate_instances (fi₁ fi₂ : Fintype ι) (lo₁ lo₂ : LinearOrder ι) (hlo : lo₁=lo₂)
    (hr₁ : @Fintype.card ι fi₁=r) (hr₂ : @Fintype.card ι fi₂=r) :
    shiftedEvaluateWith J L G R S ι r site M N V hs j fi₁ lo₁ hr₁ =
    shiftedEvaluateWith J L G R S ι r site M N V hs j fi₂ lo₂ hr₂ := by
  cases Subsingleton.elim fi₁ fi₂
  cases hlo
  rfl

#print axioms evaluateWith
#print axioms evaluate_instances
#print axioms shiftedEvaluateWith
#print axioms shifted_evaluate_instances
end Verification.AffineThomEvaluationInstances
