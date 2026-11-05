/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedMilnorWittDegreeSpaces
import Verification.LocalizedThomSections

/-!
# Graded Milnor Witt Strict Scalars

Ordinary graded Milnor-Witt multiplication as morphisms of strict
sheaves. The normalization is uniform over every smooth affine base and
finite normal Thom frame. It contains no exchange data, stratification,
family-specific basis or differential.
-/
noncomputable section
namespace Verification.GradedMilnorWittStrictScalars
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.GradedMilnorWittDegreeSpaces Verification.GradedSectionTotal
open Verification.SheafGradedLaurentResidue
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
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (P : GradedMilnorWittHomogeneity.Standard site N W)
local notation "B" => CommRingCat.of R

def one (k : ℤ) : space site N W B (k-k) :=
  ⟨1,by simpa using (show GradedMilnorWittHomogeneity.Homogeneous site N W B 0 1 from
    ⟨P.oneSection B,P.one_value B⟩)⟩

def product (k l m : ℤ) (a : space site N W B (l-k)) (b : space site N W B (m-l)) :
    space site N W B (m-k) :=
  ⟨a.val*b.val,by
    have h := GradedMilnorWittHomogeneity.mul P a.property b.property
    have he : (l-k)+(m-l)=m-k := by omega
    rw [he] at h
    exact h⟩

variable (V : LocalizedThomSections.Standard J L G R site M N)

structure Standard where
  scalar : ∀ k l : ℤ,space site N W B (l-k) →+ (M k ⟶ M l)
  scalar_one : ∀ k,scalar k k (one R site N W P k)=𝟙 (M k)
  scalar_comp : ∀ k l m (a : space site N W B (l-k)) (b : space site N W B (m-l)),
    scalar k l a ≫ scalar l m b=scalar k m (product R site N W P k l m a b)
  evaluate : ∀ (S ι : Type) [CommRing S] [Algebra R S] [Fintype ι]
    (hs : Algebra.Smooth R S) (k l : ℤ) (c : space site N W B (l-k))
    (a : L.obj (LocalizedThomSections.thom G S ι) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(Fintype.card ι : ℤ)) (M k)))),
    includeDegree (W.grading (CommRingCat.of S)) (l-Fintype.card ι)
      (V.evaluate S ι hs l (a ≫ J.map (DerivedCategory.Q.map
        ((CochainComplex.singleFunctor A (-(Fintype.card ι : ℤ))).map (scalar k l c)))))=
    includeDegree (W.grading (CommRingCat.of S)) (k-Fintype.card ι) (V.evaluate S ι hs k a)*
      GradedMilnorWittSheaf.pullback site N W (S := B) (T := CommRingCat.of S) (algebraMap R S) c.val

#print axioms one
#print axioms product
#print axioms Standard
end Verification.GradedMilnorWittStrictScalars
