/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathMilnorWittGradedRealization
import Verification.PathGradedCoefficientAction
import Verification.GradedMilnorWittStrictScalars

/-!
# Path Strict Coefficient Action

The formal path action is constructed from ordinary graded MW scalar
morphisms. The Laurent coaction grading and the multiplication order are
checked internally. Every positive degree shift is allowed.
-/
noncomputable section
namespace Verification.PathStrictCoefficientAction
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.PathGradedCoefficientAction
open Verification.GradedMilnorWittDegreeSpaces
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
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (H : GradedMilnorWittStrictScalars.Standard J L G R site M N W P V)

def pieceMap (offset i j : ℕ) : piece ((j:ℤ)-i) →+
    space site N W (CommRingCat.of R) (((j+offset:ℕ):ℤ)-(i+offset:ℕ)) where
  toFun c := ⟨PathMilnorWittCoefficients.realize (W.symbols (CommRingCat.of R)).toCoefficients c.val,by
    change GradedMilnorWittHomogeneity.Homogeneous site N W (CommRingCat.of R)
      (((j+offset:ℕ):ℤ)-(i+offset:ℕ)) _
    have he : (((j+offset:ℕ):ℤ)-(i+offset:ℕ))=(j:ℤ)-i := by omega
    rw [he]
    exact PathMilnorWittGradedRealization.homogeneous P (CommRingCat.of R) c.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a.val b.val)

theorem pieceMap_one (offset i : ℕ) : pieceMap R site N W P offset i i (unit i)=
    GradedMilnorWittStrictScalars.one R site N W P ((i+offset:ℕ):ℤ) :=
  Subtype.ext (map_one _)

theorem pieceMap_product (offset i j k : ℕ)
    (b : piece ((k:ℤ)-j)) (a : piece ((j:ℤ)-i)) :
    pieceMap R site N W P offset i k (product b a)=
    GradedMilnorWittStrictScalars.product R site N W P ((i+offset:ℕ):ℤ) ((j+offset:ℕ):ℤ) ((k+offset:ℕ):ℤ)
      (pieceMap R site N W P offset i j a) (pieceMap R site N W P offset j k b) := by
  apply Subtype.ext
  change PathMilnorWittCoefficients.realize _ (b.val*a.val)=
    PathMilnorWittCoefficients.realize _ a.val*PathMilnorWittCoefficients.realize _ b.val
  rw [mul_comm b.val a.val,map_mul]

def action (offset : ℕ) : Action (fun i : ℕ=>M ((i+offset:ℕ):ℤ)) where
  act i j := (H.scalar ((i+offset:ℕ):ℤ) ((j+offset:ℕ):ℤ)).comp (pieceMap R site N W P offset i j)
  one i := by
    change H.scalar _ _ (pieceMap R site N W P offset i i (unit i))=𝟙 _
    rw [pieceMap_one,H.scalar_one]
  mul i j k b a := by
    change H.scalar _ _ (pieceMap R site N W P offset i k (product b a))=
      H.scalar _ _ (pieceMap R site N W P offset i j a) ≫
      H.scalar _ _ (pieceMap R site N W P offset j k b)
    rw [pieceMap_product,H.scalar_comp]

omit [J.Additive] [L.Additive] in
theorem action_apply (offset i j : ℕ) (c : piece ((j:ℤ)-i)) :
    (action J L G R site M N W P V H offset).act i j c=
      H.scalar ((i+offset:ℕ):ℤ) ((j+offset:ℕ):ℤ) (pieceMap R site N W P offset i j c) := rfl

#print axioms pieceMap
#print axioms pieceMap_one
#print axioms pieceMap_product
#print axioms action
#print axioms action_apply
end Verification.PathStrictCoefficientAction
