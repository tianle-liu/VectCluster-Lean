/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathGradedCoefficientAction
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Graded Coefficient Category

The additive category of finite free modules with the actual coefficient
weights. Its morphisms are literal homogeneous matrices over the proved
quotient ring. Positive Milnor--Witt realization uses K(j+1), leaving the
constant Z summand outside this coefficient action.
-/

noncomputable section
namespace Verification.GradedCoefficientCategory

open CategoryTheory CategoryTheory.Limits Verification.PathCoefficientRing

structure Space where
  index : Type
  finite : Fintype index
  decidable : DecidableEq index
  weight : index → ℕ

attribute [instance] Space.finite Space.decidable

def maps (X Y : Space) : AddSubgroup (Matrix Y.index X.index Coeff) where
  carrier := {M | PathGradedMatrices.Homogeneous (fun i=>(Y.weight i:ℤ)) (fun j=>(X.weight j:ℤ)) M}
  zero_mem' := PathGradedMatrices.zero _ _
  add_mem' := PathGradedMatrices.add _ _ _ _
  neg_mem' := PathGradedMatrices.neg _ _ _

instance category : Category Space where
  Hom X Y := maps X Y
  id X := ⟨1,PathGradedMatrices.one _⟩
  comp f g := ⟨g.val*f.val,PathGradedMatrices.mul _ _ _ _ _ g.property f.property⟩
  id_comp f := by apply Subtype.ext;exact Matrix.mul_one _
  comp_id f := by apply Subtype.ext;exact Matrix.one_mul _
  assoc f g h := by apply Subtype.ext;exact (Matrix.mul_assoc _ _ _).symm

instance preadditive : Preadditive Space where
  homGroup X Y := inferInstanceAs (AddCommGroup (maps X Y))
  add_comp _ _ _ f g h := by apply Subtype.ext;exact Matrix.mul_add _ _ _
  comp_add _ _ _ f g h := by apply Subtype.ext;exact Matrix.add_mul _ _ _

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (K : ℕ → C) (T : PathGradedCoefficientAction.Action K)

def realization : Space ⥤ C where
  obj X := ⨁ fun i=>K (X.weight i)
  map {X Y} f := PathGradedCoefficientAction.realize K T Y.weight X.weight f.val f.property
  map_id X := PathGradedCoefficientAction.realize_one K T X.weight
  map_comp {X Y Z} f g := PathGradedCoefficientAction.realize_mul K T Z.weight Y.weight X.weight
    g.val f.val g.property f.property

instance realization_additive : (realization K T).Additive where
  map_add := by
    intro X Y f g
    exact PathGradedCoefficientAction.realize_add K T Y.weight X.weight
      f.val g.val f.property g.property

/-- Index j realizes K_(j+1); no K_0 or Z action occurs in this functor. -/
def positiveRealization (T : PathGradedCoefficientAction.Action (fun j=>K (j+1))) : Space ⥤ C :=
  realization (fun j=>K (j+1)) T

instance positiveRealization_additive (T : PathGradedCoefficientAction.Action (fun j=>K (j+1))) :
    (positiveRealization K T).Additive := realization_additive _ _

#print axioms Space
#print axioms maps
#print axioms category
#print axioms preadditive
#print axioms realization
#print axioms realization_additive
#print axioms positiveRealization
#print axioms positiveRealization_additive

end Verification.GradedCoefficientCategory
