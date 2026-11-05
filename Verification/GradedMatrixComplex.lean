/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedCoefficientCategory
import Mathlib.Algebra.Homology.Homotopy

/-!
# Graded Matrix Complex

Actual cellular-degree complexes in the homogeneous coefficient category.
Degree cutouts use the literal finite subsets of matrix indices.
-/

noncomputable section
namespace Verification.GradedMatrixComplex

open Classical CategoryTheory Verification.PathCoefficientRing
  Verification.GradedCoefficientCategory

variable {X Y Z : Space}

def Supported (dx : X.index → ℤ) (dy : Y.index → ℤ) (k : ℤ) (f : X ⟶ Y) : Prop :=
  ∀j i,dy j≠dx i+k → f.val j i=0

def degreeSpace (X : Space) (d : X.index → ℤ) (p : ℤ) : Space where
  index := {i // d i=p}
  finite := inferInstance
  decidable := inferInstance
  weight := fun i=>X.weight i.val

def cut (dx : X.index → ℤ) (dy : Y.index → ℤ) (p q : ℤ) (f : X ⟶ Y) :
    degreeSpace X dx p ⟶ degreeSpace Y dy q :=
  ⟨fun j i=>f.val j.val i.val,fun j i=>f.property j.val i.val⟩

theorem sum_supported {ι : Type} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (f : ι → Coeff) (hf : ∀i,¬p i → f i=0) : (∑i : {i // p i},f i.val)=∑i,f i := by
  rw [←Finset.sum_subtype (Finset.univ.filter p) (by simp) f]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi
  exact hf i (by simpa using hi)

theorem cut_comp (dx : X.index → ℤ) (dy : Y.index → ℤ) (dz : Z.index → ℤ)
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : ℤ) (hf : Supported dx dy k f)
    (p q r : ℤ) (hq : q=p+k) :
    cut dx dy p q f ≫ cut dy dz q r g=cut dx dz p r (f ≫ g) := by
  apply Subtype.ext
  funext j i
  change (∑l : {l // dy l=q},g.val j.val l.val*f.val l.val i.val)=∑l,g.val j.val l*f.val l i.val
  apply sum_supported (fun l=>dy l=q) (fun l=>g.val j.val l*f.val l i.val)
  intro l hl
  rw [hf l i.val (by have hi:=i.property;omega),mul_zero]

theorem cut_zero (dx : X.index → ℤ) (dy : Y.index → ℤ) (p q : ℤ) :
    cut dx dy p q (0 : X ⟶ Y)=0 := rfl

theorem cut_add (dx : X.index → ℤ) (dy : Y.index → ℤ) (p q : ℤ) (f g : X ⟶ Y) :
    cut dx dy p q (f+g)=cut dx dy p q f+cut dx dy p q g := rfl

theorem cut_id (dx : X.index → ℤ) (p : ℤ) : cut dx dx p p (𝟙 X)=𝟙 (degreeSpace X dx p) := by
  apply Subtype.ext
  funext i j
  change (1 : Matrix X.index X.index Coeff) i.val j.val=(1 : Matrix _ _ Coeff) i j
  by_cases he : i=j
  · subst j;simp
  · have hv : i.val≠j.val := fun h=>he (Subtype.ext h)
    simp [Matrix.one_apply,he,hv]

variable (X : Space) (d : X.index → ℤ) (D : X ⟶ X)
  (hd : Supported d d 1 D) (hsq : D≫D=0)

def complex : CochainComplex Space ℤ :=
  CochainComplex.of (degreeSpace X d) (fun p=>cut d d p (p+1) D) (by
    intro p
    rw [cut_comp d d d D D 1 hd p (p+1) (p+1+1) rfl,hsq,cut_zero])

theorem complex_d (p : ℤ) : (complex X d D hd hsq).d p (p+1)=cut d d p (p+1) D :=
  CochainComplex.of_d _ _ _ p

variable {X} {d D hd hsq}

def map {dy : Y.index → ℤ} {E : Y ⟶ Y} {he : Supported dy dy 1 E} {hsqe : E≫E=0}
    (f : X ⟶ Y) (hf : Supported d dy 0 f) (hc : f≫E=D≫f) :
    complex X d D hd hsq ⟶ complex Y dy E he hsqe :=
  CochainComplex.ofHom _ _ _ _ _ _ (fun p=>cut d dy p p f) (by
    intro p
    rw [cut_comp d dy dy f E 0 hf p p (p+1) (by omega),
      cut_comp d d dy D f 1 hd p (p+1) (p+1) rfl,hc])

theorem supported_zero (dx : X.index → ℤ) (dy : Y.index → ℤ) (k : ℤ) :
    Supported dx dy k (0 : X ⟶ Y) := by intro j i _;rfl

theorem complex_d_between (X : Space) (d : X.index → ℤ) (D : X ⟶ X)
    (hd : Supported d d 1 D) (hsq : D≫D=0) (p q : ℤ) (h : p+1=q) :
    (complex X d D hd hsq).d p q=cut d d p q D := by
  subst q
  exact complex_d X d D hd hsq p

#print axioms Supported
#print axioms degreeSpace
#print axioms cut
#print axioms sum_supported
#print axioms cut_comp
#print axioms cut_zero
#print axioms cut_add
#print axioms cut_id
#print axioms complex
#print axioms complex_d
#print axioms map
#print axioms supported_zero
#print axioms complex_d_between

end Verification.GradedMatrixComplex
