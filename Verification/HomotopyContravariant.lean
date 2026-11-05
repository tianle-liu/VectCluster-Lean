/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.Opposite
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Homotopy Contravariant

Contravariant additive coefficient functors preserve genuine chain
homotopy equivalences. This uses no exactness or projective object claim.
-/

noncomputable section
namespace Verification.HomotopyContravariant

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

universe u v u' v'
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]
variable {ι : Type*} {c : ComplexShape ι} {X Y : HomologicalComplex C c}

/-- Reversal sends the actual components of a homotopy to their opposites. -/
def opposite {f g : X ⟶ Y} (h : Homotopy f g) :
    Homotopy ((opFunctor C c).map f.op) ((opFunctor C c).map g.op) where
  hom i j := (h.hom j i).op
  zero i j hij := by rw [h.zero j i hij,op_zero]
  comm i := by
    change (f.f i).op = (h.hom i (c.prev i) ≫ Y.d (c.prev i) i).op +
      (X.d i (c.next i) ≫ h.hom (c.next i) i).op + (g.f i).op
    rw [h.comm i]
    simp only [op_add]
    change (X.d i (c.next i) ≫ h.hom (c.next i) i).op +
      (h.hom i (c.prev i) ≫ Y.d (c.prev i) i).op + (g.f i).op = _
    rw [add_comm ((X.d i (c.next i) ≫ h.hom (c.next i) i).op)
      ((h.hom i (c.prev i) ≫ Y.d (c.prev i) i).op)]

/-- Opposite complexes retain the constructed inverse and both homotopies. -/
def oppositeEquivalence (e : HomotopyEquiv X Y) : HomotopyEquiv X.op Y.op where
  hom := (opFunctor C c).map e.inv.op
  inv := (opFunctor C c).map e.hom.op
  homotopyHomInvId := by
    simpa only [op_comp,Functor.map_comp,op_id,Functor.map_id] using opposite e.homotopyHomInvId
  homotopyInvHomId := by
    simpa only [op_comp,Functor.map_comp,op_id,Functor.map_id] using opposite e.homotopyInvHomId

/-- The literal contravariant coefficient complex. Its term at i is F(X_i). -/
def complex (F : Cᵒᵖ ⥤ D) [F.Additive] (X : HomologicalComplex C c) :
    HomologicalComplex D c.symm := (F.mapHomologicalComplex c.symm).obj X.op

def equivalence (F : Cᵒᵖ ⥤ D) [F.Additive] (e : HomotopyEquiv X Y) :
    HomotopyEquiv (complex F X) (complex F Y) :=
  F.mapHomotopyEquiv (oppositeEquivalence e)

/-- In particular, apply the genuine groups of maps into any coefficient object M. -/
def homComplex (M : C) (X : HomologicalComplex C c) : HomologicalComplex AddCommGrp.{v} c.symm :=
  complex (preadditiveYoneda.obj M) X

def homEquivalence (M : C) (e : HomotopyEquiv X Y) :
    HomotopyEquiv (homComplex M X) (homComplex M Y) := equivalence (preadditiveYoneda.obj M) e

#print axioms opposite
#print axioms oppositeEquivalence
#print axioms complex
#print axioms equivalence
#print axioms homComplex
#print axioms homEquivalence

end Verification.HomotopyContravariant
