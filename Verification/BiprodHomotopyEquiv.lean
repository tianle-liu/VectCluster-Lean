/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.Homotopy

/-!
# Biprod Homotopy Equiv

Adjoin an unchanged complex to a homotopy equivalence. This will adjoin
Z[0] to the positive-weight MW path contraction, without a coefficient action
on Z and without any projectivity assumption.
-/

noncomputable section
namespace Verification.BiprodHomotopyEquiv

open CategoryTheory CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {ι : Type} {c : ComplexShape ι}

instance complexBinaryBiproducts : HasBinaryBiproducts (HomologicalComplex C c) where
  has_binary_biproduct _ _ := inferInstance

variable (S : HomologicalComplex C c) {A B : HomologicalComplex C c}

def liftHomotopy {f g : A ⟶ B} (h : Homotopy f g) :
    Homotopy (biprod.map (𝟙 S) f) (biprod.map (𝟙 S) g) := by
  let α : S ⊞ A ⟶ S ⊞ B := (biprod.fst : S ⊞ A ⟶ S) ≫ (biprod.inl : S ⟶ S ⊞ B)
  let β := (h.compLeft (biprod.snd : S ⊞ A ⟶ A)).compRight (biprod.inr : B ⟶ S ⊞ B)
  simpa only [biprod.map_eq,Category.id_comp,Category.assoc,α] using (Homotopy.refl α).add β

def equivalence (e : HomotopyEquiv A B) : HomotopyEquiv (S ⊞ A) (S ⊞ B) where
  hom := biprod.map (𝟙 S) e.hom
  inv := biprod.map (𝟙 S) e.inv
  homotopyHomInvId := by
    have ha : biprod.map (𝟙 S) e.hom ≫ biprod.map (𝟙 S) e.inv=
        biprod.map (𝟙 S) (e.hom≫e.inv) := by
      apply biprod.hom_ext <;> simp [Category.assoc]
    have hb : biprod.map (𝟙 S) (𝟙 A)=𝟙 (S ⊞ A) := by
      apply biprod.hom_ext <;> simp
    exact (Homotopy.ofEq ha).trans ((liftHomotopy S e.homotopyHomInvId).trans (Homotopy.ofEq hb))
  homotopyInvHomId := by
    have ha : biprod.map (𝟙 S) e.inv ≫ biprod.map (𝟙 S) e.hom=
        biprod.map (𝟙 S) (e.inv≫e.hom) := by
      apply biprod.hom_ext <;> simp [Category.assoc]
    have hb : biprod.map (𝟙 S) (𝟙 B)=𝟙 (S ⊞ B) := by
      apply biprod.hom_ext <;> simp
    exact (Homotopy.ofEq ha).trans ((liftHomotopy S e.homotopyInvHomId).trans (Homotopy.ofEq hb))

#print axioms complexBinaryBiproducts
#print axioms liftHomotopy
#print axioms equivalence

end Verification.BiprodHomotopyEquiv
