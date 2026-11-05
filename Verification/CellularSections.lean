/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Cellular Sections

The actual coefficient cochains Hom(C_*, M), for any preadditive
coefficient category. Naturality in M and determination of a differential
by all coefficient sections are proved directly.
-/
namespace Verification.CellularSections
open CategoryTheory CategoryTheory.Limits
variable {C : Type*} [Category C] [Preadditive C]
variable (K : ChainComplex C ℕ) (M : C)

def term (p : ℕ) : AddCommGrp := AddCommGrp.of (K.X p ⟶ M)

def differential (p : ℕ) : term K M p ⟶ term K M (p+1) := AddCommGrp.ofHom {
  toFun := fun a => K.d (p+1) p ≫ a
  map_zero' := by simp
  map_add' := by intro a b; simp only [Preadditive.comp_add] }

theorem differential_squared (p : ℕ) : differential K M p ≫ differential K M (p+1) = 0 := by
  ext a
  change K.d ((p+1)+1) (p+1) ≫ (K.d (p+1) p ≫ a) = 0
  rw [← Category.assoc,K.d_comp_d,zero_comp]

def complex : CochainComplex AddCommGrp ℕ :=
  CochainComplex.of (term K M) (differential K M) (differential_squared K M)

theorem complex_d (p : ℕ) (a : K.X p ⟶ M) :
    ((complex K M).d p (p+1)).hom a = K.d (p+1) p ≫ a := by
  exact congrArg (fun f : term K M p ⟶ term K M (p+1) => f.hom a)
    (CochainComplex.of_d (term K M) (differential K M) (differential_squared K M) p)

def coefficientMap {N : C} (f : M ⟶ N) : complex K M ⟶ complex K N :=
  CochainComplex.ofHom _ _ _ _ _ _ (fun _ => AddCommGrp.ofHom {
    toFun := fun a => a ≫ f
    map_zero' := by simp
    map_add' := by intro a b; simp only [Preadditive.add_comp] }) (by
      intro p
      ext a
      exact (Category.assoc (K.d (p+1) p) a f).symm)

theorem coefficientMap_id : coefficientMap K M (𝟙 M) = 𝟙 (complex K M) := by
  ext p a
  exact Category.comp_id a

theorem coefficientMap_comp {N P : C} (f : M ⟶ N) (g : N ⟶ P) :
    coefficientMap K M (f ≫ g) = coefficientMap K M f ≫ coefficientMap K N g := by
  ext p a
  exact (Category.assoc a f g).symm

omit [Preadditive C] in
theorem coefficients_determine {A B : C} (f g : A ⟶ B)
    (h : ∀ (N : C) (a : B ⟶ N), f ≫ a = g ≫ a) : f = g := by
  simpa only [Category.comp_id] using h B (𝟙 B)

#print axioms term
#print axioms differential
#print axioms differential_squared
#print axioms complex
#print axioms complex_d
#print axioms coefficientMap
#print axioms coefficientMap_id
#print axioms coefficientMap_comp
#print axioms coefficients_determine
end Verification.CellularSections
