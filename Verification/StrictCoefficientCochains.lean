/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ProjectiveConeTerms
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Strict Coefficient Cochains

The literal coefficient complex of a nonpositive strict projective
model: degree q is Hom(P^(-q),M), with differential precomposition by
the actual differential of P. Its cohomological bound follows from
vanishing of P's actual terms, without any ambient concentration claim.
-/
noncomputable section
namespace Verification.StrictCoefficientCochains
open CategoryTheory CategoryTheory.Limits
universe u v
variable {A : Type u} [Category.{v} A] [Preadditive A]
variable (P : CochainComplex A ℤ) (M : A)

def term (q : ℕ) : AddCommGrp.{v} := AddCommGrp.of (P.X (-(q : ℤ)) ⟶ M)

def differential (q : ℕ) : term P M q ⟶ term P M (q+1) := AddCommGrp.ofHom
  { toFun := fun f => P.d (-((q+1 : ℕ) : ℤ)) (-(q : ℤ)) ≫ f
    map_zero' := by simp
    map_add' := by intro f g; simp only [Preadditive.comp_add] }

theorem square (q : ℕ) : differential P M q ≫ differential P M (q+1)=0 := by
  ext f
  change P.d (-((q+1+1 : ℕ) : ℤ)) (-((q+1 : ℕ) : ℤ)) ≫
    (P.d (-((q+1 : ℕ) : ℤ)) (-(q : ℤ)) ≫ f)=0
  rw [←Category.assoc,P.d_comp_d,Limits.zero_comp]

def complex : CochainComplex AddCommGrp.{v} ℕ :=
  CochainComplex.of (term P M) (differential P M) (square P M)

theorem differential_apply (q : ℕ) (f : (complex P M).X q) :
    (complex P M).d q (q+1) f=P.d (-((q+1 : ℕ) : ℤ)) (-(q : ℤ)) ≫ f := by
  dsimp only [complex]
  rw [CochainComplex.of_d]
  rfl

theorem term_zero {h q : ℕ} (hb : P.IsStrictlyGE (-(h : ℤ))) (hq : h<q) :
    IsZero ((complex P M).X q) := by
  letI := hb
  have hz := P.isZero_of_isStrictlyGE (-(h : ℤ)) (-(q : ℤ)) (by omega)
  letI : Subsingleton ((complex P M).X q) := ⟨fun f g => hz.eq_of_src f g⟩
  exact AddCommGrp.isZero_of_subsingleton _

theorem homology_zero {h q : ℕ} (hb : P.IsStrictlyGE (-(h : ℤ))) (hq : h<q) :
    IsZero ((complex P M).homology q) :=
  ((complex P M).sc q).isZero_homology_of_isZero_X₂ (term_zero P M hb hq)

#print axioms term
#print axioms differential
#print axioms square
#print axioms complex
#print axioms differential_apply
#print axioms term_zero
#print axioms homology_zero
end Verification.StrictCoefficientCochains
