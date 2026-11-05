/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ProjectiveConeTerms
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.Additive
import Mathlib.Data.Finset.Max

/-!
# Finite Projective Biproduct

Finite sums of actual bounded projective cochain complexes are bounded
and termwise projective. Integer support bounds are constructed explicitly.
-/
noncomputable section
namespace Verification.FiniteProjectiveBiproduct
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type*} [Category A] [Abelian A]
variable {ι : Type} [Fintype ι] (P : ι → CochainComplex A ℤ)

def termIso (k : ℤ) : (⨁ P).X k ≅ ⨁ fun i => (P i).X k :=
  (HomologicalComplex.eval A (ComplexShape.up ℤ) k).mapBiproduct P

theorem projective (h : ∀ i k, Projective ((P i).X k)) (k : ℤ) : Projective ((⨁ P).X k) := by
  letI : ∀ i, Projective ((P i).X k) := fun i => h i k
  have hp : Projective (⨁ fun i => (P i).X k) := {
    factors := fun f e _ => ⟨biproduct.desc (fun i => Projective.factorThru (biproduct.ι (fun j => (P j).X k) i ≫ f) e), by aesop_cat⟩ }
  exact Projective.of_iso (termIso P k).symm hp

theorem isZero_sum (f : ι → A) (h : ∀ i, IsZero (f i)) : IsZero (⨁ f) := by
  rw [IsZero.iff_id_eq_zero]
  apply biproduct.hom_ext
  intro i
  exact (h i).eq_of_tgt _ _

theorem bounded (h : ∀ i, ProjectiveConeTerms.Bounded (P i)) :
    ProjectiveConeTerms.Bounded (⨁ P) := by
  classical
  choose a b ha hb using h
  refine ⟨-(∑ i, |a i|), ∑ i, |b i|,?_,?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro k hk
    apply IsZero.of_iso (isZero_sum (fun i => (P i).X k) ?_) (termIso P k)
    intro i
    have hlo : -(∑ j, |a j|) ≤ a i :=
      (neg_le_neg (Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i))).trans (neg_abs_le (a i))
    exact (CochainComplex.isStrictlyGE_iff (P i) (a i)).mp (ha i) k (lt_of_lt_of_le hk hlo)
  · rw [CochainComplex.isStrictlyLE_iff]
    intro k hk
    apply IsZero.of_iso (isZero_sum (fun i => (P i).X k) ?_) (termIso P k)
    intro i
    have hhi : b i ≤ ∑ j, |b j| :=
      (le_abs_self (b i)).trans (Finset.single_le_sum (fun j _ => abs_nonneg (b j)) (Finset.mem_univ i))
    exact (CochainComplex.isStrictlyLE_iff (P i) (b i)).mp (hb i) k (lt_of_le_of_lt hhi hk)

#print axioms termIso
#print axioms projective
#print axioms isZero_sum
#print axioms bounded
end Verification.FiniteProjectiveBiproduct
