/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FreePartnerQuotient
import Verification.EliminationWithResidual

/-!
# Freezing Presentation

In an actual exchange presentation with selected originals zero and
neighbor originals units, eliminate precisely the neighbor partners and
separate the selected free partners. Remaining mutable originals are not
inverted. Coefficient constraints stay in the residual presented ring.
-/
noncomputable section
namespace Verification.FreezingPresentation
open MvPolynomial
variable {R α ι κ : Type*} [CommRing R]
variable (x g : ((α ⊕ ι) ⊕ κ) → R)
attribute [local instance] MvPolynomial.algebraMvPolynomial

def coefficientConstraints : Ideal (MvPolynomial ι R) :=
  Ideal.span (Set.range (fun a : α => C (g (Sum.inl (Sum.inl a)))))

def retainedRelation (i : ι) : MvPolynomial ι R :=
  C (x (Sum.inl (Sum.inr i))) * X i - C (g (Sum.inl (Sum.inr i)))

def remainingIdeal : Ideal (MvPolynomial ι R) :=
  coefficientConstraints g ⊔ Ideal.span (Set.range (retainedRelation x g))

theorem residual_eq_free (hzero : ∀ a, x (Sum.inl (Sum.inl a)) = 0) :
    EliminationWithResidual.residualIdeal x g =
      FreePartnerQuotient.relations (α := α) (remainingIdeal x g) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨v, rfl⟩
    cases v with
    | inl a =>
      have ha : C (g (Sum.inl (Sum.inl a))) ∈ remainingIdeal x g :=
        (show coefficientConstraints g ≤ remainingIdeal x g from le_sup_left)
          (Ideal.subset_span (Set.mem_range_self a))
      have hm := Ideal.mem_map_of_mem (rename (Sum.inr : ι → α ⊕ ι)).toRingHom ha
      change rename (Sum.inr : ι → α ⊕ ι) (C (g (Sum.inl (Sum.inl a)))) ∈
        FreePartnerQuotient.relations (α := α) (remainingIdeal x g) at hm
      have hn := (FreePartnerQuotient.relations (α := α) (remainingIdeal x g)).neg_mem hm
      simpa only [EliminationWithResidual.residualRelation, hzero, map_zero, zero_mul,
        zero_sub, rename_C] using hn
    | inr i =>
      have hi : retainedRelation x g i ∈ remainingIdeal x g :=
        (show Ideal.span (Set.range (retainedRelation x g)) ≤ remainingIdeal x g from le_sup_right)
          (Ideal.subset_span (Set.mem_range_self i))
      have hm := Ideal.mem_map_of_mem (rename (Sum.inr : ι → α ⊕ ι)).toRingHom hi
      change rename (Sum.inr : ι → α ⊕ ι) (retainedRelation x g i) ∈
        FreePartnerQuotient.relations (α := α) (remainingIdeal x g) at hm
      simpa only [retainedRelation, map_sub, map_mul, rename_C, rename_X,
        EliminationWithResidual.residualRelation] using hm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨a, rfl⟩
      change rename (Sum.inr : ι → α ⊕ ι) (C (g (Sum.inl (Sum.inl a)))) ∈
        EliminationWithResidual.residualIdeal x g
      have hm : EliminationWithResidual.residualRelation x g (Sum.inl a) ∈
          EliminationWithResidual.residualIdeal x g := Ideal.subset_span (Set.mem_range_self _)
      have hn := (EliminationWithResidual.residualIdeal x g).neg_mem hm
      simpa only [EliminationWithResidual.residualRelation, hzero, map_zero, zero_mul,
        zero_sub, neg_neg, rename_C] using hn
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change rename (Sum.inr : ι → α ⊕ ι) (retainedRelation x g i) ∈
        EliminationWithResidual.residualIdeal x g
      have hm : EliminationWithResidual.residualRelation x g (Sum.inr i) ∈
          EliminationWithResidual.residualIdeal x g := Ideal.subset_span (Set.mem_range_self _)
      simpa only [retainedRelation, map_sub, map_mul, rename_C, rename_X,
        EliminationWithResidual.residualRelation] using hm

def preparedEquiv (a : κ → Rˣ)
    (hzero : ∀ v, x (Sum.inl (Sum.inl v)) = 0)
    (hunit : ∀ k, x (Sum.inr k) = (a k : R)) :
    (MvPolynomial ((α ⊕ ι) ⊕ κ) R ⧸ StratumPresentation.exchangeIdeal x g) ≃ₐ[R]
      MvPolynomial α (MvPolynomial ι R ⧸ remainingIdeal x g) :=
  (EliminationWithResidual.exchangeQuotientEquiv x g a hunit).trans
    ((Ideal.quotientEquivAlgOfEq R (residual_eq_free x g hzero)).trans
      (FreePartnerQuotient.quotientEquiv (remainingIdeal x g)))

#print axioms coefficientConstraints
#print axioms retainedRelation
#print axioms remainingIdeal
#print axioms residual_eq_free
#print axioms preparedEquiv
end Verification.FreezingPresentation
