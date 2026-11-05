/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.EvenWittWordIndex
import Verification.EvenWittColorVanishing

/-!
# Even Witt Word Basis

The actual quotient basis indexed by the manuscript's (A_x,F) pairs;
each basis vector is the literal mutable/frozen Pfister product.
-/
noncomputable section
open scoped Classical BigOperators
namespace Verification.EvenWittWordBasis
open MonoidAlgebra Verification.OriginalWittQuotient Verification.EvenWittPfisterResidue
variable {V C : Type*} [Fintype V] [Fintype C]
variable (c : V → C) (I : Finset V)
variable (hc : Function.Injective (fun i : I => c i.val))

def factor : (V ⊕ C) → Stratum (EvenWittColumns.frozenMatrix c) I :=
  Sum.elim (fun i => Ideal.Quotient.mk _ (of ℤ _ (normalVector i)) - 1)
    (fun a => (-1:ℤ) • Ideal.Quotient.mk _ (of ℤ _ (frozen a)) - 1)

omit [Fintype V] [Fintype C] in
theorem remaining_factor (a : EvenWittPfisterBasis.Remaining c I) :
    factor c I a.val =
      (EvenWittPfisterBasis.signs c I a : ℤ) • EvenWittCoordinateSplit.coordinate c I a - 1 := by
  rcases a with ⟨a,ha⟩
  cases a with
  | inl v => simp only [factor,Sum.elim_inl,EvenWittPfisterBasis.signs,Units.val_one,one_smul]; rfl
  | inr a => rfl

omit [Fintype V] [Fintype C] in
theorem remaining_word (A : Finset (EvenWittPfisterBasis.Remaining c I)) :
    (∏ a ∈ A, ((EvenWittPfisterBasis.signs c I a : ℤ) •
      EvenWittCoordinateSplit.coordinate c I a - 1)) =
    quotientWord c I (EvenWittWordIndex.equiv c I A).val.1 (EvenWittWordIndex.equiv c I A).val.2 := by
  have he : (∏ a ∈ A, ((EvenWittPfisterBasis.signs c I a : ℤ) •
      EvenWittCoordinateSplit.coordinate c I a - 1)) =
      ∏ a ∈ A.map (Function.Embedding.subtype _), factor c I a := by
    rw [Finset.prod_map]
    apply Finset.prod_congr rfl
    intro a _
    exact (remaining_factor c I a).symm
  rw [he,Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]
  simp only [EvenWittWordIndex.equiv_val,quotientWord,word,mutableWord,frozenWord,
    map_mul,map_prod,map_sub,map_one,map_zsmul,factor,Sum.elim_inl,Sum.elim_inr]

def basis : Basis (EvenWittWordIndex.LocalIndex c I) ℤ (Stratum (EvenWittColumns.frozenMatrix c) I) :=
  (EvenWittPfisterBasis.basis c I hc (EvenWittPfisterBasis.signs c I)).reindex (EvenWittWordIndex.equiv c I)

theorem basis_word (AF : EvenWittWordIndex.LocalIndex c I) :
    basis c I hc AF = quotientWord c I AF.val.1 AF.val.2 := by
  rw [basis,Basis.reindex_apply,EvenWittPfisterBasis.basis_word,remaining_word]
  rw [Equiv.apply_symm_apply]

#print axioms factor
#print axioms remaining_factor
#print axioms remaining_word
#print axioms basis
#print axioms basis_word
end Verification.EvenWittWordBasis
