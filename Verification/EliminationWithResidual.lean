/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.Elimination
import Verification.StratumPresentation

/-!
# Elimination With Residual

Eliminate unit-coefficient partners while retaining arbitrary equations
in the remaining variables. In particular the remaining original x_i need
not vanish, so this applies to open exchange charts, not only zero strata.
-/

noncomputable section
namespace Verification.EliminationWithResidual
open MvPolynomial
variable {R ι κ : Type*} [CommRing R]

def combined (J : Ideal (MvPolynomial ι R)) (a : κ → Rˣ) (b : κ → R) :
    Ideal (MvPolynomial (ι ⊕ κ) R) :=
  Elimination.relations a b ⊔ J.map (rename Sum.inl).toRingHom

theorem mapped_residual (J : Ideal (MvPolynomial ι R)) (a : κ → Rˣ) (b : κ → R) :
    ((J.map (rename Sum.inl).toRingHom).map (Ideal.Quotient.mk (Elimination.relations a b))).map
      (Elimination.quotientEquiv a b).toRingHom = J := by
  rw [Ideal.map_map, Ideal.map_map]
  have h : (Elimination.quotientEquiv (ι := ι) a b).toRingHom.comp
      ((Ideal.Quotient.mk (Elimination.relations a b)).comp (rename Sum.inl).toRingHom) =
      RingHom.id (MvPolynomial ι R) := by
    exact congrArg AlgHom.toRingHom (Elimination.descend_includeFree (ι := ι) a b)
  rw [RingHom.comp_assoc, h, Ideal.map_id]

def quotientRingEquiv (J : Ideal (MvPolynomial ι R)) (a : κ → Rˣ) (b : κ → R) :
    (MvPolynomial (ι ⊕ κ) R ⧸ combined J a b) ≃+* (MvPolynomial ι R ⧸ J) :=
  (DoubleQuot.quotQuotEquivQuotSup (Elimination.relations a b)
    (J.map (rename Sum.inl).toRingHom)).symm.trans
    (Ideal.quotientEquiv _ J (Elimination.quotientEquiv a b).toRingEquiv
      (mapped_residual J a b).symm)

theorem quotientRingEquiv_generator (J : Ideal (MvPolynomial ι R))
    (a : κ → Rˣ) (b : κ → R) (p : MvPolynomial (ι ⊕ κ) R) :
    quotientRingEquiv J a b (Ideal.Quotient.mk (combined J a b) p) =
      Ideal.Quotient.mk J (Elimination.substitute a b p) := by
  dsimp only [quotientRingEquiv, RingEquiv.trans_apply]
  erw [DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk
    (Elimination.relations (ι := ι) a b) (J.map (rename Sum.inl).toRingHom) p]
  rfl

def quotientEquiv (J : Ideal (MvPolynomial ι R)) (a : κ → Rˣ) (b : κ → R) :
    (MvPolynomial (ι ⊕ κ) R ⧸ combined J a b) ≃ₐ[R] (MvPolynomial ι R ⧸ J) :=
  AlgEquiv.ofRingEquiv (f := quotientRingEquiv J a b) (fun r => by
    change quotientRingEquiv J a b (Ideal.Quotient.mk (combined J a b) (C r)) =
      Ideal.Quotient.mk J (C r)
    rw [quotientRingEquiv_generator]
    simp [Elimination.substitute])

def residualRelation (x g : (ι ⊕ κ) → R) (i : ι) : MvPolynomial ι R :=
  C (x (Sum.inl i)) * X i - C (g (Sum.inl i))

def residualIdeal (x g : (ι ⊕ κ) → R) : Ideal (MvPolynomial ι R) :=
  Ideal.span (Set.range (residualRelation x g))

theorem rename_residual (x g : (ι ⊕ κ) → R) (i : ι) :
    rename (Sum.inl : ι → ι ⊕ κ) (residualRelation x g i) =
      StratumPresentation.exchangeRelation x g (Sum.inl i) := by
  simp [residualRelation, StratumPresentation.exchangeRelation]

theorem exchangeIdeal_eq_combined (x g : (ι ⊕ κ) → R) (a : κ → Rˣ)
    (ha : ∀ k, x (Sum.inr k) = (a k : R)) :
    StratumPresentation.exchangeIdeal x g = combined (residualIdeal x g) a (fun k => g (Sum.inr k)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨v,rfl⟩
    cases v with
    | inl i =>
      rw [← rename_residual]
      exact (show (residualIdeal x g).map (rename Sum.inl).toRingHom ≤
        combined (residualIdeal x g) a (fun k => g (Sum.inr k)) from le_sup_right)
          (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self i)))
    | inr k =>
      have hm : Elimination.relation (ι := ι) a (fun k => g (Sum.inr k)) k ∈
          Elimination.relations a (fun k => g (Sum.inr k)) :=
        Ideal.subset_span (Set.mem_range_self k)
      apply (show Elimination.relations (ι := ι) a (fun k => g (Sum.inr k)) ≤
        combined (residualIdeal x g) a (fun k => g (Sum.inr k)) from le_sup_left)
      simpa only [Elimination.relation, StratumPresentation.exchangeRelation, ha] using hm
  · apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨k,rfl⟩
      have hm : StratumPresentation.exchangeRelation x g (Sum.inr k) ∈
          StratumPresentation.exchangeIdeal x g := Ideal.subset_span (Set.mem_range_self (Sum.inr k))
      simpa only [Elimination.relation, StratumPresentation.exchangeRelation, ha] using hm
    · apply Ideal.map_le_iff_le_comap.mpr
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change rename Sum.inl (residualRelation x g i) ∈ StratumPresentation.exchangeIdeal x g
      rw [rename_residual]
      exact Ideal.subset_span (Set.mem_range_self (Sum.inl i))

def exchangeQuotientEquiv (x g : (ι ⊕ κ) → R) (a : κ → Rˣ)
    (ha : ∀ k, x (Sum.inr k) = (a k : R)) :
    (MvPolynomial (ι ⊕ κ) R ⧸ StratumPresentation.exchangeIdeal x g) ≃ₐ[R]
      (MvPolynomial ι R ⧸ residualIdeal x g) :=
  (Ideal.quotientEquivAlgOfEq R (exchangeIdeal_eq_combined x g a ha)).trans
    (quotientEquiv (residualIdeal x g) a (fun k => g (Sum.inr k)))

#print axioms combined
#print axioms mapped_residual
#print axioms quotientRingEquiv
#print axioms quotientRingEquiv_generator
#print axioms quotientEquiv
#print axioms residualRelation
#print axioms residualIdeal
#print axioms rename_residual
#print axioms exchangeIdeal_eq_combined
#print axioms exchangeQuotientEquiv
end Verification.EliminationWithResidual
