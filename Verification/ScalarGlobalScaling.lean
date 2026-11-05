/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarExchangeRelabel
import Verification.PartnerScaling

/-!
# Scalar Global Scaling

Simultaneous constant rescaling of the literal global exchange quotient.
Only nonzero constants multiply original and partner coordinates. No original
coordinate is inverted in this equivalence, so it preserves all zero strata.
-/
noncomputable section
namespace Verification.ScalarGlobalScaling
open MvPolynomial
open scoped BigOperators
variable (R : Type*) [CommRing R]
variable {ρ σ : Type*} [Fintype ρ]
variable (j : σ → ρ) (B : ρ → σ → ℤ) (a b : σ → Rˣ) (w : ρ → Rˣ)

def common (i : σ) : Rˣ := a i * ∏ r, w r ^ (B r i).toNat
def partner (i : σ) : Rˣ := common R B a w i / w (j i)

def ambient : MvPolynomial σ (MvPolynomial ρ R) ≃ₐ[R] MvPolynomial σ (MvPolynomial ρ R) :=
  (mapAlgEquiv σ (PartnerScaling.scaleEquiv w)).trans
    ((PartnerScaling.scaleEquiv (fun i=>Units.map (C : R →+* MvPolynomial ρ R).toMonoidHom
      (partner R j B a w i))).restrictScalars R)

omit [Fintype ρ] in
theorem scale_monomial (w : ρ → Rˣ) [Fintype ρ] (p : ρ → ℕ) :
    PartnerScaling.scaleEquiv w (∏ r, (X r : MvPolynomial ρ R)^p r)=
      C (∏ r, (w r : R)^p r) * ∏ r, X r^p r := by
  change PartnerScaling.scaleHom w _ = _
  rw [map_prod]
  simp only [map_pow,PartnerScaling.scaleHom_X,mul_pow,Finset.prod_mul_distrib]
  rw [map_prod]
  simp only [map_pow]

theorem ambient_C (p : MvPolynomial ρ R) :
    ambient R j B a w (C p)=C (PartnerScaling.scaleEquiv w p) := by
  change PartnerScaling.scaleHom _ (MvPolynomial.map (PartnerScaling.scaleEquiv w).toRingHom (C p))=_
  rw [map_C,PartnerScaling.scaleHom_C]
  rfl

theorem ambient_X (i : σ) :
    ambient R j B a w (X i)=C (C (partner R j B a w i : R))*X i := by
  change PartnerScaling.scaleHom _ (MvPolynomial.map (PartnerScaling.scaleEquiv w).toRingHom (X i))=_
  rw [map_X,PartnerScaling.scaleHom_X]
  rfl

theorem ambient_original (r : ρ) :
    ambient R j B a w (C (X r))=C (C (w r : R))*C (X r) := by
  rw [ambient_C]
  change C (PartnerScaling.scaleHom w (X r))=_
  rw [PartnerScaling.scaleHom_X,map_mul]

variable (hbalance : ∀ i,a i * ∏ r,w r^(B r i).toNat = b i * ∏ r,w r^(-B r i).toNat)
include hbalance in
theorem scale_powerSum (i : σ) :
    PartnerScaling.scaleEquiv w (ScalarExchangeRelabel.powerSum R (fun r=>B r i) (a i) (b i))=
      C (common R B a w i : R)*ExchangeRelabel.powerSum R (fun r=>B r i) := by
  have h : (a i : R)*(∏ r,(w r : R)^(B r i).toNat)=
      (b i : R)*(∏ r,(w r : R)^(-B r i).toNat) := by
    exact_mod_cast hbalance i
  simp only [ScalarExchangeRelabel.powerSum,map_add,map_mul]
  have hc (r : R) : PartnerScaling.scaleEquiv w (C r)=C r := PartnerScaling.scaleHom_C w r
  rw [hc,hc]
  rw [scale_monomial,scale_monomial]
  simp only [common,Units.val_mul,Units.coe_prod,Units.val_pow_eq_pow_val,ExchangeRelabel.powerSum]
  rw [← mul_assoc,← map_mul,← mul_assoc,← map_mul,← h]
  ring

include hbalance in
theorem ambient_relation (i : σ) :
    ambient R j B a w (ScalarExchangeRelabel.relation R j B a b i)=
      C (C (common R B a w i : R))*ExchangeRelabel.relation R j B i := by
  have h : (w (j i) : R)*(partner R j B a w i : R)=(common R B a w i : R) := by
    change ((w (j i) * (common R B a w i / w (j i)) : Rˣ) : R)=_
    congr 1
    simp [div_eq_mul_inv,mul_comm]
  rw [ScalarExchangeRelabel.relation,map_sub,map_mul,ambient_original,ambient_X,
    ambient_C,scale_powerSum R B a b w hbalance,map_mul,ExchangeRelabel.relation]
  rw [show C (C (w (j i) : R))*C (X (j i))*(C (C (partner R j B a w i : R))*X i)=
    (C (C (w (j i) : R))*C (C (partner R j B a w i : R)))*(C (X (j i))*X i) by ring,
      ← C_mul,← C_mul,h]
  ring

include hbalance in
theorem map_relations : (ScalarExchangeRelabel.relations R j B a b).map
    (ambient R j B a w).toRingHom=ExchangeRelabel.relations R j B := by
  rw [ScalarExchangeRelabel.relations,Ideal.map_span,← Set.range_comp]
  change Ideal.span (Set.range (fun i=>ambient R j B a w (ScalarExchangeRelabel.relation R j B a b i)))=_
  simp only [ambient_relation R j B a b w hbalance]
  exact TranslatedStratum.unit_scaled_span
    (fun i=>Units.map (C.comp C : R →+* MvPolynomial σ (MvPolynomial ρ R)).toMonoidHom
      (common R B a w i)) (ExchangeRelabel.relation R j B)

def quotientEquiv : (MvPolynomial σ (MvPolynomial ρ R) ⧸ ScalarExchangeRelabel.relations R j B a b) ≃ₐ[R]
    (MvPolynomial σ (MvPolynomial ρ R) ⧸ ExchangeRelabel.relations R j B) :=
  Ideal.quotientEquivAlg _ _ (ambient R j B a w) (map_relations R j B a b w hbalance).symm

theorem quotient_original (r : ρ) :
    quotientEquiv R j B a b w hbalance (Ideal.Quotient.mk _ (C (X r)))=
      algebraMap R _ (w r : R)*ExchangeRelabel.original R j B r := by
  change Ideal.Quotient.mk _ (ambient R j B a w (C (X r)))=_
  rw [ambient_original,map_mul]
  rfl

#print axioms common
#print axioms partner
#print axioms ambient
#print axioms scale_monomial
#print axioms ambient_C
#print axioms ambient_X
#print axioms ambient_original
#print axioms scale_powerSum
#print axioms ambient_relation
#print axioms map_relations
#print axioms quotientEquiv
#print axioms quotient_original
end Verification.ScalarGlobalScaling
