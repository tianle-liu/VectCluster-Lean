/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarGlobalScaling

/-!
# Two Term Coordinate Scaling

Unit rescaling of both original and partner polynomial variables in an
exchange presentation, allowing both coefficient families to change. This is
global over the coefficient ring and requires no mutable coordinate inverse.
-/
noncomputable section
namespace Verification.TwoTermCoordinateScaling
open MvPolynomial
open scoped BigOperators
variable (S : Type*) [CommRing S] {ρ σ : Type*} [Fintype ρ]
variable (j : σ → ρ) (B : ρ → σ → ℤ)
variable (a b a' b' : σ → Sˣ) (w : ρ → Sˣ) (γ : σ → Sˣ)

def ambient : MvPolynomial σ (MvPolynomial ρ S) ≃ₐ[S] MvPolynomial σ (MvPolynomial ρ S) :=
  (mapAlgEquiv σ (PartnerScaling.scaleEquiv w)).trans
    ((PartnerScaling.scaleEquiv (fun i=>Units.map (C : S →+* MvPolynomial ρ S).toMonoidHom
      (γ i / w (j i)))).restrictScalars S)

omit [Fintype ρ] in
theorem ambient_C (p : MvPolynomial ρ S) : ambient S j w γ (C p)=C (PartnerScaling.scaleEquiv w p) := by
  change PartnerScaling.scaleHom _ (MvPolynomial.map (PartnerScaling.scaleEquiv w).toRingHom (C p))=_
  rw [map_C,PartnerScaling.scaleHom_C]
  rfl

omit [Fintype ρ] in
theorem ambient_X (i : σ) : ambient S j w γ (X i)=C (C ((γ i / w (j i) : Sˣ) : S))*X i := by
  change PartnerScaling.scaleHom _ (MvPolynomial.map (PartnerScaling.scaleEquiv w).toRingHom (X i))=_
  rw [map_X,PartnerScaling.scaleHom_X]
  rfl

omit [Fintype ρ] in
theorem ambient_original (r : ρ) : ambient S j w γ (C (X r))=C (C (w r : S))*C (X r) := by
  rw [ambient_C]
  change C (PartnerScaling.scaleHom w (X r))=_
  rw [PartnerScaling.scaleHom_X,map_mul]

variable (ha : ∀ i,a i*∏ r,w r^(B r i).toNat=γ i*a' i)
variable (hb : ∀ i,b i*∏ r,w r^(-B r i).toNat=γ i*b' i)
include ha hb in
theorem powerSum_image (i : σ) :
    PartnerScaling.scaleEquiv w (ScalarExchangeRelabel.powerSum S (fun r=>B r i) (a i) (b i))=
      C (γ i : S)*ScalarExchangeRelabel.powerSum S (fun r=>B r i) (a' i) (b' i) := by
  have hp : (a i : S)*(∏ r,(w r : S)^(B r i).toNat)=(γ i : S)*(a' i : S) := by exact_mod_cast ha i
  have hn : (b i : S)*(∏ r,(w r : S)^(-B r i).toNat)=(γ i : S)*(b' i : S) := by exact_mod_cast hb i
  have hc (s : S) : PartnerScaling.scaleEquiv w (C s)=C s := PartnerScaling.scaleHom_C w s
  simp only [ScalarExchangeRelabel.powerSum,map_add,map_mul,hc]
  rw [ScalarGlobalScaling.scale_monomial,ScalarGlobalScaling.scale_monomial,
    ← mul_assoc,← C_mul,← mul_assoc,← C_mul,hp,hn]
  simp only [map_mul]
  ring

include ha hb in
theorem relation_image (i : σ) : ambient S j w γ (ScalarExchangeRelabel.relation S j B a b i)=
    C (C (γ i : S))*ScalarExchangeRelabel.relation S j B a' b' i := by
  have hu : (w (j i) : S)*((γ i/w (j i) : Sˣ) : S)=(γ i : S) := by
    change ((w (j i)*(γ i/w (j i)) : Sˣ) : S)=_
    congr 1
    simp [div_eq_mul_inv,mul_comm]
  rw [ScalarExchangeRelabel.relation,map_sub,map_mul,ambient_original,ambient_X,ambient_C,
    powerSum_image S B a b a' b' w γ ha hb,map_mul,ScalarExchangeRelabel.relation]
  rw [show C (C (w (j i) : S))*C (X (j i))*(C (C ((γ i/w (j i) : Sˣ) : S))*X i)=
    (C (C (w (j i) : S))*C (C ((γ i/w (j i) : Sˣ) : S)))*(C (X (j i))*X i) by ring,
    ← C_mul,← C_mul,hu]
  ring

include ha hb in
theorem map_relations : (ScalarExchangeRelabel.relations S j B a b).map (ambient S j w γ).toRingHom=
    ScalarExchangeRelabel.relations S j B a' b' := by
  rw [ScalarExchangeRelabel.relations,Ideal.map_span,← Set.range_comp]
  change Ideal.span (Set.range (fun i=>ambient S j w γ (ScalarExchangeRelabel.relation S j B a b i)))=_
  simp only [relation_image S j B a b a' b' w γ ha hb]
  exact TranslatedStratum.unit_scaled_span
    (fun i=>Units.map (C.comp C : S →+* MvPolynomial σ (MvPolynomial ρ S)).toMonoidHom (γ i))
      (ScalarExchangeRelabel.relation S j B a' b')

def quotientEquiv :
    (MvPolynomial σ (MvPolynomial ρ S) ⧸ ScalarExchangeRelabel.relations S j B a b) ≃ₐ[S]
      (MvPolynomial σ (MvPolynomial ρ S) ⧸ ScalarExchangeRelabel.relations S j B a' b') :=
  Ideal.quotientEquivAlg _ _ (ambient S j w γ) (map_relations S j B a b a' b' w γ ha hb).symm

#print axioms ambient
#print axioms ambient_C
#print axioms ambient_X
#print axioms ambient_original
#print axioms powerSum_image
#print axioms relation_image
#print axioms map_relations
#print axioms quotientEquiv
end Verification.TwoTermCoordinateScaling
