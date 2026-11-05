/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PartnerScaling

/-!
# Nested Exchange Universal

Universal property of a nested polynomial exchange quotient over a
coefficient algebra. The coefficient algebra is an independent parameter.
-/
noncomputable section
namespace Verification.NestedExchangeUniversal
open MvPolynomial
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type*} (p : ι → MvPolynomial ι S)
attribute [local instance] MvPolynomial.algebraMvPolynomial
abbrev Ring := MvPolynomial ι (MvPolynomial ι S) ⧸ PartnerScaling.relations (fun i=>X i) p

def x (i : ι) : Ring S p := Ideal.Quotient.mk _ (C (X i))
def y (i : ι) : Ring S p := Ideal.Quotient.mk _ (X i)
def value (q : MvPolynomial ι S) : Ring S p := Ideal.Quotient.mk _ (C q)

def valueHom : MvPolynomial ι S →ₐ[S] Ring S p :=
  (Ideal.Quotient.mkₐ S (PartnerScaling.relations (fun i=>X i) p)).comp
    ({ toRingHom := C
       commutes' := fun _=>rfl } : MvPolynomial ι S →ₐ[S] MvPolynomial ι (MvPolynomial ι S))

theorem valueHom_apply (q : MvPolynomial ι S) : valueHom S p q=value S p q := rfl

theorem aeval_value (q : MvPolynomial ι S) :
    aeval (x S p) q=value S p q := by
  have h : aeval (x S p)=valueHom S p := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [aeval_X,valueHom_apply]
    rfl
  exact (AlgHom.congr_fun h q).trans (valueHom_apply S p q)

theorem equation (i : ι) : x S p i*y S p i=value S p (p i) := by
  apply sub_eq_zero.mp
  have h : Ideal.Quotient.mk (PartnerScaling.relations (fun i=>X i) p)
      (PartnerScaling.relation (fun i=>X i) p i)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  simpa only [PartnerScaling.relation,map_sub,map_mul,x,y,value] using h

theorem equation_aeval (i : ι) : x S p i*y S p i=aeval (x S p) (p i) := by
  rw [aeval_value,equation]

variable {T : Type*} [CommRing T] [Algebra R T]
def lift (φ : S →ₐ[R] T) (xx yy : ι → T)
    (h : ∀ i,xx i*yy i=aevalTower φ xx (p i)) : Ring S p →ₐ[R] T :=
  Ideal.Quotient.liftₐ _ (aevalTower (aevalTower φ xx) yy) (by
    change PartnerScaling.relations (fun i=>X i) p ≤ RingHom.ker (aevalTower (aevalTower φ xx) yy).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change aevalTower (aevalTower φ xx) yy (PartnerScaling.relation (fun i=>X i) p i)=0
    rw [PartnerScaling.relation,map_sub,map_mul,aevalTower_C,aevalTower_X,aevalTower_X,aevalTower_C]
    exact sub_eq_zero.mpr (h i))

theorem lift_x (φ : S →ₐ[R] T) (xx yy : ι → T)
    (h : ∀ i,xx i*yy i=aevalTower φ xx (p i)) (i : ι) :
    lift R S p φ xx yy h (x S p i)=xx i := by
  change aevalTower (aevalTower φ xx) yy (C (X i))=xx i
  rw [aevalTower_C,aevalTower_X]

theorem lift_y (φ : S →ₐ[R] T) (xx yy : ι → T)
    (h : ∀ i,xx i*yy i=aevalTower φ xx (p i)) (i : ι) :
    lift R S p φ xx yy h (y S p i)=yy i := by
  change aevalTower (aevalTower φ xx) yy (X i)=yy i
  rw [aevalTower_X]

theorem lift_coefficient (φ : S →ₐ[R] T) (xx yy : ι → T)
    (h : ∀ i,xx i*yy i=aevalTower φ xx (p i)) (s : S) :
    lift R S p φ xx yy h (algebraMap S (Ring S p) s)=φ s := by
  change aevalTower (aevalTower φ xx) yy (C (C s))=φ s
  rw [aevalTower_C,aevalTower_C]

theorem hom_ext (a b : Ring S p →ₐ[R] T)
    (hc : ∀ s,a (algebraMap S _ s)=b (algebraMap S _ s))
    (hx : ∀ i,a (x S p i)=b (x S p i)) (hy : ∀ i,a (y S p i)=b (y S p i)) : a=b := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · intro q
    have h : (a.toRingHom.comp (Ideal.Quotient.mk (PartnerScaling.relations (fun i=>X i) p))).comp C=
        (b.toRingHom.comp (Ideal.Quotient.mk (PartnerScaling.relations (fun i=>X i) p))).comp C := by
      apply MvPolynomial.ringHom_ext
      · exact hc
      · exact hx
    exact RingHom.congr_fun h q
  · exact hy

#print axioms Ring
#print axioms x
#print axioms y
#print axioms value
#print axioms valueHom
#print axioms valueHom_apply
#print axioms aeval_value
#print axioms equation
#print axioms equation_aeval
#print axioms lift
#print axioms lift_x
#print axioms lift_y
#print axioms lift_coefficient
#print axioms hom_ext
end Verification.NestedExchangeUniversal
