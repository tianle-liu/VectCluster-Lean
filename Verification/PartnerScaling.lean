/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TranslatedStratum
import Mathlib.Tactic.Ring

/-!
# Partner Scaling

Rescale only the exchange partners in an actual quotient, fixing
the entire coefficient algebra (which may itself contain the originals).
-/
noncomputable section
namespace Verification.PartnerScaling
open MvPolynomial
variable {S ι : Type*} [CommRing S]

def scaleHom (a : ι → Sˣ) : MvPolynomial ι S →ₐ[S] MvPolynomial ι S :=
  aeval (fun i => C (a i : S) * X i)

theorem scaleHom_C (a : ι → Sˣ) (s : S) : scaleHom a (C s) = C s := by simp [scaleHom]
theorem scaleHom_X (a : ι → Sˣ) (i : ι) : scaleHom a (X i) = C (a i : S) * X i := by simp [scaleHom]

theorem scaleHom_inv_comp (a : ι → Sˣ) :
    (scaleHom (fun i => (a i)⁻¹)).comp (scaleHom a) = AlgHom.id S _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, scaleHom_X, scaleHom_C, map_mul, AlgHom.id_apply]
  rw [← mul_assoc, ← C_mul]
  simp

def scaleEquiv (a : ι → Sˣ) : MvPolynomial ι S ≃ₐ[S] MvPolynomial ι S :=
  AlgEquiv.ofAlgHom (scaleHom a) (scaleHom (fun i => (a i)⁻¹))
    (by simpa only [inv_inv] using scaleHom_inv_comp (fun i => (a i)⁻¹))
    (scaleHom_inv_comp a)

def relation (x g : ι → S) (i : ι) : MvPolynomial ι S := C (x i) * X i - C (g i)
def relations (x g : ι → S) : Ideal (MvPolynomial ι S) := Ideal.span (Set.range (relation x g))

theorem scale_relation (x g : ι → S) (a : ι → Sˣ) (i : ι) :
    scaleEquiv a (relation x (fun i => (a i : S) * g i) i) = C (a i : S) * relation x g i := by
  change scaleHom a _ = _
  simp only [relation, map_sub, map_mul, scaleHom_C, scaleHom_X]
  ring

theorem map_relations (x g : ι → S) (a : ι → Sˣ) :
    (relations x (fun i => (a i : S) * g i)).map (scaleEquiv a).toRingHom = relations x g := by
  rw [relations, Ideal.map_span, ← Set.range_comp]
  change Ideal.span (Set.range (fun i => scaleEquiv a (relation x (fun i => (a i : S) * g i) i))) = _
  simp only [scale_relation]
  exact TranslatedStratum.unit_scaled_span
    (fun i => Units.map (C : S →+* MvPolynomial ι S).toMonoidHom (a i)) (relation x g)

def quotientEquiv (x g : ι → S) (a : ι → Sˣ) :
    (MvPolynomial ι S ⧸ relations x (fun i => (a i : S) * g i)) ≃ₐ[S]
      (MvPolynomial ι S ⧸ relations x g) :=
  Ideal.quotientEquivAlg _ _ (scaleEquiv a) (map_relations x g a).symm

theorem quotientEquiv_coefficient (x g : ι → S) (a : ι → Sˣ) (s : S) :
    quotientEquiv x g a (Ideal.Quotient.mk _ (C s)) = Ideal.Quotient.mk _ (C s) := by
  change Ideal.Quotient.mk _ (scaleHom a (C s)) = _
  rw [scaleHom_C]

#print axioms scaleHom
#print axioms scaleHom_C
#print axioms scaleHom_X
#print axioms scaleHom_inv_comp
#print axioms scaleEquiv
#print axioms relation
#print axioms relations
#print axioms scale_relation
#print axioms map_relations
#print axioms quotientEquiv
#print axioms quotientEquiv_coefficient
end Verification.PartnerScaling
