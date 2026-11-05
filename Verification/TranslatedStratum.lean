/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StratumPresentation
import Verification.CharacterGenerators
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Translated Stratum

Assembling the actual (AS) zero-stratum algebra: zero original
coordinates give free exchange partners, the other partners are eliminated,
and the independent character equations give a translated split torus.
Each equivalence is between the presented quotient rings; no pointwise
bijection or pre-assumed geometric stratum equivalence is used.
-/
namespace Verification.TranslatedStratum
open CategoryTheory

variable {A ι : Type*} [CommRing A]

theorem unit_scaled_span (u : ι → Aˣ) (g : ι → A) :
    Ideal.span (Set.range (fun i => (u i : A) * g i)) = Ideal.span (Set.range g) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have hi : (u i : A) * g i ∈ Ideal.span (Set.range (fun i => (u i : A) * g i)) :=
      Ideal.subset_span (Set.mem_range_self i)
    have hi' := Ideal.mul_mem_left (Ideal.span (Set.range (fun i => (u i : A) * g i)))
      (((u i)⁻¹ : Aˣ) : A) hi
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using hi'

open Verification.StratumPresentation Verification.SplitTorusFiber Verification.CharacterGenerators
variable {R H K κ : Type*} [CommRing R] [CommGroup H] [CommGroup K]

/-- The residual coefficient ideal is exactly the primitive character ideal,
even when each exchange equation contains its own invertible monomial factor. -/
theorem coefficientIdeal_eq_characters
    (c : H →* Rˣ) (w : ι → H)
    (f : (ι ⊕ κ) → MonoidAlgebra R (H × K))
    (u : ι → (MonoidAlgebra R (H × K))ˣ)
    (hf : ∀ i, f (Sum.inl i) = (u i : MonoidAlgebra R (H × K)) * relation c (w i)) :
    coefficientIdeal f = generatorRelations c w := by
  unfold coefficientIdeal generatorRelations
  have heq : (fun i => f (Sum.inl i)) = fun i => (u i : MonoidAlgebra R (H × K)) * relation c (w i) :=
    funext hf
  rw [heq, unit_scaled_span]

/-- The assembled affine-times-torus algebra in split lattice coordinates. -/
noncomputable def stratumRingEquiv
    (c : H →* Rˣ) (w : ι → H) (hw : Subgroup.closure (Set.range w) = ⊤)
    (x f : (ι ⊕ κ) → MonoidAlgebra R (H × K))
    (a : κ → (MonoidAlgebra R (H × K))ˣ)
    (hx0 : ∀ i, x (Sum.inl i) = 0)
    (hxu : ∀ k, x (Sum.inr k) = (a k : MonoidAlgebra R (H × K)))
    (u : ι → (MonoidAlgebra R (H × K))ˣ)
    (hf : ∀ i, f (Sum.inl i) = (u i : MonoidAlgebra R (H × K)) * relation c (w i)) :
    (MvPolynomial (ι ⊕ κ) (MonoidAlgebra R (H × K)) ⧸ exchangeIdeal x f) ≃+*
      MvPolynomial ι (MonoidAlgebra R K) :=
  (quotientEquiv x f a hx0 hxu).toRingEquiv.trans
    (MvPolynomial.mapEquiv ι
      ((Ideal.quotEquivOfEq (coefficientIdeal_eq_characters c w f u hf)).trans
        (generatedFiberEquiv c w hw).toRingEquiv))

universe v
noncomputable def stratumSpecIso
    {S G T α β : Type v} [CommRing S] [CommGroup G] [CommGroup T]
    (c : G →* Sˣ) (w : α → G) (hw : Subgroup.closure (Set.range w) = ⊤)
    (x f : (α ⊕ β) → MonoidAlgebra S (G × T))
    (a : β → (MonoidAlgebra S (G × T))ˣ)
    (hx0 : ∀ i, x (Sum.inl i) = 0)
    (hxu : ∀ k, x (Sum.inr k) = (a k : MonoidAlgebra S (G × T)))
    (u : α → (MonoidAlgebra S (G × T))ˣ)
    (hf : ∀ i, f (Sum.inl i) = (u i : MonoidAlgebra S (G × T)) * relation c (w i)) :
    AlgebraicGeometry.Spec (CommRingCat.of
      (MvPolynomial (α ⊕ β) (MonoidAlgebra S (G × T)) ⧸ exchangeIdeal x f)) ≅
      AlgebraicGeometry.Spec (CommRingCat.of (MvPolynomial α (MonoidAlgebra S T))) :=
  AlgebraicGeometry.Scheme.Spec.mapIso
    (stratumRingEquiv c w hw x f a hx0 hxu u hf).toCommRingCatIso.symm.op

#print axioms unit_scaled_span
#print axioms coefficientIdeal_eq_characters
#print axioms stratumRingEquiv
#print axioms stratumSpecIso
end Verification.TranslatedStratum
