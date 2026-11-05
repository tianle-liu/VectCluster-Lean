/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictPrincipalLongExact

/-!
# Strict Cohomological Dimension

The dimension inequality and high-degree restriction isomorphism
used in the original framed-freezing induction, derived from the four
ordinary localization terms.
-/
noncomputable section
namespace Verification.StrictCohomologicalDimension
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
variable {M : Type u} (T : StrictNisnevichInput.Theory M)

def Bound (A : Type) [CommRing A] (d : ℕ) : Prop :=
  ∀ (F : M) (q : ℕ), d < q → IsZero (T.cohomology (Spec (CommRingCat.of A)) F q)

theorem of_equiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (d : ℕ) (h : Bound T B d) : Bound T A d := by
  intro F q hq
  exact IsZero.of_iso (h F q hq) (T.iso (Scheme.Spec.mapIso e.toCommRingCatIso.symm.op) F q)

variable (k : Type) [Field k] (P : StrictPrincipalLongExact.Standard T k)
variable (A : Type) [CommRing A] [Algebra k A] [Algebra.Smooth k A]
variable (f : A) (hf : IsSMulRegular A f) (hs : Algebra.Smooth k (A ⧸ Ideal.span {f}))

include P hf hs in
theorem principal_bound (du dc : ℕ) (hu : Bound T (Localization.Away f) du)
    (hc : Bound T (A ⧸ Ideal.span {f}) dc) : Bound T A (max du (dc+1)) := by
  intro F q hq
  cases q with
  | zero => omega
  | succ q =>
    have hleft := hc (T.contract F) q (by omega)
    have hright := hu F (q+1) (by omega)
    let d := P.sequence A f hf hs F q
    exact d.left_exact.isZero_X₂ (hleft.eq_of_src _ _) (hright.eq_of_tgt _ _)

include P hf hs in
theorem restriction_isIso (hc : Bound T (A ⧸ Ideal.span {f}) 0)
    (F : M) (q : ℕ) (hq : 0 < q) :
    IsIso (P.sequence A f hf hs F q).restriction := by
  let d := P.sequence A f hf hs F q
  have hl := hc (T.contract F) q hq
  have hr := hc (T.contract F) (q+1) (by omega)
  letI : Mono d.restriction := d.left_exact.mono_g (hl.eq_of_src _ _)
  letI : Epi d.restriction := d.right_exact.epi_f (hr.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi d.restriction

#print axioms Bound
#print axioms of_equiv
#print axioms principal_bound
#print axioms restriction_isIso
end Verification.StrictCohomologicalDimension
