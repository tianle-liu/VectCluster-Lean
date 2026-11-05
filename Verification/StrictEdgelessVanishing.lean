/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictNisnevichInput
import Verification.AffineAxisGeometry
import Verification.UniversalExchangeRecursion
import Verification.UniversalExchangeRegular

/-!
# Strict Edgeless Vanishing

The edgeless vanishing argument is an internal induction on the number
of actual D(xy-1) factors. Both preserving steps are derived from ordinary
principal localization: the closed zero section is the coefficient scheme,
and the closed hyperbola is its Laurent extension. The displayed equations
and their regularity, and all product identifications, were proved above.
-/
noncomputable section
namespace Verification.StrictEdgelessVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.UniversalExchangeChart
universe u
variable {M : Type u} (T : StrictNisnevichInput.Theory M)
attribute [local instance] MvPolynomial.algebraMvPolynomial

def Positive (A : Type) [CommRing A] : Prop :=
  ∀ (s : M) (q : ℕ), 0 < q → IsZero (T.cohomology (Spec (CommRingCat.of A)) s q)

theorem of_equiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (h : Positive T B) : Positive T A := by
  intro s q hq
  exact IsZero.of_iso (h s q hq) (T.iso (Scheme.Spec.mapIso e.toCommRingCatIso.symm.op) s q)

variable (k : Type) [Field k] (P : StrictNisnevichInput.Standard T k)
variable (A : Type) [CommRing A] [Algebra k A] [Algebra.Smooth k A]

include P k in
theorem affine_positive (ι : Type) [Fintype ι] (hA : Positive T A) :
    Positive T (MvPolynomial ι A) := by
  intro s q hq
  exact IsZero.of_iso (hA s q hq) (P.affine A ι s q)

include P k in
theorem principal_positive (f : A) (hf : IsSMulRegular A f)
    (hsm : Algebra.Smooth k (A ⧸ Ideal.span {f}))
    (hA : Positive T A) (hC : Positive T (A ⧸ Ideal.span {f})) :
    Positive T (Localization.Away f) := by
  intro s q hq
  let d := P.principal A f hf hsm s q
  have hl := IsZero.of_iso (hA s q hq) d.source
  have hr := IsZero.of_iso (hC (T.contract s) q hq) d.target
  exact IsZero.of_iso (d.exact.isZero_X₂ (hl.eq_of_src _ _) (hr.eq_of_tgt _ _)) d.middle.symm

variable [IsDomain A]

include P k in
theorem laurent_positive (hA : Positive T A) : Positive T (SingleLaurent.Laurent.{0,0} A) := by
  letI : Algebra.Smooth A (AffineAxisGeometry.Line A) := {}
  letI : Algebra.Smooth k (AffineAxisGeometry.Line A) :=
    Algebra.Smooth.comp k A (AffineAxisGeometry.Line A)
  have hC : Positive T (AffineAxisGeometry.Closed A) :=
    of_equiv T (AffineAxisGeometry.closedEquiv A).toRingEquiv hA
  have hs : Algebra.Smooth k (AffineAxisGeometry.Closed A) :=
    Algebra.Smooth.of_equiv ((AffineAxisGeometry.closedEquiv A).restrictScalars k).symm
  apply of_equiv T (AffineAxisGeometry.openEquiv A).toRingEquiv
  exact principal_positive T k P (AffineAxisGeometry.Line A) (AffineAxisGeometry.coordinate A)
    (AffineAxisGeometry.coordinate_regular A) hs (affine_positive T k P A PUnit hA) hC

include P k in
theorem surface_positive (hA : Positive T A) : Positive T (OpenPolynomial A (Fin 1)) := by
  letI : Algebra.Smooth A (HyperbolaGeometry.Plane A) := {}
  letI : Algebra.Smooth k (HyperbolaGeometry.Plane A) :=
    Algebra.Smooth.comp k A (HyperbolaGeometry.Plane A)
  letI : Algebra.Smooth A (SingleLaurent.Laurent.{0,0} A) := AffineAxisGeometry.laurent_smooth A
  letI : Algebra.Smooth k (SingleLaurent.Laurent.{0,0} A) :=
    Algebra.Smooth.comp k A (SingleLaurent.Laurent.{0,0} A)
  have hs : Algebra.Smooth k (HyperbolaGeometry.Closed A) :=
    Algebra.Smooth.of_equiv ((HyperbolaGeometry.closedEquiv A).restrictScalars k).symm
  apply of_equiv T (UniversalExchangeRecursion.oneEquiv A).toRingEquiv
  exact principal_positive T k P (HyperbolaGeometry.Plane A) (HyperbolaGeometry.equation A)
    (HyperbolaGeometry.equation_regular A) hs
    (affine_positive T k P A (Fin 1 ⊕ Fin 1) hA)
    (of_equiv T (HyperbolaGeometry.closedEquiv A).toRingEquiv (laurent_positive T k P A hA))

include P k in
theorem factors_positive (hA : Positive T A) (n : ℕ) : Positive T (OpenPolynomial A (Fin n)) := by
  induction n with
  | zero => exact of_equiv T (UniversalExchangeRecursion.emptyEquiv A).toRingEquiv hA
  | succ n ih =>
      letI : IsDomain (OpenPolynomial A (Fin n)) := UniversalExchangeRegular.domain A (Fin n)
      letI : Algebra.Smooth A (OpenPolynomial A (Fin n)) := UniversalExchangeRegular.smooth A (Fin n)
      letI : Algebra.Smooth k (OpenPolynomial A (Fin n)) :=
        Algebra.Smooth.comp k A (OpenPolynomial A (Fin n))
      exact of_equiv T (UniversalExchangeRecursion.successorEquiv A n).symm.toRingEquiv
        (surface_positive T k P (OpenPolynomial A (Fin n)) ih)

#print axioms Positive
#print axioms of_equiv
#print axioms affine_positive
#print axioms principal_positive
#print axioms laurent_positive
#print axioms surface_positive
#print axioms factors_positive
end Verification.StrictEdgelessVanishing
