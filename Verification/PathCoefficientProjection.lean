/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathSignedStratumEquivalence
import Verification.PathOriginalStratumTransport
import Verification.PolynomialSectionIso

/-!
# Path Coefficient Projection

The actual path coefficient projection kills exactly the selected partner
coordinates; its signed original coordinates and coefficient section are explicit.
-/
noncomputable section
namespace Verification.PathCoefficientProjection
open Verification.PathCompression Verification.PathLiteralStratum Verification.PathClassRepresentatives
open Verification.PathSignedStratumCoefficients Verification.PathSignedStratumEquivalence
open Verification.PathOriginalStratumTransport Verification.IndependentChartIndex
open MvPolynomial
variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)

def selectedEquiv : I ≃ Selected n (mutableSet n I) where
  toFun i := ⟨mutableIndex hI i,mutableIndex_mem hI i⟩
  invFun i := ⟨i.val.val+1,(mem_mutableSet n I i.val).mp i.property⟩
  left_inv i := by
    apply Subtype.ext
    have hi := (Finset.mem_Icc.mp (hI.1 i.property)).1
    change i.val-1+1=i.val
    omega
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    change i.val.val+1-1=i.val.val
    omega

theorem selectedEquiv_val (i : I) : (selectedEquiv hI i).val=mutableIndex hI i := rfl

variable (R : Type) [CommRing R] (a b : R)

def partnerIdeal : Ideal (Layer R hI a b) :=
  Ideal.span (Set.range (fun i : I => layerY R hI a b (mutableIndex hI i)))

def projection : Layer R hI a b →ₐ[R] Coefficients R hI a b :=
  (PolynomialSectionIso.zeroEvaluation R (Coefficients R hI a b) I).comp
    (stratumEquiv R hI a b).toAlgHom

theorem projection_partner (i : I) : projection hI R a b (layerY R hI a b (mutableIndex hI i))=0 := by
  change PolynomialSectionIso.zeroEvaluation R _ I
    (stratumEquiv R hI a b (layerY R hI a b (mutableIndex hI i)))=0
  rw [stratumEquiv_partner]
  exact MvPolynomial.aeval_X _ _

theorem projection_signed (p : Vertices n I) :
    projection hI R a b (signedUnit R hI a b p : Layer R hI a b)=
      (signedCoordinate R hI a b p : Coefficients R hI a b) := by
  change PolynomialSectionIso.zeroEvaluation R _ I
    (stratumEquiv R hI a b (signedUnit R hI a b p : Layer R hI a b))=_
  rw [stratumEquiv_signed]
  exact MvPolynomial.aeval_C _ _

theorem projection_section (c : Coefficients R hI a b) :
    projection hI R a b (toLayer R hI a b c)=c := by
  have hh := AlgHom.congr_fun (forward_coefficients R hI a b) c
  change forward R hI a b (toLayer R hI a b c)=C c at hh
  change PolynomialSectionIso.zeroEvaluation R _ I (forward R hI a b (toLayer R hI a b c))=c
  rw [hh]
  exact MvPolynomial.aeval_C _ _

theorem projection_surjective : Function.Surjective (projection hI R a b) :=
  fun c => ⟨toLayer R hI a b c,projection_section hI R a b c⟩

#print axioms selectedEquiv
#print axioms selectedEquiv_val
#print axioms partnerIdeal
#print axioms projection
#print axioms projection_partner
#print axioms projection_signed
#print axioms projection_section
#print axioms projection_surjective
end Verification.PathCoefficientProjection
