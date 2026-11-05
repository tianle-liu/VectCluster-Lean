/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualTransverseOpen
import Verification.LocalTransverseTorusFace
import Verification.AffineSectionTransport

/-!
# Actual Torus Face

The original open transverse morphism is the actual torus-face map
followed by the old stratum's affine zero section. Under standard polynomial
A1 invariance this identifies the original open map with the torus map,
using constructed affine coordinates and no boundary comparison assumption.
-/
noncomputable section
namespace Verification.ActualTorusFace
open CategoryTheory Opposite MvPolynomial
open Verification.ActualOpenChart Verification.ActualTransverseSlice
open Verification.ActualTransverseLocalization Verification.ActualTransverseOpen
universe u
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)

abbrev OldTorus := LocalTransverseOpen.Laurent (characters R ι κ τ B) v

def torusFace : OldTorus R ι κ τ B v →ₐ[R] OpenTarget R ι κ τ B :=
  (LocalTransverseTorusFace.torusFace (characters R ι κ τ B) v).restrictScalars R

def affineFace : LocalTransverseOpen.Affine (characters R ι κ τ B) v →ₐ[R]
    OpenTarget R ι κ τ B :=
  (LocalTransverseTorusFace.affineFace (characters R ι κ τ B) v).restrictScalars R

theorem affine_square_coefficient (z : GlobalOpen R ι κ τ j B) :
    affineFace R ι κ τ B v (affineEquiv R ι κ τ j B hB v
      (algebraMap (Intermediate R ι κ τ j B v) (OpenSource R ι κ τ j B v)
        (Ideal.Quotient.mk (partialIdeal R ι κ τ j B v) z))) =
      localizedSlice R ι κ τ j B hB v
        (algebraMap (Intermediate R ι κ τ j B v) (OpenSource R ι κ τ j B v)
          (Ideal.Quotient.mk (partialIdeal R ι κ τ j B v) z)) := by
  change LocalTransverseTorusFace.affineFace (characters R ι κ τ B) v
    (LocalTransverseOpen.toAffine (characters R ι κ τ B) v
      (openEquiv R ι κ τ j B hB v (algebraMap (Intermediate R ι κ τ j B v)
        (OpenSource R ι κ τ j B v) (Ideal.Quotient.mk (partialIdeal R ι κ τ j B v) z)))) = _
  rw [openEquiv_include, LocalTransverseOpen.toAffine_include, localizedSlice_coefficient]
  exact AlgHom.congr_fun (LocalTransverseTorusFace.raw_square (characters R ι κ τ B) v)
    (globalOpenEquiv R ι κ τ j B hB z)

theorem affine_square : (affineFace R ι κ τ B v).comp
    (affineEquiv R ι κ τ j B hB v).toAlgHom = localizedSlice R ι κ τ j B hB v := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (originalParameter R ι κ τ j B v))
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  exact affine_square_coefficient R ι κ τ j B hB v

omit [Fintype ι] in
theorem affineFace_zero : affineFace R ι κ τ B v =
    (torusFace R ι κ τ B v).comp
      (PolynomialSectionIso.zeroEvaluation R (OldTorus R ι κ τ B v) (LocalTransverseOpen.Old v)) := by
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · intro a
    change LocalTransverseTorusFace.affineFace (characters R ι κ τ B) v (C a) =
      torusFace R ι κ τ B v (MvPolynomial.aeval (fun _ => (0 : OldTorus R ι κ τ B v)) (C a))
    rw [LocalTransverseTorusFace.affineFace_C, MvPolynomial.aeval_C]
    rfl
  · intro i
    change LocalTransverseTorusFace.affineFace (characters R ι κ τ B) v (X i) =
      torusFace R ι κ τ B v (MvPolynomial.aeval (fun _ => (0 : OldTorus R ι κ τ B v)) (X i))
    rw [LocalTransverseTorusFace.affineFace_X, MvPolynomial.aeval_X, map_zero]

def oldZeroSection : OpenSource R ι κ τ j B v →ₐ[R] OldTorus R ι κ τ B v :=
  (PolynomialSectionIso.zeroEvaluation R (OldTorus R ι κ τ B v) (LocalTransverseOpen.Old v)).comp
    (affineEquiv R ι κ τ j B hB v).toAlgHom

theorem torus_square : (torusFace R ι κ τ B v).comp (oldZeroSection R ι κ τ j B hB v) =
    localizedSlice R ι κ τ j B hB v := by
  rw [oldZeroSection, ← AlgHom.comp_assoc, ← affineFace_zero, affine_square]

variable {D : Type*} [Category D] (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ D)
variable [IsIso (PolynomialSectionIso.projectionMap R (OldTorus R ι κ τ B v) (LocalTransverseOpen.Old v) F)]

def oldIso : F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (OldTorus R ι κ τ B v))) ≅
    F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (OpenSource R ι κ τ j B v))) :=
  AffineSectionTransport.sectionIso R (OldTorus R ι κ τ B v) (LocalTransverseOpen.Old v)
    (OpenSource R ι κ τ j B v) (affineEquiv R ι κ τ j B hB v) F

theorem oldIso_hom : (oldIso R ι κ τ j B hB v F).hom =
    F.map (oldZeroSection R ι κ τ j B hB v).toUnder.op :=
  AffineSectionTransport.sectionIso_hom R (OldTorus R ι κ τ B v) (LocalTransverseOpen.Old v)
    (OpenSource R ι κ τ j B v) (affineEquiv R ι κ τ j B hB v) F

theorem actual_open_map : F.map (localizedSlice R ι κ τ j B hB v).toUnder.op ≫
    (oldIso R ι κ τ j B hB v F).inv = F.map (torusFace R ι κ τ B v).toUnder.op := by
  have h : F.map (localizedSlice R ι κ τ j B hB v).toUnder.op =
      F.map (torusFace R ι κ τ B v).toUnder.op ≫ (oldIso R ι κ τ j B hB v F).hom := by
    rw [oldIso_hom, ← Functor.map_comp]
    change F.map (localizedSlice R ι κ τ j B hB v).toUnder.op =
      F.map ((torusFace R ι κ τ B v).comp (oldZeroSection R ι κ τ j B hB v)).toUnder.op
    rw [torus_square]
  rw [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

#print axioms OldTorus
#print axioms torusFace
#print axioms affineFace
#print axioms affine_square_coefficient
#print axioms affine_square
#print axioms affineFace_zero
#print axioms oldZeroSection
#print axioms torus_square
#print axioms oldIso
#print axioms oldIso_hom
#print axioms actual_open_map
end Verification.ActualTorusFace
