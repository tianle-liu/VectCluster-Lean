/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ExchangeTransverseSlice
import Verification.ActualOpenPartners

/-!
# Actual Transverse Slice

The actual locally closed exchange chart W_(I,j) has the transverse
slice used in the manuscript. The morphism is a map of literal coordinate
rings, with exact images of original and mutated coordinates.
-/
noncomputable section
universe u
namespace Verification.ActualTransverseSlice
open MvPolynomial Verification.ActualOpenChart Verification.ExchangeTransverseSlice
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)

def openSlice : GlobalOpen R ι κ τ j B →ₐ[R] Slice (characters R ι κ τ B) :=
  (sliceMap (R := R) (characters R ι κ τ B) v).comp (globalOpenEquiv R ι κ τ j B hB).toAlgHom

theorem openSlice_coordinate (i : ι) :
    openSlice R ι κ τ j B hB v (globalCoordinate R ι κ τ j B i) =
      coordinate (characters R ι κ τ B) v i := by
  change sliceMap (R := R) _ _ (globalOpenEquiv R ι κ τ j B hB (globalCoordinate R ι κ τ j B i)) = _
  rw [globalOpenEquiv_coordinate,slice_x]

theorem openSlice_selected :
    openSlice R ι κ τ j B hB v (globalCoordinate R ι κ τ j B v) = Polynomial.X := by
  rw [openSlice_coordinate]
  classical
  simp [coordinate]

theorem openSlice_other (i : ι) (hi : i ≠ v) :
    openSlice R ι κ τ j B hB v (globalCoordinate R ι κ τ j B i) = 0 := by
  rw [openSlice_coordinate]
  classical
  simp [coordinate,hi]

theorem openSlice_partner (i : ι) :
    openSlice R ι κ τ j B hB v (ActualOpenPartners.globalPartner R ι κ τ j B i) = 0 := by
  change sliceMap (R := R) _ _ (globalOpenEquiv R ι κ τ j B hB (ActualOpenPartners.globalPartner R ι κ τ j B i)) = 0
  rw [ActualOpenPartners.globalOpenEquiv_partner,map_mul,slice_y,mul_zero]

def partialIdeal : Ideal (GlobalOpen R ι κ τ j B) :=
  Ideal.span (Set.range (fun i : {i : ι // i ≠ v} => globalCoordinate R ι κ τ j B i.1))

abbrev Intermediate := GlobalOpen R ι κ τ j B ⧸ partialIdeal R ι κ τ j B v

def transverseSlice : Intermediate R ι κ τ j B v →ₐ[R] Slice (characters R ι κ τ B) :=
  Ideal.Quotient.liftₐ (partialIdeal R ι κ τ j B v) (openSlice R ι κ τ j B hB v) (by
    change partialIdeal R ι κ τ j B v ≤ RingHom.ker (openSlice R ι κ τ j B hB v).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact openSlice_other R ι κ τ j B hB v i.1 i.2)

def originalParameter : Intermediate R ι κ τ j B v :=
  Ideal.Quotient.mk (partialIdeal R ι κ τ j B v) (globalCoordinate R ι κ τ j B v)

theorem transverse_parameter :
    transverseSlice R ι κ τ j B hB v (originalParameter R ι κ τ j B v) = Polynomial.X :=
  openSlice_selected R ι κ τ j B hB v

theorem transverse_partner (i : ι) :
    transverseSlice R ι κ τ j B hB v (Ideal.Quotient.mk (partialIdeal R ι κ τ j B v)
      (ActualOpenPartners.globalPartner R ι κ τ j B i)) = 0 :=
  openSlice_partner R ι κ τ j B hB v i

def closedIdeal : Ideal (Intermediate R ι κ τ j B v) := Ideal.span {originalParameter R ι κ τ j B v}

theorem closed_pullback :
    (closedIdeal R ι κ τ j B v).map (transverseSlice R ι κ τ j B hB v).toRingHom =
      parameterIdeal (characters R ι κ τ B) := by
  rw [closedIdeal,Ideal.map_span,Set.image_singleton]
  change Ideal.span {transverseSlice R ι κ τ j B hB v (originalParameter R ι κ τ j B v)} = _
  rw [transverse_parameter]
  rfl

def conormalMap : (closedIdeal R ι κ τ j B v).Cotangent →ₗ[R]
    (parameterIdeal (characters R ι κ τ B)).Cotangent :=
  Ideal.mapCotangent _ _ (transverseSlice R ι κ τ j B hB v)
    (Ideal.map_le_iff_le_comap.mp (le_of_eq (closed_pullback R ι κ τ j B hB v)))

theorem conormal_parameter :
    conormalMap R ι κ τ j B hB v
      ((closedIdeal R ι κ τ j B v).toCotangent
        ⟨originalParameter R ι κ τ j B v,Ideal.subset_span (Set.mem_singleton _)⟩) =
    (parameterIdeal (characters R ι κ τ B)).toCotangent
      ⟨Polynomial.X,Ideal.subset_span (Set.mem_singleton _)⟩ := by
  rw [conormalMap,Ideal.mapCotangent_toCotangent]
  apply congrArg (parameterIdeal (characters R ι κ τ B)).toCotangent
  apply Subtype.ext
  exact transverse_parameter R ι κ τ j B hB v

#print axioms openSlice
#print axioms openSlice_coordinate
#print axioms openSlice_selected
#print axioms openSlice_other
#print axioms openSlice_partner
#print axioms partialIdeal
#print axioms Intermediate
#print axioms transverseSlice
#print axioms originalParameter
#print axioms transverse_parameter
#print axioms transverse_partner
#print axioms closedIdeal
#print axioms closed_pullback
#print axioms conormalMap
#print axioms conormal_parameter
end Verification.ActualTransverseSlice
