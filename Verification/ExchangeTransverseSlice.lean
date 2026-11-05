/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalExchangeSmooth
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Exchange Transverse Slice

The transverse affine-line slice in the actual local exchange ring.
Its coefficient torus is the genuine character quotient, and its map on
normal parameters and on ideal conormal classes is explicit.
-/
noncomputable section
universe u
namespace Verification.ExchangeTransverseSlice
open Verification.LocalExchangeSmooth
variable {R S ι : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (χ : ι → Sˣ) (j : ι)

def fiberIdeal : Ideal S := Ideal.span (Set.range (fun i => 1 + (χ i : S)))
abbrev Fiber := S ⧸ fiberIdeal χ
abbrev Slice := Polynomial (Fiber χ)

def coefficientMap : S →ₐ[R] Slice χ := IsScalarTower.toAlgHom R S (Slice χ)

def coordinate (i : ι) : Slice χ := by
  classical
  exact if i = j then Polynomial.X else 0

theorem coefficient_relation (i : ι) : (-1 : Slice χ) = coefficientMap (R := R) χ (χ i : S) := by
  have hh := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_range_self i) : 1 + (χ i : S) ∈ fiberIdeal χ)
  have hp := congrArg (Polynomial.C : Fiber χ →+* Slice χ) hh
  change -1 = Polynomial.C (Ideal.Quotient.mk _ (χ i : S))
  simp only [map_add,map_one,map_zero] at hp
  change 1 + Polynomial.C (Ideal.Quotient.mk (fiberIdeal χ) (χ i : S)) = 0 at hp
  linear_combination -hp

def sliceMap : LocalAlgebra χ →ₐ[R] Slice χ :=
  lift χ (coefficientMap (R := R) χ) (coordinate χ j) (fun _ => 0)
    (fun i => by rw [mul_zero,zero_sub]; exact coefficient_relation (R := R) χ i)

theorem slice_x (i : ι) : sliceMap (R := R) χ j (x χ i) = coordinate χ j i :=
  lift_x _ _ _ _ _ _

theorem slice_x_selected : sliceMap (R := R) χ j (x χ j) = Polynomial.X := by
  classical
  rw [slice_x]
  simp [coordinate]

theorem slice_x_other (i : ι) (hij : i ≠ j) : sliceMap (R := R) χ j (x χ i) = 0 := by
  classical
  rw [slice_x]
  simp [coordinate,hij]

theorem slice_y (i : ι) : sliceMap (R := R) χ j (y χ i) = 0 := lift_y _ _ _ _ _ _

theorem slice_coefficient (s : S) :
    sliceMap (R := R) χ j (algebraMap S (LocalAlgebra χ) s) = Polynomial.C (Ideal.Quotient.mk (fiberIdeal χ) s) :=
  lift_coefficient _ _ _ _ _ _

def boundaryIdeal : Ideal (LocalAlgebra χ) := Ideal.span {x χ j}
def parameterIdeal : Ideal (Slice χ) := Ideal.span {Polynomial.X}

theorem boundary_pullback : (boundaryIdeal χ j).map (sliceMap (R := R) χ j).toRingHom = parameterIdeal χ := by
  rw [boundaryIdeal,Ideal.map_span,Set.image_singleton]
  change Ideal.span {sliceMap (R := R) χ j (x χ j)} = parameterIdeal χ
  rw [slice_x_selected]
  rfl

theorem boundary_maps : boundaryIdeal χ j ≤ (parameterIdeal χ).comap (sliceMap (R := R) χ j).toRingHom :=
  Ideal.map_le_iff_le_comap.mp (le_of_eq (boundary_pullback (R := R) χ j))

def conormalMap : (boundaryIdeal χ j).Cotangent →ₗ[R] (parameterIdeal χ).Cotangent :=
  Ideal.mapCotangent (boundaryIdeal χ j) (parameterIdeal χ) (sliceMap (R := R) χ j) (boundary_maps (R := R) χ j)

theorem conormal_parameter :
    conormalMap (R := R) χ j ((boundaryIdeal χ j).toCotangent ⟨x χ j,Ideal.subset_span (Set.mem_singleton _)⟩) =
      (parameterIdeal χ).toCotangent ⟨Polynomial.X,Ideal.subset_span (Set.mem_singleton _)⟩ := by
  rw [conormalMap,Ideal.mapCotangent_toCotangent]
  apply congrArg (parameterIdeal χ).toCotangent
  apply Subtype.ext
  exact slice_x_selected (R := R) χ j

#print axioms fiberIdeal
#print axioms Fiber
#print axioms Slice
#print axioms coefficientMap
#print axioms coordinate
#print axioms coefficient_relation
#print axioms sliceMap
#print axioms slice_x
#print axioms slice_x_selected
#print axioms slice_x_other
#print axioms slice_y
#print axioms slice_coefficient
#print axioms boundaryIdeal
#print axioms parameterIdeal
#print axioms boundary_pullback
#print axioms boundary_maps
#print axioms conormalMap
#print axioms conormal_parameter
end Verification.ExchangeTransverseSlice
