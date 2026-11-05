/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AffineComponentUnits
import Verification.ProductComponentIdempotents
import Verification.BoundaryComponentSelector

/-!
# Affine Component Unit Generation

All units of a finite product of affine-over-torus rings are generated
by units of the whole coefficient product and individual component Laurent
selectors. This uses the proved unit-coordinate equivalence, not a unit
classification hypothesis.
-/
noncomputable section
namespace Verification.AffineComponentUnitGeneration
open scoped BigOperators
open Verification.AffineComponentUnits
variable {J : Type} (R : J → Type) [∀ j, CommRing (R j)] [∀ j, IsDomain (R j)]
variable (ι κ : Type) [Fintype ι] [Fintype κ]
attribute [local instance] Classical.propDecidable

theorem coordinates_symm_val (z : ∀ j, (R j)ˣ × Multiplicative (κ →₀ ℤ)) (j : J) :
    ((coordinates R ι κ).symm z : AffineComponentUnits.Ring R ι κ) j =
      MvPolynomial.C (LaurentUnitCoordinates.monomial (R j) κ (z j).1 (z j).2.toAdd :
        OriginalTorus.Torus (R j) κ) := rfl

def coefficient (c : (∀ j, R j)ˣ) : (AffineComponentUnits.Ring R ι κ)ˣ :=
  (coordinates R ι κ).symm (fun j => (MulEquiv.piUnits c j, 1))

def selector (j : J) (k : κ) : (AffineComponentUnits.Ring R ι κ)ˣ :=
  (coordinates R ι κ).symm (fun l => (1, Multiplicative.ofAdd (if l = j then Finsupp.single k 1 else 0)))

theorem coefficient_coordinates (c : (∀ j, R j)ˣ) :
    coordinates R ι κ (coefficient R ι κ c) = fun j => (MulEquiv.piUnits c j, 1) :=
  (coordinates R ι κ).apply_symm_apply _

theorem selector_coordinates (j : J) (k : κ) :
    coordinates R ι κ (selector R ι κ j k) =
      fun l => (1, Multiplicative.ofAdd (if l = j then Finsupp.single k 1 else 0)) :=
  (coordinates R ι κ).apply_symm_apply _

theorem coefficient_val (c : (∀ j, R j)ˣ) (j : J) :
    (coefficient R ι κ c : AffineComponentUnits.Ring R ι κ) j =
      MvPolynomial.C (algebraMap (R j) (OriginalTorus.Torus (R j) κ) ((c : ∀ j, R j) j)) := by
  rw [coefficient, coordinates_symm_val]
  simp [LaurentUnitCoordinates.monomial]

theorem selector_val (j l : J) (k : κ) :
    (selector R ι κ j k : AffineComponentUnits.Ring R ι κ) l =
      if l = j then MvPolynomial.C (OriginalTorus.torusCoordinate (R l) κ k) else 1 := by
  rw [selector, coordinates_symm_val]
  by_cases h : l = j
  · simp only [h, if_true, LaurentUnitCoordinates.monomial, map_one, one_mul]
    rfl
  · simp [h, LaurentUnitCoordinates.monomial]

def coefficientHom : (∀ j, R j) →+* AffineComponentUnits.Ring R ι κ where
  toFun c j := MvPolynomial.C (algebraMap (R j) (OriginalTorus.Torus (R j) κ) (c j))
  map_one' := by
    funext j
    exact ((MvPolynomial.C : OriginalTorus.Torus (R j) κ →+* MvPolynomial ι _).comp
      (algebraMap (R j) (OriginalTorus.Torus (R j) κ))).map_one
  map_mul' c d := by
    funext j
    exact ((MvPolynomial.C : OriginalTorus.Torus (R j) κ →+* MvPolynomial ι _).comp
      (algebraMap (R j) (OriginalTorus.Torus (R j) κ))).map_mul (c j) (d j)
  map_zero' := by funext j; simp
  map_add' c d := by funext j; simp

theorem coefficient_eq_map (c : (∀ j, R j)ˣ) :
    coefficient R ι κ c = Units.map (coefficientHom R ι κ).toMonoidHom c := by
  apply Units.ext
  funext j
  exact coefficient_val R ι κ c j

def indicator (j : J) : AffineComponentUnits.Ring R ι κ :=
  ProductComponentIdempotents.indicator
    (fun j => MvPolynomial ι (OriginalTorus.Torus (R j) κ)) (RingEquiv.refl _) j

omit [∀ j, IsDomain (R j)] [Fintype ι] [Fintype κ] in
theorem indicator_val (j l : J) : indicator R ι κ j l = if l = j then 1 else 0 := by
  by_cases h : l = j
  · subst l
    simp [indicator, ProductComponentIdempotents.indicator]
  · simp [indicator, ProductComponentIdempotents.indicator, Pi.single_apply, h]

omit [∀ j, IsDomain (R j)] [Fintype ι] [Fintype κ] in
theorem indicator_idempotent (j : J) : indicator R ι κ j * indicator R ι κ j = indicator R ι κ j :=
  ProductComponentIdempotents.indicator_idempotent
    (fun j => MvPolynomial ι (OriginalTorus.Torus (R j) κ)) (RingEquiv.refl _) j

def variableUnit (k : κ) : (AffineComponentUnits.Ring R ι κ)ˣ :=
  MulEquiv.piUnits.symm (fun j => IntegralPolynomialUnits.constants (OriginalTorus.Torus (R j) κ) ι
    (ScalarGlobalUnits.laurentVariable (R j) κ k))

omit [∀ j, IsDomain (R j)] [Fintype ι] [Fintype κ] in
theorem variableUnit_val (k : κ) (j : J) :
    (variableUnit R ι κ k : AffineComponentUnits.Ring R ι κ) j =
      MvPolynomial.C (OriginalTorus.torusCoordinate (R j) κ k) := rfl

theorem selector_ring_value (j : J) (k : κ) :
    (selector R ι κ j k : AffineComponentUnits.Ring R ι κ) =
      1 - indicator R ι κ j + indicator R ι κ j * (variableUnit R ι κ k : AffineComponentUnits.Ring R ι κ) := by
  funext l
  rw [selector_val]
  change (if l = j then MvPolynomial.C (OriginalTorus.torusCoordinate (R l) κ k) else 1) =
    1 - indicator R ι κ j l + indicator R ι κ j l *
      (variableUnit R ι κ k : AffineComponentUnits.Ring R ι κ) l
  rw [indicator_val, variableUnit_val]
  by_cases h : l = j <;> simp [h]

theorem selector_boundary_unit (j : J) (k : κ) : selector R ι κ j k =
    BoundaryComponentSelector.unit (indicator R ι κ j) (indicator_idempotent R ι κ j)
      (variableUnit R ι κ k) :=
  Units.ext (selector_ring_value R ι κ j k)

variable [Fintype J]

theorem selector_product_coordinates (a : J → κ →₀ ℤ) (l : J) :
    coordinates R ι κ (∏ j, ∏ k, selector R ι κ j k ^ (a j k)) l =
      (1, Multiplicative.ofAdd (a l)) := by
  simp only [map_prod, Finset.prod_apply]
  rw [Finset.prod_eq_single l]
  · have hp (f : ∀ j, (R j)ˣ × Multiplicative (κ →₀ ℤ)) (z : ℤ) : (f ^ z) l = f l ^ z := rfl
    simp only [map_zpow, selector_coordinates, hp, if_pos rfl]
    change (∏ k, ((1 : (R l)ˣ), Multiplicative.ofAdd (Finsupp.single k (1 : ℤ))) ^ (a l k)) = _
    apply Prod.ext
    · change MonoidHom.fst (R l)ˣ (Multiplicative (κ →₀ ℤ))
        (∏ k, (1, Multiplicative.ofAdd (Finsupp.single k (1 : ℤ))) ^ (a l k)) = 1
      rw [map_prod]
      simp
    · change MonoidHom.snd (R l)ˣ (Multiplicative (κ →₀ ℤ))
        (∏ k, (1, Multiplicative.ofAdd (Finsupp.single k (1 : ℤ))) ^ (a l k)) = _
      rw [map_prod]
      simpa using FinsuppLaurentUnits.exponent_expansion κ (a l)
  · intro j _ hj
    simp [selector_coordinates, Ne.symm hj]
  · simp

def constantPart (u : (AffineComponentUnits.Ring R ι κ)ˣ) : (∀ j, R j)ˣ :=
  MulEquiv.piUnits.symm (fun j => (coordinates R ι κ u j).1)

def exponentPart (u : (AffineComponentUnits.Ring R ι κ)ˣ) (j : J) : κ →₀ ℤ :=
  (coordinates R ι κ u j).2.toAdd

theorem decomposition (u : (AffineComponentUnits.Ring R ι κ)ˣ) :
    u = coefficient R ι κ (constantPart R ι κ u) *
      ∏ j, ∏ k, selector R ι κ j k ^ (exponentPart R ι κ u j k) := by
  apply (coordinates R ι κ).injective
  rw [map_mul, coefficient_coordinates]
  funext j
  rw [Pi.mul_apply, selector_product_coordinates]
  simp [constantPart, exponentPart]

variable {G : Type*} [AddCommGroup G]

theorem additive_decomposition (f : Additive ((AffineComponentUnits.Ring R ι κ)ˣ) →+ G)
    (u : (AffineComponentUnits.Ring R ι κ)ˣ) :
    f (Additive.ofMul u) = f (Additive.ofMul (coefficient R ι κ (constantPart R ι κ u))) +
      ∑ j, ∑ k, (exponentPart R ι κ u j k) • f (Additive.ofMul (selector R ι κ j k)) := by
  calc
    f (Additive.ofMul u) = f (Additive.ofMul
      (coefficient R ι κ (constantPart R ι κ u) *
        ∏ j, ∏ k, selector R ι κ j k ^ (exponentPart R ι κ u j k))) :=
          congrArg (fun v => f (Additive.ofMul v)) (decomposition R ι κ u)
    _ = _ := by simp only [ofMul_mul, ofMul_prod, ofMul_zpow, map_add, map_sum, map_zsmul]

#print axioms coordinates_symm_val
#print axioms coefficient
#print axioms selector
#print axioms coefficient_coordinates
#print axioms selector_coordinates
#print axioms coefficient_val
#print axioms selector_val
#print axioms coefficientHom
#print axioms coefficient_eq_map
#print axioms indicator
#print axioms indicator_val
#print axioms indicator_idempotent
#print axioms variableUnit
#print axioms variableUnit_val
#print axioms selector_ring_value
#print axioms selector_boundary_unit
#print axioms selector_product_coordinates
#print axioms constantPart
#print axioms exponentPart
#print axioms decomposition
#print axioms additive_decomposition
end Verification.AffineComponentUnitGeneration
