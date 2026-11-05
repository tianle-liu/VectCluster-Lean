/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PartialPowerSmooth

/-!
# Partial Power Product

An explicit product decomposition of a partial Laurent power fiber.
The constrained roots form the actual finite power quotient; all other
Laurent coordinates remain free. Both directions are defined on generators.
-/
noncomputable section
universe u
namespace Verification.PartialPowerProduct
open Verification.DiagonalPowerFibers
open Verification.PrimitiveCharacters
variable {R ι κ : Type u} [CommRing R]

abbrev FreeIndex (j : κ ↪ ι) := {i : ι // i ∉ Set.range j}
abbrev ProductAlgebra (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) :=
  Laurent (PowerAlgebra e b) (FreeIndex j)

def freeUnit (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (i : FreeIndex j) :
    (ProductAlgebra j e b)ˣ :=
  (MonoidAlgebra.of (PowerAlgebra e b) (Multiplicative (FreeIndex j →₀ ℤ))).toHomUnits
    (Multiplicative.ofAdd (Finsupp.single i 1))

def rootUnit (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (he : ∀ k, 0 < e k) (k : κ) :
    (ProductAlgebra j e b)ˣ :=
  Units.map (algebraMap (PowerAlgebra e b) (ProductAlgebra j e b)).toMonoidHom
    (coordinateUnits e b he k)

theorem rootUnit_val (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ)
    (he : ∀ k, 0 < e k) (k : κ) :
    (rootUnit j e b he k : ProductAlgebra j e b) =
      algebraMap (PowerAlgebra e b) (ProductAlgebra j e b) (coordinate e b k) := by
  simp [rootUnit, coordinateUnits]

def assigned (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (he : ∀ k, 0 < e k) :
    ι → (ProductAlgebra j e b)ˣ := by
  classical
  exact Function.extend j (rootUnit j e b he)
    (fun i => if h : i ∉ Set.range j then freeUnit j e b ⟨i,h⟩ else 1)

theorem assigned_selected (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ)
    (he : ∀ k, 0 < e k) (k : κ) : assigned j e b he (j k) = rootUnit j e b he k := by
  classical
  exact j.injective.extend_apply _ _ k

theorem assigned_free (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ)
    (he : ∀ k, 0 < e k) (i : FreeIndex j) : assigned j e b he i = freeUnit j e b i := by
  classical
  unfold assigned
  rw [Function.extend_apply' _ _ _ i.property, dif_pos i.property]

theorem assigned_power (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ)
    (he : ∀ k, 0 < e k) (k : κ) :
    (assigned j e b he (j k) : ProductAlgebra j e b) ^ e k =
      algebraMap R (ProductAlgebra j e b) (b k : R) := by
  rw [assigned_selected, rootUnit_val, ← map_pow, coordinate_power,
    ← IsScalarTower.algebraMap_apply R (PowerAlgebra e b) (ProductAlgebra j e b)]

def forward (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (he : ∀ k, 0 < e k) :
    PartialPowerSmooth.PartialAlgebra j e b →ₐ[R] ProductAlgebra j e b :=
  PartialPowerSmooth.lift j e b (assigned j e b he) (assigned_power j e b he)

theorem forward_coordinate (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ)
    (he : ∀ k, 0 < e k) (i : ι) :
    forward j e b he (PartialPowerSmooth.coordinate j e b i) = assigned j e b he i :=
  PartialPowerSmooth.lift_coordinate _ _ _ _ _ _

def rootMap (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) :
    PowerAlgebra e b →ₐ[R] PartialPowerSmooth.PartialAlgebra j e b :=
  DiagonalPowerFibers.lift e b (fun k => PartialPowerSmooth.coordinate j e b (j k))
    (PartialPowerSmooth.coordinate_power j e b)

theorem rootMap_coordinate (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (k : κ) :
    rootMap j e b (coordinate e b k) = PartialPowerSmooth.coordinate j e b (j k) :=
  DiagonalPowerFibers.lift_coordinate _ _ _ _ _

def freeCharacter (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) :
    Multiplicative (FreeIndex j →₀ ℤ) →* PartialPowerSmooth.PartialAlgebra j e b :=
  (Units.coeHom _).comp (basisCharacter Finsupp.basisSingleOne
    (fun i : FreeIndex j => PartialPowerSmooth.coordinateUnit j e b i))

def backward (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) :
    ProductAlgebra j e b →ₐ[R] PartialPowerSmooth.PartialAlgebra j e b :=
  MonoidAlgebra.liftNCAlgHom (rootMap j e b) (freeCharacter j e b) (fun _ _ => Commute.all _ _)

theorem backward_coefficient (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ)
    (a : PowerAlgebra e b) :
    backward j e b (algebraMap (PowerAlgebra e b) (ProductAlgebra j e b) a) = rootMap j e b a := by
  change MonoidAlgebra.liftNC _ _ (Finsupp.single 1 a) = _
  rw [MonoidAlgebra.liftNC_single, map_one, mul_one]
  rfl

theorem backward_free (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (i : FreeIndex j) :
    backward j e b (freeUnit j e b i : ProductAlgebra j e b) =
      PartialPowerSmooth.coordinate j e b i := by
  change MonoidAlgebra.liftNC _ _ (Finsupp.single _ 1) = _
  rw [MonoidAlgebra.liftNC_single]
  change rootMap j e b 1 * freeCharacter j e b
    (Multiplicative.ofAdd (Finsupp.single i 1)) = _
  rw [map_one, one_mul]
  change (basisCharacter (Finsupp.basisSingleOne : Basis (FreeIndex j) ℤ (FreeIndex j →₀ ℤ))
    (fun i : FreeIndex j => PartialPowerSmooth.coordinateUnit j e b i)
    (Multiplicative.ofAdd (Finsupp.basisSingleOne i)) : PartialPowerSmooth.PartialAlgebra j e b) = _
  rw [basisCharacter_apply, PartialPowerSmooth.coordinateUnit_val]

theorem backward_assigned (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ)
    (he : ∀ k, 0 < e k) (i : ι) :
    backward j e b (assigned j e b he i : ProductAlgebra j e b) =
      PartialPowerSmooth.coordinate j e b i := by
  classical
  by_cases hi : i ∈ Set.range j
  · obtain ⟨k,rfl⟩ := hi
    rw [assigned_selected, rootUnit_val, backward_coefficient, rootMap_coordinate]
  · rw [show assigned j e b he i = freeUnit j e b ⟨i,hi⟩ from assigned_free j e b he ⟨i,hi⟩]
    exact backward_free j e b ⟨i,hi⟩

theorem backward_forward (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (he : ∀ k, 0 < e k) :
    (backward j e b).comp (forward j e b he) = AlgHom.id R _ := by
  apply PartialPowerSmooth.hom_ext j e b
  intro i
  change backward j e b (forward j e b he (PartialPowerSmooth.coordinate j e b i)) = _
  rw [forward_coordinate, backward_assigned]
  rfl

theorem forward_rootMap (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (he : ∀ k, 0 < e k) :
    (forward j e b he).comp (rootMap j e b) =
      IsScalarTower.toAlgHom R (PowerAlgebra e b) (ProductAlgebra j e b) := by
  apply DiagonalPowerFibers.hom_ext e b
  intro k
  change forward j e b he (rootMap j e b (coordinate e b k)) = _
  rw [rootMap_coordinate, forward_coordinate, assigned_selected, rootUnit_val]
  rfl

theorem forward_backward (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (he : ∀ k, 0 < e k) :
    (forward j e b he).comp (backward j e b) = AlgHom.id R _ := by
  apply AlgHom.coe_ringHom_injective
  apply MonoidAlgebra.ringHom_ext'
  · apply RingHom.ext
    intro a
    change forward j e b he (backward j e b (algebraMap (PowerAlgebra e b) _ a)) =
      algebraMap (PowerAlgebra e b) _ a
    rw [backward_coefficient]
    exact AlgHom.congr_fun (forward_rootMap j e b he) a
  · apply MonoidHom.eq_of_eqOn_dense
      (basis_generates (Finsupp.basisSingleOne : Basis (FreeIndex j) ℤ (FreeIndex j →₀ ℤ)))
    rintro _ ⟨i,rfl⟩
    change forward j e b he (backward j e b (freeUnit j e b i : ProductAlgebra j e b)) = _
    rw [backward_free, forward_coordinate, assigned_free]
    rfl

def productEquiv (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (he : ∀ k, 0 < e k) :
    PartialPowerSmooth.PartialAlgebra j e b ≃ₐ[R] ProductAlgebra j e b :=
  AlgEquiv.ofAlgHom (forward j e b he) (backward j e b)
    (forward_backward j e b he) (backward_forward j e b he)

#print axioms FreeIndex
#print axioms ProductAlgebra
#print axioms freeUnit
#print axioms rootUnit
#print axioms rootUnit_val
#print axioms assigned
#print axioms assigned_selected
#print axioms assigned_free
#print axioms assigned_power
#print axioms forward
#print axioms forward_coordinate
#print axioms rootMap
#print axioms rootMap_coordinate
#print axioms freeCharacter
#print axioms backward
#print axioms backward_coefficient
#print axioms backward_free
#print axioms backward_assigned
#print axioms backward_forward
#print axioms forward_rootMap
#print axioms forward_backward
#print axioms productEquiv
end Verification.PartialPowerProduct
