/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarInitialCoordinates
import Verification.ScalarGlobalUnitOrders

/-!
# Scalar Global Units

Global-unit classification for the actual scalar exchange ring. The sole
standard-theory input is a unit classification for a standalone Laurent
group algebra. The localization, its coordinate images, all boundary
orders, elimination of mutable exponents, and frozen-unit converse are
proved internally on the actual presentation.
-/
noncomputable section
namespace Verification.ScalarGlobalUnits
set_option maxHeartbeats 100000
open Verification.ScalarFrozenGlobal Verification.ScalarIndependentBasicOpen
open Verification.IndependentChartIndex
open Verification.FrozenAcyclicCover (earlierWeights laterWeights)
open Verification.ExchangeOpenCover
open scoped BigOperators
variable (R κ : Type) [CommRing R] [Fintype κ]

def laurentVariable (k : κ) : (OriginalTorus.Torus R κ)ˣ :=
  (MonoidAlgebra.of R (Multiplicative (κ →₀ ℤ))).toHomUnits
    (Multiplicative.ofAdd (Finsupp.single k 1))

#print axioms laurentVariable

omit [Fintype κ] in
theorem laurentVariable_val (k : κ) : (laurentVariable R κ k : OriginalTorus.Torus R κ) =
    OriginalTorus.torusCoordinate R κ k := rfl

#print axioms laurentVariable_val

/-- Explicit external standard Laurent-unit theorem, independent of any
exchange matrix, global ring, or boundary. -/
def LaurentUnitClassification : Prop :=
  ∀ u : (OriginalTorus.Torus R κ)ˣ, ∃ c : Rˣ, ∃ z : κ → ℤ,
    u = Units.map (algebraMap R (OriginalTorus.Torus R κ)).toMonoidHom c *
      ∏ k, laurentVariable R κ k ^ z k

#print axioms LaurentUnitClassification

variable (n : ℕ) (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)

def frozenUnit (k : κ) : (Global R κ n B a b)ˣ := (frozen_unit R κ n B a b k).unit

#print axioms frozenUnit

theorem frozenUnit_val (k : κ) : (frozenUnit R κ n B a b k : Global R κ n B a b) =
    initial R κ n B a b (Sum.inr k) := (frozen_unit R κ n B a b k).unit_spec

#print axioms frozenUnit_val

def coefficientUnit (c : Rˣ) (z : κ → ℤ) : (Global R κ n B a b)ˣ :=
  Units.map (algebraMap R (Global R κ n B a b)).toMonoidHom c *
    ∏ k, frozenUnit R κ n B a b k ^ z k

#print axioms coefficientUnit

theorem coefficient_isUnit (c : Rˣ) (z : κ → ℤ) :
    IsUnit (coefficientUnit R κ n B a b c z : Global R κ n B a b) :=
  (coefficientUnit R κ n B a b c z).isUnit

#print axioms coefficient_isUnit

theorem embedding_frozen (k : κ) :
    Units.map (ScalarInitialCoordinates.coordinateTorusEquiv R κ n B a b).toRingHom.toMonoidHom
      (Units.map (algebraMap (Global R κ n B a b) (BasicOpen R κ n ∅ B a b)).toMonoidHom
        (frozenUnit R κ n B a b k)) =
      laurentVariable R (Other n ∅ ⊕ κ) (Sum.inr k) := by
  apply Units.ext
  change ScalarInitialCoordinates.coordinateTorusEquiv R κ n B a b
    (algebraMap (Global R κ n B a b) (BasicOpen R κ n ∅ B a b)
      (frozenUnit R κ n B a b k)) =
        OriginalTorus.torusCoordinate R (Other n ∅ ⊕ κ) (Sum.inr k)
  rw [frozenUnit_val]
  exact ScalarInitialCoordinates.coordinateTorusEquiv_original R κ n B a b (Sum.inr k)

#print axioms embedding_frozen

theorem torus_mutable (i : Fin n) :
    Units.map (ScalarInitialCoordinates.coordinateTorusEquiv R κ n B a b).toRingHom.toMonoidHom
      (ScalarInitialUnits.localizedUnit R κ n B a b i) =
      laurentVariable R (Other n ∅ ⊕ κ) (Sum.inl ⟨i, Finset.not_mem_empty i⟩) := by
  apply Units.ext
  change ScalarInitialCoordinates.coordinateTorusEquiv R κ n B a b
    (ScalarInitialUnits.localizedUnit R κ n B a b i) =
      OriginalTorus.torusCoordinate R (Other n ∅ ⊕ κ) (Sum.inl ⟨i, Finset.not_mem_empty i⟩)
  rw [ScalarInitialUnits.localizedUnit_val]
  exact ScalarInitialCoordinates.coordinateTorusEquiv_original R κ n B a b
    (Sum.inl ⟨i, Finset.not_mem_empty i⟩)

#print axioms torus_mutable

theorem embedding_ground (c : Rˣ) :
    Units.map (ScalarInitialCoordinates.coordinateTorusEquiv R κ n B a b).toRingHom.toMonoidHom
      (Units.map (algebraMap (Global R κ n B a b) (BasicOpen R κ n ∅ B a b)).toMonoidHom
        (Units.map (algebraMap R (Global R κ n B a b)).toMonoidHom c)) =
      Units.map (algebraMap R (OriginalTorus.Torus R (Other n ∅ ⊕ κ))).toMonoidHom c := by
  apply Units.ext
  change ScalarInitialCoordinates.coordinateTorusEquiv R κ n B a b
    (algebraMap (Global R κ n B a b) (BasicOpen R κ n ∅ B a b)
      (algebraMap R (Global R κ n B a b) (c : R))) = _
  rw [← IsScalarTower.algebraMap_apply]
  exact (ScalarInitialCoordinates.coordinateTorusEquiv R κ n B a b).commutes (c : R)

#print axioms embedding_ground

def otherEmptyEquiv : Other n ∅ ≃ Fin n where
  toFun := Subtype.val
  invFun i := ⟨i, Finset.not_mem_empty i⟩
  left_inv _ := rfl
  right_inv _ := rfl

#print axioms otherEmptyEquiv

theorem initial_expansion
    (hLaurent : LaurentUnitClassification R (Other n ∅ ⊕ κ)) (u : (Global R κ n B a b)ˣ) :
    ∃ c : Rˣ, ∃ f : κ → ℤ, ∃ z : Fin n → ℤ,
      Units.map (algebraMap (Global R κ n B a b) (BasicOpen R κ n ∅ B a b)).toMonoidHom u =
        Units.map (algebraMap (Global R κ n B a b) (BasicOpen R κ n ∅ B a b)).toMonoidHom
          (coefficientUnit R κ n B a b c f) *
            ∏ i, ScalarInitialUnits.localizedUnit R κ n B a b i ^ z i := by
  obtain ⟨c,z,hz⟩ := hLaurent (Units.map
    (ScalarInitialCoordinates.coordinateTorusEquiv R κ n B a b).toRingHom.toMonoidHom
      (Units.map (algebraMap (Global R κ n B a b) (BasicOpen R κ n ∅ B a b)).toMonoidHom u))
  refine ⟨c, (fun k => z (Sum.inr k)),
    (fun i => z (Sum.inl ⟨i, Finset.not_mem_empty i⟩)), ?_⟩
  apply Units.map_injective
    (f := (ScalarInitialCoordinates.coordinateTorusEquiv R κ n B a b).toRingHom.toMonoidHom)
    (ScalarInitialCoordinates.coordinateTorusEquiv R κ n B a b).injective
  rw [hz, Fintype.prod_sum_type]
  simp only [coefficientUnit, map_mul, map_prod, map_zpow,
    embedding_ground, embedding_frozen, torus_mutable]
  have hp := Fintype.prod_equiv (otherEmptyEquiv n)
    (fun i : Other n ∅ => laurentVariable R (Other n ∅ ⊕ κ) (Sum.inl i) ^ z (Sum.inl i))
    (fun i : Fin n => laurentVariable R (Other n ∅ ⊕ κ)
      (Sum.inl ⟨i, Finset.not_mem_empty i⟩) ^ z (Sum.inl ⟨i, Finset.not_mem_empty i⟩))
    (fun _ => rfl)
  rw [hp]
  ac_rfl

#print axioms initial_expansion

variable [IsDomain R] [IsNoetherianRing R]
variable (hpos : ∀ r i : Fin n, ¬ r < i → (B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ r i : Fin n, ¬ i < r → (-B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hall : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
  AnticliqueSubcolumns.AS (fun q j => B q (Sum.inl j)) I)
include hpos hneg hsupport hall

/-- The global target classification is derived, not an external assumption. -/
theorem global_units
    (hLaurent : LaurentUnitClassification R (Other n ∅ ⊕ κ)) (u : (Global R κ n B a b)ˣ) :
    ∃ c : Rˣ, ∃ f : κ → ℤ, u = coefficientUnit R κ n B a b c f := by
  obtain ⟨c,f,z,h⟩ := initial_expansion R κ n B a b hLaurent u
  exact ⟨c,f,ScalarGlobalUnitOrders.unit_eq_coefficient R κ n B a b
    hpos hneg hsupport hall u (coefficientUnit R κ n B a b c f) z h⟩

#print axioms global_units

theorem isUnit_iff
    (hLaurent : LaurentUnitClassification R (Other n ∅ ⊕ κ)) (q : Global R κ n B a b) :
    IsUnit q ↔ ∃ c : Rˣ, ∃ f : κ → ℤ, q = (coefficientUnit R κ n B a b c f : Global R κ n B a b) := by
  constructor
  · rintro ⟨u,rfl⟩
    obtain ⟨c,f,h⟩ := global_units R κ n B a b hpos hneg hsupport hall hLaurent u
    exact ⟨c,f,congrArg Units.val h⟩
  · rintro ⟨c,f,rfl⟩
    exact coefficient_isUnit R κ n B a b c f

#print axioms isUnit_iff

end Verification.ScalarGlobalUnits
