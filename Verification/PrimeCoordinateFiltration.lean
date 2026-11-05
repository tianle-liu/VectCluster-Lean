/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeStratumIncidence
import Mathlib.Data.Finset.Card

/-!
# Prime Coordinate Filtration

The genuine Zariski filtration by the number of zero original coordinates.
Its stages are open subsets of the prime spectrum; the successive layers are
the disjoint coordinate-zero strata. Acyclicity is used only to prove that
the actual exchange ring has independent zero sets.
-/
noncomputable section
namespace Verification.PrimeCoordinateFiltration
open scoped BigOperators
variable {A V : Type*} [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A)

def zeroSet (p : PrimeSpectrum A) : Finset V := by
  classical
  exact Finset.univ.filter (fun i => x i ∈ p.asIdeal)

def openBy (I : Finset V) : TopologicalSpace.Opens (PrimeSpectrum A) :=
  PrimeSpectrum.basicOpen (∏ i ∈ Iᶜ, x i)

omit [DecidableEq V] in
theorem mem_zeroSet (p : PrimeSpectrum A) (i : V) : i ∈ zeroSet x p ↔ x i ∈ p.asIdeal := by
  simp only [zeroSet,Finset.mem_filter,Finset.mem_univ,true_and]

theorem mem_openBy (I : Finset V) (p : PrimeSpectrum A) :
    p ∈ openBy x I ↔ zeroSet x p ⊆ I := by
  change (∏ i ∈ Iᶜ, x i) ∉ p.asIdeal ↔ _
  rw [Ideal.IsPrime.prod_mem_iff]
  push_neg
  constructor
  · intro h i hi
    by_contra hn
    exact h i (Finset.mem_compl.mpr hn) ((mem_zeroSet x p i).mp hi)
  · intro h i hi hx
    exact Finset.mem_compl.mp hi (h ((mem_zeroSet x p i).mpr hx))

/-- Stage r consists of points with fewer than r zero coordinates. -/
def stage (r : ℕ) : TopologicalSpace.Opens (PrimeSpectrum A) :=
  ⨆ I : {I : Finset V // I.card < r}, openBy x I.val

theorem mem_stage (r : ℕ) (p : PrimeSpectrum A) :
    p ∈ stage x r ↔ (zeroSet x p).card < r := by
  rw [stage,TopologicalSpace.Opens.mem_iSup]
  constructor
  · rintro ⟨I,hI⟩
    exact (Finset.card_le_card ((mem_openBy x I.val p).mp hI)).trans_lt I.property
  · intro h
    exact ⟨⟨zeroSet x p,h⟩,(mem_openBy x _ p).mpr (Finset.Subset.refl _)⟩

theorem stage_mono : Monotone (stage x) := by
  intro r s hrs p hp
  exact (mem_stage x s p).mpr (((mem_stage x r p).mp hp).trans_le hrs)

theorem stage_zero : stage x 0 = ⊥ := by
  ext p
  change (p ∈ stage x 0) ↔ False
  rw [mem_stage]
  exact iff_false_intro (Nat.not_lt_zero _)

theorem stage_exhaustive : stage x (Fintype.card V + 1) = ⊤ := by
  ext p
  change (p ∈ stage x (Fintype.card V + 1)) ↔ True
  rw [mem_stage,iff_true]
  exact Nat.lt_succ_of_le (Finset.card_le_univ _)

theorem mem_layer (r : ℕ) (p : PrimeSpectrum A) :
    p ∈ (stage x (r+1) : Set (PrimeSpectrum A)) \ stage x r ↔ (zeroSet x p).card = r := by
  change ((p ∈ stage x (r+1)) ∧ ¬p ∈ stage x r) ↔ _
  rw [mem_stage,mem_stage]
  omega

omit [DecidableEq V] in
theorem stratum_zeroSet (I : Finset V) (p : PrimeSpectrum A) :
    p ∈ PrimeStratumIncidence.stratum x I ↔ zeroSet x p = I := by
  constructor
  · intro hp
    ext i
    exact (mem_zeroSet x p i).trans (hp i)
  · intro hp i
    rw [← mem_zeroSet x p i,hp]

theorem layer_strata (r : ℕ) :
    (stage x (r+1) : Set (PrimeSpectrum A)) \ stage x r =
      ⋃ I : {I : Finset V // I.card = r}, PrimeStratumIncidence.stratum x I.val := by
  ext p
  rw [mem_layer,Set.mem_iUnion]
  constructor
  · intro hp
    exact ⟨⟨zeroSet x p,hp⟩,(stratum_zeroSet x _ p).mpr rfl⟩
  · rintro ⟨I,hI⟩
    rw [(stratum_zeroSet x I.val p).mp hI,I.property]

omit [DecidableEq V] in
theorem strata_disjoint (I J : Finset V) (h : I ≠ J) :
    Disjoint (PrimeStratumIncidence.stratum x I) (PrimeStratumIncidence.stratum x J) := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  exact h (((stratum_zeroSet x I p).mp hp).symm.trans ((stratum_zeroSet x J p).mp hq))

section Actual
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover Verification.ExchangeGeometry Verification.ExchangeRing
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

def actualStage (r : ℕ) : TopologicalSpace.Opens (PrimeSpectrum (Global R κ n B)) :=
  stage (fun i => initial R κ n B (Sum.inl i)) r

theorem actual_zeroSet_independent
    (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
    (p : PrimeSpectrum (Global R κ n B)) :
    Independent (laterWeights κ n B) (zeroSet (fun i => initial R κ n B (Sum.inl i)) p) :=
  primeZeroSet_independent (laterWeights κ n B) _
    (adjacent_span_eq_top (earlierWeights κ n B) (laterWeights κ n B) _ _ _ _ hsupport
      (earlierCoefficient_unit R κ n B) (ordered_equations R κ n B hpos hneg)) p

end Actual
#print axioms zeroSet
#print axioms openBy
#print axioms mem_zeroSet
#print axioms mem_openBy
#print axioms stage
#print axioms mem_stage
#print axioms stage_mono
#print axioms stage_zero
#print axioms stage_exhaustive
#print axioms mem_layer
#print axioms stratum_zeroSet
#print axioms layer_strata
#print axioms strata_disjoint
#print axioms actualStage
#print axioms actual_zeroSet_independent
end Verification.PrimeCoordinateFiltration
