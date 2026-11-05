/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimitiveCharacters
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Group.Units.Hom

/-!
# Smith Characters

The actual change of character equations to Smith coordinates. Mathlib's
Smith normal form theorem supplies the two lattice bases. We prove that
changing the source basis does not change the character ideal, and that
the ambient basis change carries it to independent signed power equations.
The constants change by integral products, so remain units over any base.
This file does not assert the subsequent tensor-product presentation or
the finite etaleness of the whole diagonal fiber.
-/

noncomputable section
namespace Verification.SmithCharacters
open MonoidAlgebra
open Verification.PrimitiveCharacters

variable {R M P ι κ : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup P]

def latticeRelation (f : P →ₗ[ℤ] M) (c : Multiplicative P →* Rˣ)
    (p : P) : MonoidAlgebra R (Multiplicative M) :=
  of R (Multiplicative M) (Multiplicative.ofAdd (f p)) -
    algebraMap R _ (c (Multiplicative.ofAdd p) : R)

def fullIdeal (f : P →ₗ[ℤ] M) (c : Multiplicative P →* Rˣ) :
    Ideal (MonoidAlgebra R (Multiplicative M)) :=
  Ideal.span (Set.range (latticeRelation f c))

theorem all_relations_mem (f : P →ₗ[ℤ] M) (b : Basis κ ℤ P)
    (c : Multiplicative P →* Rˣ) (p : P) :
    latticeRelation f c p ∈ columnIdeal f b c := by
  let J := columnIdeal f b c
  let q := Ideal.Quotient.mk J
  let u : Multiplicative P →* (MonoidAlgebra R (Multiplicative M) ⧸ J) :=
    q.toMonoidHom.comp ((of R (Multiplicative M)).comp
      f.toAddMonoidHom.toMultiplicative)
  let v : Multiplicative P →* (MonoidAlgebra R (Multiplicative M) ⧸ J) :=
    (algebraMap R _).toMonoidHom.comp ((Units.coeHom R).comp c)
  have huv : u = v := by
    apply MonoidHom.eq_of_eqOn_dense (basis_generates b)
    rintro _ ⟨i, rfl⟩
    have hi : q (latticeRelation f c (b i)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
    rw [latticeRelation, map_sub] at hi
    exact sub_eq_zero.mp (show u (Multiplicative.ofAdd (b i)) -
      v (Multiplicative.ofAdd (b i)) = 0 from hi)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (latticeRelation f c p) = 0
  rw [latticeRelation, map_sub]
  change u (Multiplicative.ofAdd p) - v (Multiplicative.ofAdd p) = 0
  rw [huv, sub_self]

theorem columnIdeal_eq_fullIdeal (f : P →ₗ[ℤ] M) (b : Basis κ ℤ P)
    (c : Multiplicative P →* Rˣ) : columnIdeal f b c = fullIdeal f c := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span (Set.mem_range_self (b i))
  · apply Ideal.span_le.mpr
    rintro _ ⟨p, rfl⟩
    exact all_relations_mem f b c p

theorem columnIdeal_basis_independent (f : P →ₗ[ℤ] M)
    (b : Basis κ ℤ P) (b' : Basis ι ℤ P) (c : Multiplicative P →* Rˣ) :
    columnIdeal f b c = columnIdeal f b' c := by
  rw [columnIdeal_eq_fullIdeal, columnIdeal_eq_fullIdeal]

def smithSourceBasis (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n) : Basis (Fin n) ℤ P :=
  s.bN.map (LinearEquiv.ofInjective f hf).symm

theorem smithSourceBasis_image (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n) (i : Fin n) :
    f (smithSourceBasis f hf s i) = s.a i • s.bM (s.f i) := by
  change ((LinearEquiv.ofInjective f hf)
    ((LinearEquiv.ofInjective f hf).symm (s.bN i)) : M) = _
  rw [LinearEquiv.apply_symm_apply, s.snf]

def smithCoordinates {N : Submodule ℤ M} {n : ℕ}
    (s : Basis.SmithNormalForm N ι n) :
    Multiplicative M ≃* Multiplicative (ι →₀ ℤ) :=
  s.bM.repr.toAddEquiv.toMultiplicative

theorem smithCoordinates_source (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n) (i : Fin n) :
    smithCoordinates s (Multiplicative.ofAdd (f (smithSourceBasis f hf s i))) =
      Multiplicative.ofAdd (Finsupp.single (s.f i) (s.a i)) := by
  change s.bM.repr (f (smithSourceBasis f hf s i)) = Finsupp.single (s.f i) (s.a i)
  rw [smithSourceBasis_image, map_smul, s.bM.repr_self, Finsupp.smul_single]
  simp

def diagonalIdeal {n : ℕ} (j : Fin n ↪ ι) (a : Fin n → ℤ) (u : Fin n → Rˣ) :
    Ideal (MonoidAlgebra R (Multiplicative (ι →₀ ℤ))) :=
  Ideal.span (Set.range (fun i =>
    of R (Multiplicative (ι →₀ ℤ)) (Multiplicative.ofAdd (Finsupp.single (j i) (a i))) -
      algebraMap R _ (u i : R)))

def smithConstants (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n)
    (c : Multiplicative P →* Rˣ) (i : Fin n) : Rˣ :=
  c (Multiplicative.ofAdd (smithSourceBasis f hf s i))

theorem smith_ideal_map (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    (b : Basis κ ℤ P) {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n)
    (c : Multiplicative P →* Rˣ) :
    (columnIdeal f b c).map (domCongr R R (smithCoordinates s)).toRingHom =
      diagonalIdeal s.f s.a (smithConstants f hf s c) := by
  rw [columnIdeal_basis_independent f b (smithSourceBasis f hf s),
    columnIdeal, Ideal.map_span, ← Set.range_comp]
  unfold diagonalIdeal
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change (domCongr R R (smithCoordinates s))
    (of R (Multiplicative M) (Multiplicative.ofAdd (f (smithSourceBasis f hf s i))) -
      algebraMap R _ (c (Multiplicative.ofAdd (smithSourceBasis f hf s i)) : R)) = _
  rw [map_sub, AlgEquiv.commutes]
  have hm : (domCongr R R (smithCoordinates s))
      (of R (Multiplicative M) (Multiplicative.ofAdd (f (smithSourceBasis f hf s i)))) =
      of R (Multiplicative (ι →₀ ℤ))
        (Multiplicative.ofAdd (Finsupp.single (s.f i) (s.a i))) := by
    change (domCongr R R (smithCoordinates s)) (Finsupp.single _ 1) = Finsupp.single _ 1
    rw [domCongr_single, smithCoordinates_source f hf s]
  rw [hm]
  rfl

def smithFiberEquiv (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    (b : Basis κ ℤ P) {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n)
    (c : Multiplicative P →* Rˣ) :
    (MonoidAlgebra R (Multiplicative M) ⧸ columnIdeal f b c) ≃ₐ[R]
      (MonoidAlgebra R (Multiplicative (ι →₀ ℤ)) ⧸
        diagonalIdeal s.f s.a (smithConstants f hf s c)) :=
  Ideal.quotientEquivAlg _ _ (domCongr R R (smithCoordinates s))
    (smith_ideal_map f hf b s c).symm

theorem smith_coefficient_ne_zero {N : Submodule ℤ M} {n : ℕ}
    (s : Basis.SmithNormalForm N ι n) (i : Fin n) : s.a i ≠ 0 := by
  intro hi
  have hb : (s.bN i : M) = 0 := by rw [s.snf, hi, zero_smul]
  exact s.bN.ne_zero i (Subtype.ext hb)

theorem exists_smith_fiber [Finite ι] (bM : Basis ι ℤ M)
    (f : P →ₗ[ℤ] M) (hf : Function.Injective f) (bP : Basis κ ℤ P)
    (c : Multiplicative P →* Rˣ) :
    ∃ (n : ℕ) (j : Fin n ↪ ι) (a : Fin n → ℤ) (u : Fin n → Rˣ),
      (∀ i, a i ≠ 0) ∧
      Nonempty ((MonoidAlgebra R (Multiplicative M) ⧸ columnIdeal f bP c) ≃ₐ[R]
        (MonoidAlgebra R (Multiplicative (ι →₀ ℤ)) ⧸ diagonalIdeal j a u)) := by
  obtain ⟨n,s⟩ := (LinearMap.range f).smithNormalForm bM
  exact ⟨n, s.f, s.a, smithConstants f hf s c, smith_coefficient_ne_zero s,
    ⟨smithFiberEquiv f hf bP s c⟩⟩

def coordinateUnit (R ι : Type*) [CommRing R] (i : ι) :
    (MonoidAlgebra R (Multiplicative (ι →₀ ℤ)))ˣ :=
  (of R (Multiplicative (ι →₀ ℤ))).toHomUnits
    (Multiplicative.ofAdd (Finsupp.single i 1))

theorem monomial_eq_signed_power (i : ι) (a : ℤ) :
    of R (Multiplicative (ι →₀ ℤ)) (Multiplicative.ofAdd (Finsupp.single i a)) =
      ((coordinateUnit R ι i ^ a : (MonoidAlgebra R (Multiplicative (ι →₀ ℤ)))ˣ) :
        MonoidAlgebra R (Multiplicative (ι →₀ ℤ))) := by
  have hs : Finsupp.single i a = a • (Finsupp.single i 1 : ι →₀ ℤ) := by
    rw [Finsupp.smul_single]
    simp
  rw [hs, ofAdd_zsmul]
  exact congrArg Units.val
    (map_zpow (of R (Multiplicative (ι →₀ ℤ))).toHomUnits
      (Multiplicative.ofAdd (Finsupp.single i 1)) a)

theorem inverse_unit_relation_mem_iff {A : Type*} [CommRing A]
    (J : Ideal A) (x y : Aˣ) :
    ((↑(x⁻¹) : A) - ↑(y⁻¹) ∈ J) ↔ ((x : A) - (y : A) ∈ J) := by
  rw [← Ideal.Quotient.eq, ← Ideal.Quotient.eq]
  let q := Units.map (Ideal.Quotient.mk J).toMonoidHom
  change (↑(q (x⁻¹)) : A ⧸ J) = ↑(q (y⁻¹)) ↔
    (↑(q x) : A ⧸ J) = ↑(q y)
  rw [map_inv, map_inv]
  constructor
  · intro h
    exact congrArg Units.val (inv_injective (Units.ext h))
  · intro h
    exact congrArg Units.val (congrArg Inv.inv (Units.ext h))

def positiveConstant (a : ℤ) (u : Rˣ) : Rˣ := if a < 0 then u⁻¹ else u

def positiveIdeal {n : ℕ} (j : Fin n ↪ ι) (e : Fin n → ℕ) (u : Fin n → Rˣ) :
    Ideal (MonoidAlgebra R (Multiplicative (ι →₀ ℤ))) :=
  Ideal.span (Set.range (fun i =>
    (coordinateUnit R ι (j i) : MonoidAlgebra R (Multiplicative (ι →₀ ℤ))) ^ e i -
      algebraMap R _ (u i : R)))

theorem signed_relation_mem_iff (J : Ideal (MonoidAlgebra R (Multiplicative (ι →₀ ℤ))))
    (i : ι) (a : ℤ) (u : Rˣ) :
    (of R (Multiplicative (ι →₀ ℤ)) (Multiplicative.ofAdd (Finsupp.single i a)) -
      algebraMap R _ (u : R) ∈ J) ↔
    ((coordinateUnit R ι i : MonoidAlgebra R (Multiplicative (ι →₀ ℤ))) ^ a.natAbs -
      algebraMap R _ (positiveConstant a u : R) ∈ J) := by
  rw [monomial_eq_signed_power]
  cases a with
  | ofNat e => simp [positiveConstant, Int.not_lt.mpr (Int.natCast_nonneg e)]
  | negSucc e =>
    rw [zpow_negSucc]
    simpa [positiveConstant, Units.val_pow_eq_pow_val] using
      inverse_unit_relation_mem_iff J (coordinateUnit R ι i ^ (e+1))
        ((Units.map (algebraMap R _).toMonoidHom u)⁻¹)

theorem diagonalIdeal_eq_positiveIdeal {n : ℕ} (j : Fin n ↪ ι)
    (a : Fin n → ℤ) (u : Fin n → Rˣ) :
    diagonalIdeal j a u = positiveIdeal j (fun i => (a i).natAbs)
      (fun i => positiveConstant (a i) (u i)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (signed_relation_mem_iff _ (j i) (a i) (u i)).mpr
      (Ideal.subset_span (Set.mem_range_self i))
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (signed_relation_mem_iff _ (j i) (a i) (u i)).mp
      (Ideal.subset_span (Set.mem_range_self i))

theorem exists_positive_power_fiber [Finite ι] (bM : Basis ι ℤ M)
    (f : P →ₗ[ℤ] M) (hf : Function.Injective f) (bP : Basis κ ℤ P) (uP : κ → Rˣ) :
    ∃ (n : ℕ) (j : Fin n ↪ ι) (e : Fin n → ℕ) (u : Fin n → Rˣ),
      (∀ i, 0 < e i) ∧
      Nonempty ((MonoidAlgebra R (Multiplicative M) ⧸ prescribedIdeal f bP uP) ≃ₐ[R]
        (MonoidAlgebra R (Multiplicative (ι →₀ ℤ)) ⧸ positiveIdeal j e u)) := by
  rw [prescribedIdeal_eq]
  obtain ⟨n,j,a,u,ha,⟨E⟩⟩ := exists_smith_fiber bM f hf bP (basisCharacter bP uP)
  refine ⟨n,j,(fun i => (a i).natAbs),(fun i => positiveConstant (a i) (u i)),
    (fun i => Int.natAbs_pos.mpr (ha i)), ?_⟩
  exact ⟨E.trans (Ideal.quotientEquivAlgOfEq R (diagonalIdeal_eq_positiveIdeal j a u))⟩

#print axioms latticeRelation
#print axioms fullIdeal
#print axioms all_relations_mem
#print axioms columnIdeal_eq_fullIdeal
#print axioms columnIdeal_basis_independent
#print axioms smithSourceBasis
#print axioms smithSourceBasis_image
#print axioms smithCoordinates
#print axioms smithCoordinates_source
#print axioms diagonalIdeal
#print axioms smithConstants
#print axioms smith_ideal_map
#print axioms smithFiberEquiv
#print axioms smith_coefficient_ne_zero
#print axioms exists_smith_fiber
#print axioms coordinateUnit
#print axioms monomial_eq_signed_power
#print axioms inverse_unit_relation_mem_iff
#print axioms positiveConstant
#print axioms positiveIdeal
#print axioms signed_relation_mem_iff
#print axioms diagonalIdeal_eq_positiveIdeal
#print axioms exists_positive_power_fiber

end Verification.SmithCharacters
