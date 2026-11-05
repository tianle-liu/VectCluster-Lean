/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.EvenDifferential
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Even Admissible

Homogeneous degree and forbidden-coordinate preservation for the actual
exterior faces in `EvenDifferential`. The manuscript's weight convention is
`|I| + |A_x| + |F| = s`. Forbidden symbols are detected by their coordinate
contractions; these kernels and homogeneous exterior powers are actual
submodules, not Boolean stand-ins for the desired preservation theorem.
-/

namespace Verification.EvenAdmissible

open Verification.EvenDifferential

section ExteriorDegree

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem generator_mul_degree (v : M) (n : ℕ) (x : ExteriorAlgebra R M)
    (hx : x ∈ ExteriorAlgebra.exteriorPower R n M) :
    ExteriorAlgebra.ι R v * x ∈ ExteriorAlgebra.exteriorPower R (n + 1) M := by
  have hv : ExteriorAlgebra.ι R v ∈ LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) :=
    LinearMap.mem_range_self _ _
  have h := Submodule.mul_mem_mul hv hx
  simpa only [ExteriorAlgebra.exteriorPower, pow_succ'] using h

theorem contract_generator_degree (d : Module.Dual R M) (n : ℕ)
    (v : Fin (n + 1) → M) :
    contract d (ExteriorAlgebra.ιMulti R (n + 1) v) ∈ ExteriorAlgebra.exteriorPower R n M := by
  induction n with
  | zero =>
      simp only [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
        contract, CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_one,
        mul_zero, sub_zero]
      apply Submodule.smul_mem
      simp [ExteriorAlgebra.exteriorPower]
  | succ n ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      simp only [contract, CliffordAlgebra.contractLeft_ι_mul]
      apply Submodule.sub_mem
      · exact Submodule.smul_mem _ _ (ExteriorAlgebra.ιMulti_range R _ (Set.mem_range_self _))
      · exact generator_mul_degree (v 0) n _ (ih (Matrix.vecTail v))

theorem contract_degree (d : Module.Dual R M) (n : ℕ) (x : ExteriorAlgebra R M)
    (hx : x ∈ ExteriorAlgebra.exteriorPower R (n + 1) M) :
    contract d x ∈ ExteriorAlgebra.exteriorPower R n M := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      exact contract_generator_degree d n v
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

theorem contract_degree_zero (d : Module.Dual R M) (x : ExteriorAlgebra R M)
    (hx : x ∈ ExteriorAlgebra.exteriorPower R 0 M) : contract d x = 0 := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      simp [ExteriorAlgebra.ιMulti_zero_apply, contract]
  | zero => simp
  | add x y hx hy ihx ihy => simp [map_add, ihx, ihy]
  | smul a x hx ih => simp [map_smul, ih]

theorem exterior_map_degree (T : M →ₗ[R] M) (n : ℕ) (x : ExteriorAlgebra R M)
    (hx : x ∈ ExteriorAlgebra.exteriorPower R n M) :
    ExteriorAlgebra.map T x ∈ ExteriorAlgebra.exteriorPower R n M := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      rw [ExteriorAlgebra.map_apply_ιMulti]
      exact ExteriorAlgebra.ιMulti_range R n (Set.mem_range_self _)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

/-- Naturality without a preservation assumption on the contraction functional. -/
theorem contract_map_general (d : Module.Dual R M) (T : M →ₗ[R] M)
    (x : ExteriorAlgebra R M) :
    contract d (ExteriorAlgebra.map T x) = ExteriorAlgebra.map T (contract (d.comp T) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [contract, CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
      change contract d (ExteriorAlgebra.map T (ExteriorAlgebra.ι R v * x)) = _
      rw [map_mul, ExteriorAlgebra.map_apply_ι]
      simp only [contract, CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul,
        map_mul, ExteriorAlgebra.map_apply_ι, LinearMap.comp_apply]
      rw [hx]

def rankOneErase (d : Module.Dual R M) (e : M) : M →ₗ[R] M where
  toFun v := v - d v • e
  map_add' v w := by simp [add_smul]; abel
  map_smul' a v := by simp [smul_sub, smul_smul]

/-- Deleting one exterior coordinate is the explicit contraction projection. -/
theorem rankOneErase_formula (d : Module.Dual R M) (e : M) (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.map (rankOneErase d e) x = x - ExteriorAlgebra.ι R e * contract d x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [contract, CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]; abel
  | ι_mul x v hx =>
      change ExteriorAlgebra.map (rankOneErase d e) (ExteriorAlgebra.ι R v * x) = _
      rw [map_mul, ExteriorAlgebra.map_apply_ι, hx]
      simp only [rankOneErase, LinearMap.coe_mk, AddHom.coe_mk, map_sub, map_smul,
        contract, CliffordAlgebra.contractLeft_ι_mul]
      have hswap : ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R e =
          -(ExteriorAlgebra.ι R e * ExteriorAlgebra.ι R v) :=
        eq_neg_iff_add_eq_zero.mpr (ExteriorAlgebra.ι_add_mul_swap v e)
      simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, ← mul_assoc]
      rw [ExteriorAlgebra.ι_sq_zero, zero_mul, smul_zero, hswap, neg_mul]
      abel

end ExteriorDegree

section CoordinateMasks

variable {R α : Type*} [CommRing R] [DecidableEq α]

def coordinateMask (S : Finset α) : (α → R) →ₗ[R] (α → R) where
  toFun v a := if a ∈ S then 0 else v a
  map_add' v w := by funext a; by_cases ha : a ∈ S <;> simp [ha]
  map_smul' r v := by funext a; by_cases ha : a ∈ S <;> simp [ha]

theorem coordinateMask_empty : coordinateMask (R := R) (∅ : Finset α) = LinearMap.id := by
  ext v a
  simp [coordinateMask]

theorem coordinateMask_insert (S : Finset α) (a : α) :
    coordinateMask (R := R) (insert a S) =
      (rankOneErase (LinearMap.proj a) (Pi.single a (1 : R))).comp (coordinateMask S) := by
  ext v z
  by_cases hz : z = a
  · subst z; by_cases ha : a ∈ S <;> simp [coordinateMask, rankOneErase, ha]
  · by_cases ha : a ∈ S <;> simp [coordinateMask, rankOneErase, Pi.single_apply, hz, Ne.symm hz, ha]

theorem coordinateMask_dual (S : Finset α) (a : α) (ha : a ∈ S) :
    (LinearMap.proj a).comp (coordinateMask (R := R) S) = 0 := by
  ext v
  simp [coordinateMask, ha]

theorem coordinateMask_single (S : Finset α) (a : α) (ha : a ∉ S) :
    coordinateMask (R := R) S (Pi.single a 1) = Pi.single a 1 := by
  ext z
  by_cases hz : z = a
  · subst z; simp [coordinateMask, ha]
  · simp [coordinateMask, Pi.single_apply, hz, Ne.symm hz]

theorem contract_coordinateMask (S : Finset α) (a : α) (ha : a ∈ S)
    (x : ExteriorAlgebra R (α → R)) :
    contract (LinearMap.proj a) (ExteriorAlgebra.map (coordinateMask S) x) = 0 := by
  rw [contract_map_general, coordinateMask_dual S a ha]
  simp [contract]

theorem coordinateMask_fixed (S : Finset α) (x : ExteriorAlgebra R (α → R))
    (hx : ∀ a ∈ S, contract (LinearMap.proj a) x = 0) :
    ExteriorAlgebra.map (coordinateMask S) x = x := by
  revert x
  induction S using Finset.induction_on with
  | empty => intro x _; rw [coordinateMask_empty, ExteriorAlgebra.map_id]; rfl
  | @insert a S ha ih =>
      intro x hx
      rw [coordinateMask_insert, ← ExteriorAlgebra.map_comp_map]
      change ExteriorAlgebra.map (rankOneErase (LinearMap.proj a) (Pi.single a (1 : R)))
        (ExteriorAlgebra.map (coordinateMask S) x) = x
      rw [ih x (fun z hz => hx z (Finset.mem_insert_of_mem hz)), rankOneErase_formula,
        hx a (Finset.mem_insert_self a S), mul_zero, sub_zero]

end CoordinateMasks

section Coordinates

variable {R ι κ : Type*} [CommRing R] [DecidableEq ι] [DecidableEq κ]

def frozenDual (a : κ) : Module.Dual R (Coordinates R ι κ) := LinearMap.proj (Sum.inr a)

theorem frozen_dual_substitution (H : R) (b : ι → ι → R) (c : ι → κ) (i : ι) :
    (frozenDual (c i)).comp (substitution H b c i) = 0 := by
  ext v
  simp [frozenDual, substitution, replacementVector, frozenVector]

theorem replaced_frozen_absent (H : R) (b : ι → ι → R) (c : ι → κ) (i : ι)
    (x : Exterior R ι κ) :
    contract (frozenDual (c i)) (ExteriorAlgebra.map (substitution H b c i) x) = 0 := by
  rw [contract_map_general, frozen_dual_substitution]
  simp [contract]

/-- Vanishing coordinate contractions encode absence of the forbidden exterior symbols. -/
def permittedForms (c : ι → κ) (I : Finset ι) : Submodule R (Exterior R ι κ) where
  carrier := {x | (∀ j ∈ I, contract (mutableDual j) x = 0) ∧
    (∀ a ∈ I.image c, contract (frozenDual a) x = 0)}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    constructor
    · intro j hj; simp only [map_add, hx.1 j hj, hy.1 j hj, add_zero]
    · intro a ha; simp only [map_add, hx.2 a ha, hy.2 a ha, add_zero]
  smul_mem' := by
    intro r x hx
    constructor
    · intro j hj; simp only [map_smul, hx.1 j hj, smul_zero]
    · intro a ha; simp only [map_smul, hx.2 a ha, smul_zero]

def forbiddenCoordinates (c : ι → κ) (I : Finset ι) : Finset (Sum ι κ) :=
  I.image Sum.inl ∪ (I.image c).image Sum.inr

theorem permittedForms_coordinates (c : ι → κ) (I : Finset ι) (x : Exterior R ι κ) :
    x ∈ permittedForms c I ↔
      ∀ z ∈ forbiddenCoordinates c I, contract (LinearMap.proj z) x = 0 := by
  constructor
  · intro hx z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      exact hx.1 j hj
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      exact hx.2 a ha
  · intro hx
    constructor
    · intro j hj; exact hx (Sum.inl j) (by simp [forbiddenCoordinates, hj])
    · intro a ha
      exact hx (Sum.inr a) (Finset.mem_union_right _ (Finset.mem_image_of_mem Sum.inr ha))

/-- Kernel-defined permitted forms are exactly the forms fixed by deleting forbidden symbols. -/
theorem permittedForms_iff_mask (c : ι → κ) (I : Finset ι) (x : Exterior R ι κ) :
    x ∈ permittedForms c I ↔
      ExteriorAlgebra.map (coordinateMask (forbiddenCoordinates c I)) x = x := by
  rw [permittedForms_coordinates]
  constructor
  · exact coordinateMask_fixed _ x
  · intro hx z hz
    rw [← hx]
    exact contract_coordinateMask _ z hz x

theorem exteriorFace_permitted (H : R) (b : ι → ι → R) (c : ι → κ)
    (I : Finset ι) (i : ι) (hB : ∀ j ∈ insert i I, b j i = 0)
    (x : Exterior R ι κ) (hx : x ∈ permittedForms c I) :
    exteriorFace H b c i x ∈ permittedForms c (insert i I) := by
  constructor
  · intro j hj
    change contract (mutableDual j) (ExteriorAlgebra.map (substitution H b c i)
      (contract (mutableDual i) x)) = 0
    rw [contract_map _ _ (other_dual_preserved H b c j i (hB j hj))]
    by_cases hji : j = i
    · subst j
      rw [show contract (mutableDual (R := R) (κ := κ) i) (contract (mutableDual i) x) = 0 from
        CliffordAlgebra.contractLeft_contractLeft _ x]
      simp
    · have hjI : j ∈ I := (Finset.mem_insert.mp hj).resolve_left hji
      rw [show contract (mutableDual (R := R) (κ := κ) j) (contract (mutableDual i) x) =
          -(contract (mutableDual i) (contract (mutableDual j) x)) from
            CliffordAlgebra.contractLeft_comm _ _ x]
      rw [hx.1 j hjI]
      simp
  · intro a ha
    by_cases hai : a = c i
    · subst a
      exact replaced_frozen_absent H b c i _
    · have haI : a ∈ I.image c := by simpa [Finset.image_insert, hai] using ha
      have hd (v : Coordinates R ι κ) :
          frozenDual a (substitution H b c i v) = frozenDual (R := R) (ι := ι) a v :=
        substitution_frozen_coordinate H b c i a hai v
      change contract (frozenDual a) (ExteriorAlgebra.map (substitution H b c i)
        (contract (mutableDual i) x)) = 0
      rw [contract_map _ _ hd]
      rw [show contract (frozenDual (R := R) (ι := ι) a) (contract (mutableDual i) x) =
          -(contract (mutableDual i) (contract (frozenDual a) x)) from
            CliffordAlgebra.contractLeft_comm _ _ x]
      rw [hx.2 a haI]
      simp

def admissibleDegree (c : ι → κ) (I : Finset ι) (n : ℕ) : Submodule R (Exterior R ι κ) :=
  ExteriorAlgebra.exteriorPower R n (Coordinates R ι κ) ⊓ permittedForms c I

/-- The admissible homogeneous submodule is precisely the image of the deletion projection. -/
theorem admissibleDegree_eq_map (c : ι → κ) (I : Finset ι) (n : ℕ) :
    admissibleDegree (R := R) c I n =
      (ExteriorAlgebra.exteriorPower R n (Coordinates R ι κ)).map
        (ExteriorAlgebra.map (coordinateMask (forbiddenCoordinates c I))).toLinearMap := by
  ext x
  constructor
  · intro hx
    exact ⟨x, hx.1, (permittedForms_iff_mask c I x).mp hx.2⟩
  · rintro ⟨y, hy, rfl⟩
    constructor
    · exact exterior_map_degree _ n y hy
    · apply (permittedForms_coordinates c I _).mpr
      intro z hz
      exact contract_coordinateMask _ z hz y

theorem exteriorFace_admissible (H : R) (b : ι → ι → R) (c : ι → κ)
    (I : Finset ι) (i : ι) (hB : ∀ j ∈ insert i I, b j i = 0) (n : ℕ)
    (x : Exterior R ι κ) (hx : x ∈ admissibleDegree c I (n + 1)) :
    exteriorFace H b c i x ∈ admissibleDegree c (insert i I) n := by
  constructor
  · exact exterior_map_degree _ n _ (contract_degree _ n x hx.1)
  · exact exteriorFace_permitted H b c I i hB x hx.2

theorem exteriorFace_degree_zero (H : R) (b : ι → ι → R) (c : ι → κ) (x : Exterior R ι κ)
    (hx : x ∈ ExteriorAlgebra.exteriorPower R 0 (Coordinates R ι κ)) (i : ι) :
    exteriorFace H b c i x = 0 := by
  change ExteriorAlgebra.map (substitution H b c i) (contract (mutableDual i) x) = 0
  rw [contract_degree_zero _ _ hx, map_zero]

/-- Total weight is stratum codimension plus exterior degree, exactly as in the paper. -/
def fixedWeight (c : ι → κ) (I : Finset ι) (s : ℕ) : Submodule R (Exterior R ι κ) :=
  if I.card ≤ s then admissibleDegree c I (s - I.card) else ⊥

/-- Every homogeneous product of allowed coordinate symbols has the stated total weight. -/
theorem allowed_monomial_fixedWeight (c : ι → κ) (I : Finset ι) (n s : ℕ)
    (hs : I.card + n = s) (v : Fin n → Sum ι κ)
    (hv : ∀ k, v k ∉ forbiddenCoordinates c I) :
    ExteriorAlgebra.ιMulti R n (fun k => Pi.single (v k) (1 : R)) ∈ fixedWeight c I s := by
  have hbound : I.card ≤ s := by omega
  have hdegree : s - I.card = n := by omega
  simp only [fixedWeight, if_pos hbound, hdegree]
  constructor
  · exact ExteriorAlgebra.ιMulti_range R n (Set.mem_range_self _)
  · apply (permittedForms_iff_mask c I _).mpr
    rw [ExteriorAlgebra.map_apply_ιMulti]
    congr 1
    funext k
    exact coordinateMask_single _ _ (hv k)

/-- In particular the paper's `(I,A_x,F)` generators satisfy exactly its stated weight condition. -/
theorem basisTriple_fixedWeight (c : ι → κ) (I A : Finset ι) (F : Finset κ) (s : ℕ)
    (hA : Disjoint I A) (hF : Disjoint (I.image c) F)
    (hs : I.card + A.card + F.card = s)
    (v : Fin (A.card + F.card) → Sum ι κ)
    (hv : ∀ k, v k ∈ A.image Sum.inl ∪ F.image Sum.inr) :
    ExteriorAlgebra.ιMulti R (A.card + F.card) (fun k => Pi.single (v k) (1 : R)) ∈
      fixedWeight c I s := by
  apply allowed_monomial_fixedWeight c I _ s (by omega) v
  intro k
  rcases Finset.mem_union.mp (hv k) with hk | hk
  · obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hk
    rw [← he]
    have hnot : j ∉ I := fun hI => Finset.disjoint_left.mp hA hI hj
    simpa [forbiddenCoordinates] using hnot
  · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hk
    rw [← he]
    have hnot : a ∉ I.image c := fun hI => Finset.disjoint_left.mp hF hI ha
    simpa [forbiddenCoordinates] using hnot

theorem exteriorFace_fixedWeight (H : R) (b : ι → ι → R) (c : ι → κ)
    (I : Finset ι) (i : ι) (hi : i ∉ I) (hB : ∀ j ∈ insert i I, b j i = 0)
    (s : ℕ) (x : Exterior R ι κ) (hx : x ∈ fixedWeight c I s) :
    exteriorFace H b c i x ∈ fixedWeight c (insert i I) s := by
  by_cases hp : I.card ≤ s
  · simp only [fixedWeight, if_pos hp] at hx
    by_cases heq : s = I.card
    · have hx0 : x ∈ ExteriorAlgebra.exteriorPower R 0 (Coordinates R ι κ) := by simpa [heq] using hx.1
      rw [exteriorFace_degree_zero H b c x hx0 i]
      exact Submodule.zero_mem _
    · have hcard : (insert i I).card = I.card + 1 := Finset.card_insert_of_not_mem hi
      have hnext : (insert i I).card ≤ s := by omega
      have hnext' : I.card + 1 ≤ s := by omega
      have hn : s - I.card = (s - (I.card + 1)) + 1 := by omega
      simp only [fixedWeight, hcard, if_pos hnext']
      exact exteriorFace_admissible H b c I i hB _ x (by simpa only [hn] using hx)
  · have hx0 : x = 0 := by simpa only [fixedWeight, if_neg hp, Submodule.mem_bot] using hx
    rw [hx0, map_zero]
    exact Submodule.zero_mem _

/-- Actual cochains whose component on each stratum has the prescribed total weight. -/
def fixedWeightCochains (b : ι → ι → R) (c : ι → κ) (s : ℕ) :
    Submodule R ({I : Finset ι // Compatible b c I} → Exterior R ι κ) where
  carrier := {f | ∀ I, f I ∈ fixedWeight c I.val s}
  zero_mem' := by intro I; exact Submodule.zero_mem _
  add_mem' := by intro f g hf hg I; exact Submodule.add_mem _ (hf I) (hg I)
  smul_mem' := by intro a f hf I; exact Submodule.smul_mem _ a (hf I)

theorem compatibleDifferential_fixedWeight (H : R) (b : ι → ι → R) (c : ι → κ)
    (hdiag : ∀ i, b i i = 0) (s : ℕ)
    (f : fixedWeightCochains b c s) :
    compatibleDifferential H b c f.val ∈ fixedWeightCochains b c s := by
  intro J
  apply Submodule.sum_mem
  intro i hi
  have hI : Compatible b c (J.val.erase i) :=
    compatible_subset b c _ _ (Finset.erase_subset i J.val) J.property
  have hB : ∀ j ∈ insert i (J.val.erase i), b j i = 0 := by
    rw [Finset.insert_erase hi]
    exact compatible_column_zero b c J.val J.property i hi (hdiag i)
  have hp := exteriorFace_fixedWeight H b c (J.val.erase i) i (Finset.not_mem_erase i J.val)
    hB s (f.val ⟨J.val.erase i, hI⟩) (f.property ⟨J.val.erase i, hI⟩)
  simpa only [compatibleExtend, dif_pos hI, Finset.insert_erase hi] using hp

/-- The existing compatible-set differential, packaged as a linear map. -/
noncomputable def compatibleDifferentialLinear (H : R) (b : ι → ι → R) (c : ι → κ) :
    ({I : Finset ι // Compatible b c I} → Exterior R ι κ) →ₗ[R]
      ({I : Finset ι // Compatible b c I} → Exterior R ι κ) where
  toFun := compatibleDifferential H b c
  map_add' f g := by
    funext J
    simp only [compatibleDifferential, exteriorDifferential, Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : Compatible b c (J.val.erase i) <;> simp [compatibleExtend, h, map_add]
  map_smul' a f := by
    funext J
    simp only [compatibleDifferential, exteriorDifferential, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : Compatible b c (J.val.erase i) <;> simp [compatibleExtend, h, map_smul]

/-- The finite-weight admissible exterior differential is an actual linear endomorphism. -/
noncomputable def fixedWeightDifferential (H : R) (b : ι → ι → R) (c : ι → κ)
    (hdiag : ∀ i, b i i = 0) (s : ℕ) :
    fixedWeightCochains b c s →ₗ[R] fixedWeightCochains b c s where
  toFun f := ⟨compatibleDifferential H b c f.val, compatibleDifferential_fixedWeight H b c hdiag s f⟩
  map_add' f g := by apply Subtype.ext; exact (compatibleDifferentialLinear H b c).map_add f.val g.val
  map_smul' a f := by apply Subtype.ext; exact (compatibleDifferentialLinear H b c).map_smul a f.val

theorem fixedWeightDifferential_squared (H : R) (b : ι → ι → R) (c : ι → κ)
    (hdiag : ∀ i, b i i = 0) (s : ℕ) :
    (fixedWeightDifferential H b c hdiag s).comp (fixedWeightDifferential H b c hdiag s) = 0 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext J
  exact compatibleDifferential_squared H b c f.val J

end Coordinates

#print axioms generator_mul_degree
#print axioms contract_generator_degree
#print axioms contract_degree
#print axioms contract_degree_zero
#print axioms exterior_map_degree
#print axioms contract_map_general
#print axioms rankOneErase_formula
#print axioms coordinateMask_empty
#print axioms coordinateMask_insert
#print axioms coordinateMask_dual
#print axioms coordinateMask_single
#print axioms contract_coordinateMask
#print axioms coordinateMask_fixed
#print axioms frozen_dual_substitution
#print axioms replaced_frozen_absent
#print axioms permittedForms_coordinates
#print axioms permittedForms_iff_mask
#print axioms exteriorFace_permitted
#print axioms exteriorFace_admissible
#print axioms admissibleDegree_eq_map
#print axioms exteriorFace_degree_zero
#print axioms exteriorFace_fixedWeight
#print axioms allowed_monomial_fixedWeight
#print axioms basisTriple_fixedWeight
#print axioms compatibleDifferential_fixedWeight
#print axioms compatibleDifferentialLinear
#print axioms fixedWeightDifferential
#print axioms fixedWeightDifferential_squared

end Verification.EvenAdmissible

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.EvenAdmissible.admissibleDegree
#print axioms Verification.EvenAdmissible.coordinateMask
#print axioms Verification.EvenAdmissible.fixedWeight
#print axioms Verification.EvenAdmissible.fixedWeightCochains
#print axioms Verification.EvenAdmissible.forbiddenCoordinates
#print axioms Verification.EvenAdmissible.frozenDual
#print axioms Verification.EvenAdmissible.permittedForms
#print axioms Verification.EvenAdmissible.rankOneErase
