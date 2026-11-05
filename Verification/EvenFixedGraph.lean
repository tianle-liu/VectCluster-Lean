/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.EvenAdmissible

/-!
# Even Fixed Graph

The stratum index is fixed before changing coefficient rings. Compatibility over a
coefficient ring is only an algebraic sufficient condition, never a definition of
the graph after reduction modulo a prime. The final specialization uses the integer
support of the original exchange matrix and its integer half entries.
-/

namespace Verification.EvenFixedGraph

open Verification.EvenDifferential Verification.EvenAdmissible

variable {R ι κ : Type*} [CommRing R] [DecidableEq ι] [DecidableEq κ]

def DownClosed (F : Finset ι → Prop) : Prop :=
  ∀ I J, I ⊆ J → F J → F I

noncomputable def familyExtend (F : Finset ι → Prop)
    (f : {I : Finset ι // F I} → Exterior R ι κ) : Finset ι → Exterior R ι κ := by
  classical
  exact fun I => if h : F I then f ⟨I, h⟩ else 0

noncomputable def familyDifferential (H : R) (b : ι → ι → R) (c : ι → κ)
    (F : Finset ι → Prop) (f : {I : Finset ι // F I} → Exterior R ι κ) :
      {I : Finset ι // F I} → Exterior R ι κ :=
  fun J => exteriorDifferential H b c (familyExtend F f) J.val

theorem familyDifferential_squared (H : R) (b : ι → ι → R) (c : ι → κ)
    (F : Finset ι → Prop) (hclosed : DownClosed F)
    (hcompat : ∀ I, F I → Compatible b c I)
    (f : {I : Finset ι // F I} → Exterior R ι κ) (J : {I : Finset ι // F I}) :
    familyDifferential H b c F (familyDifferential H b c F f) J = 0 := by
  have hlocal : familyDifferential H b c F (familyDifferential H b c F f) J =
      exteriorDifferential H b c (exteriorDifferential H b c (familyExtend F f)) J.val := by
    apply Finset.sum_congr rfl
    intro i _
    have hi : F (J.val.erase i) := hclosed _ _ (Finset.erase_subset _ _) J.property
    simp only [familyExtend, dif_pos hi, familyDifferential]
  rw [hlocal]
  exact exteriorDifferential_squared H b c _ J.val (hcompat _ J.property)

noncomputable def familyDifferentialLinear (H : R) (b : ι → ι → R) (c : ι → κ)
    (F : Finset ι → Prop) :
    ({I : Finset ι // F I} → Exterior R ι κ) →ₗ[R]
      ({I : Finset ι // F I} → Exterior R ι κ) where
  toFun := familyDifferential H b c F
  map_add' f g := by
    funext J
    simp only [familyDifferential, exteriorDifferential, Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : F (J.val.erase i) <;> simp [familyExtend, h, map_add]
  map_smul' a f := by
    funext J
    simp only [familyDifferential, exteriorDifferential, Pi.smul_apply, RingHom.id_apply,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : F (J.val.erase i) <;> simp [familyExtend, h, map_smul]

def familyFixedWeight (c : ι → κ) (F : Finset ι → Prop) (s : ℕ) :
    Submodule R ({I : Finset ι // F I} → Exterior R ι κ) where
  carrier := {f | ∀ I, f I ∈ fixedWeight c I.val s}
  zero_mem' := by intro I; exact Submodule.zero_mem _
  add_mem' := by intro f g hf hg I; exact Submodule.add_mem _ (hf I) (hg I)
  smul_mem' := by intro a f hf I; exact Submodule.smul_mem _ a (hf I)

theorem familyDifferential_fixedWeight (H : R) (b : ι → ι → R) (c : ι → κ)
    (F : Finset ι → Prop) (hclosed : DownClosed F)
    (hcompat : ∀ I, F I → Compatible b c I) (hdiag : ∀ i, b i i = 0)
    (s : ℕ) (f : familyFixedWeight (R := R) c F s) :
    familyDifferential H b c F f.val ∈ familyFixedWeight c F s := by
  intro J
  apply Submodule.sum_mem
  intro i hi
  have hI : F (J.val.erase i) := hclosed _ _ (Finset.erase_subset _ _) J.property
  have hB : ∀ j ∈ insert i (J.val.erase i), b j i = 0 := by
    rw [Finset.insert_erase hi]
    exact compatible_column_zero b c J.val (hcompat _ J.property) i hi (hdiag i)
  have hp := exteriorFace_fixedWeight H b c (J.val.erase i) i (Finset.not_mem_erase i J.val)
    hB s (f.val ⟨J.val.erase i, hI⟩) (f.property ⟨J.val.erase i, hI⟩)
  simpa only [familyExtend, dif_pos hI, Finset.insert_erase hi] using hp

noncomputable def familyWeightDifferential (H : R) (b : ι → ι → R) (c : ι → κ)
    (F : Finset ι → Prop) (hclosed : DownClosed F)
    (hcompat : ∀ I, F I → Compatible b c I) (hdiag : ∀ i, b i i = 0) (s : ℕ) :
    familyFixedWeight (R := R) c F s →ₗ[R] familyFixedWeight (R := R) c F s where
  toFun f := ⟨familyDifferential H b c F f.val,
    familyDifferential_fixedWeight H b c F hclosed hcompat hdiag s f⟩
  map_add' f g := by apply Subtype.ext; exact (familyDifferentialLinear H b c F).map_add f.val g.val
  map_smul' a f := by apply Subtype.ext; exact (familyDifferentialLinear H b c F).map_smul a f.val

theorem familyWeightDifferential_squared (H : R) (b : ι → ι → R) (c : ι → κ)
    (F : Finset ι → Prop) (hclosed : DownClosed F)
    (hcompat : ∀ I, F I → Compatible b c I) (hdiag : ∀ i, b i i = 0) (s : ℕ) :
    (familyWeightDifferential H b c F hclosed hcompat hdiag s).comp
      (familyWeightDifferential H b c F hclosed hcompat hdiag s) = 0 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext J
  exact familyDifferential_squared H b c F hclosed hcompat f.val J

/-- The cohomological degree is the cardinality of the fixed stratum. -/
def degreePart (F : Finset ι → Prop) (p : ℕ) :
    Submodule R ({I : Finset ι // F I} → Exterior R ι κ) where
  carrier := {f | ∀ I, I.val.card ≠ p → f I = 0}
  zero_mem' := by intro I _; rfl
  add_mem' := by intro f g hf hg I hI; simp [hf I hI, hg I hI]
  smul_mem' := by intro a f hf I hI; simp [hf I hI]

theorem familyDifferential_degree (H : R) (b : ι → ι → R) (c : ι → κ)
    (F : Finset ι → Prop) (hclosed : DownClosed F) (p : ℕ)
    (f : {I : Finset ι // F I} → Exterior R ι κ) (hf : f ∈ degreePart F p) :
    familyDifferential H b c F f ∈ degreePart F (p + 1) := by
  intro J hJ
  apply Finset.sum_eq_zero
  intro i hi
  have hI : F (J.val.erase i) := hclosed _ _ (Finset.erase_subset _ _) J.property
  have hcard : (J.val.erase i).card ≠ p := by
    have h := Finset.card_erase_of_mem hi
    have hpos : 0 < J.val.card := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  have hz := hf ⟨J.val.erase i, hI⟩ hcard
  simp only [familyExtend, dif_pos hI, hz, map_zero]

def familyCochains (c : ι → κ) (F : Finset ι → Prop) (s p : ℕ) :
    Submodule R ({I : Finset ι // F I} → Exterior R ι κ) :=
  familyFixedWeight c F s ⊓ degreePart F p

/-- An actual degree-raising map between the homogeneous cochain modules. -/
noncomputable def cochainDifferential (H : R) (b : ι → ι → R) (c : ι → κ)
    (F : Finset ι → Prop) (hclosed : DownClosed F)
    (hcompat : ∀ I, F I → Compatible b c I) (hdiag : ∀ i, b i i = 0) (s p : ℕ) :
    familyCochains (R := R) c F s p →ₗ[R] familyCochains (R := R) c F s (p + 1) where
  toFun f := ⟨familyDifferential H b c F f.val,
    familyDifferential_fixedWeight H b c F hclosed hcompat hdiag s ⟨f.val, f.property.1⟩,
    familyDifferential_degree H b c F hclosed p f.val f.property.2⟩
  map_add' f g := by apply Subtype.ext; exact (familyDifferentialLinear H b c F).map_add f.val g.val
  map_smul' a f := by apply Subtype.ext; exact (familyDifferentialLinear H b c F).map_smul a f.val

theorem cochainDifferential_squared (H : R) (b : ι → ι → R) (c : ι → κ)
    (F : Finset ι → Prop) (hclosed : DownClosed F)
    (hcompat : ∀ I, F I → Compatible b c I) (hdiag : ∀ i, b i i = 0) (s p : ℕ) :
    (cochainDifferential H b c F hclosed hcompat hdiag s (p + 1)).comp
      (cochainDifferential H b c F hclosed hcompat hdiag s p) = 0 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext J
  exact familyDifferential_squared H b c F hclosed hcompat f.val J

/-- The independent/color-compatible family is determined over the integers. -/
def integerSupportFamily (B : ι → ι → ℤ) (c : ι → κ) : Finset ι → Prop :=
  Compatible B c

omit [DecidableEq ι] [DecidableEq κ] in
theorem integerSupportFamily_downClosed (B : ι → ι → ℤ) (c : ι → κ) :
    DownClosed (integerSupportFamily B c) := by
  intro I J hIJ hJ
  exact compatible_subset B c I J hIJ hJ

/-- Entries of the even matrix are halved integrally, then sent to the coefficient ring. -/
def halfMatrix (B : ι → ι → ℤ) : ι → ι → R := fun i j => ((B i j / 2 : ℤ) : R)

omit [DecidableEq ι] [DecidableEq κ] in
theorem integerSupportFamily_compatible (B : ι → ι → ℤ) (c : ι → κ) (I : Finset ι)
    (hI : integerSupportFamily B c I) : Compatible (halfMatrix (R := R) B) c I := by
  intro i hi j hj hij
  obtain ⟨hc, hB, hB'⟩ := hI i hi j hj hij
  exact ⟨hc, by simp [halfMatrix, hB], by simp [halfMatrix, hB']⟩

omit [DecidableEq ι] in
theorem halfMatrix_diagonal (B : ι → ι → ℤ) (hdiag : ∀ i, B i i = 0) :
    ∀ i, halfMatrix (R := R) B i i = 0 := by
  intro i
  simp [halfMatrix, hdiag i]

/-- Graph independence uses only the original integer exchange matrix, not colors or scalars. -/
def integerGraphFamily (B : ι → ι → ℤ) (I : Finset ι) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, i ≠ j → B i j = 0 ∧ B j i = 0

/-- The manuscript's coloring condition on pairs of nonadjacent mutable vertices. -/
def AdmissibleColoring (B : ι → ι → ℤ) (c : ι → κ) : Prop :=
  ∀ i j, i ≠ j → B i j = 0 → B j i = 0 → c i ≠ c j

omit [DecidableEq ι] [DecidableEq κ] in
theorem integerGraphFamily_downClosed (B : ι → ι → ℤ) :
    DownClosed (integerGraphFamily B) := by
  intro I J hIJ hJ i hi j hj hij
  exact hJ i (hIJ hi) j (hIJ hj) hij

omit [DecidableEq ι] [DecidableEq κ] in
theorem integerGraphFamily_compatible (B : ι → ι → ℤ) (c : ι → κ)
    (hc : AdmissibleColoring B c) (I : Finset ι) (hI : integerGraphFamily B I) :
    Compatible (halfMatrix (R := R) B) c I := by
  intro i hi j hj hij
  obtain ⟨hB, hB'⟩ := hI i hi j hj hij
  exact ⟨hc i j hij hB hB', by simp [halfMatrix, hB], by simp [halfMatrix, hB']⟩

/-- The index type in this differential is unchanged in every characteristic. -/
noncomputable def integerGraphDifferential (H : R) (B : ι → ι → ℤ) (c : ι → κ)
    (hc : AdmissibleColoring B c) (hdiag : ∀ i, B i i = 0) (s : ℕ) :
    familyFixedWeight (R := R) c (integerGraphFamily B) s →ₗ[R]
      familyFixedWeight (R := R) c (integerGraphFamily B) s :=
  familyWeightDifferential H (halfMatrix B) c (integerGraphFamily B)
    (integerGraphFamily_downClosed B) (integerGraphFamily_compatible B c hc)
    (halfMatrix_diagonal B hdiag) s

theorem integerGraphDifferential_squared (H : R) (B : ι → ι → ℤ) (c : ι → κ)
    (hc : AdmissibleColoring B c) (hdiag : ∀ i, B i i = 0) (s : ℕ) :
    (integerGraphDifferential H B c hc hdiag s).comp (integerGraphDifferential H B c hc hdiag s) = 0 :=
  familyWeightDifferential_squared H (halfMatrix B) c (integerGraphFamily B)
    (integerGraphFamily_downClosed B) (integerGraphFamily_compatible B c hc)
    (halfMatrix_diagonal B hdiag) s

noncomputable def integerGraphCochainDifferential (H : R) (B : ι → ι → ℤ) (c : ι → κ)
    (hc : AdmissibleColoring B c) (hdiag : ∀ i, B i i = 0) (s p : ℕ) :
    familyCochains (R := R) c (integerGraphFamily B) s p →ₗ[R]
      familyCochains (R := R) c (integerGraphFamily B) s (p + 1) :=
  cochainDifferential H (halfMatrix B) c (integerGraphFamily B)
    (integerGraphFamily_downClosed B) (integerGraphFamily_compatible B c hc)
    (halfMatrix_diagonal B hdiag) s p

theorem integerGraphCochainDifferential_squared (H : R) (B : ι → ι → ℤ) (c : ι → κ)
    (hc : AdmissibleColoring B c) (hdiag : ∀ i, B i i = 0) (s p : ℕ) :
    (integerGraphCochainDifferential H B c hc hdiag s (p + 1)).comp
      (integerGraphCochainDifferential H B c hc hdiag s p) = 0 :=
  cochainDifferential_squared H (halfMatrix B) c (integerGraphFamily B)
    (integerGraphFamily_downClosed B) (integerGraphFamily_compatible B c hc)
    (halfMatrix_diagonal B hdiag) s p

#print axioms familyExtend
#print axioms familyDifferential
#print axioms familyDifferential_squared
#print axioms familyDifferentialLinear
#print axioms familyFixedWeight
#print axioms familyDifferential_fixedWeight
#print axioms familyWeightDifferential
#print axioms familyWeightDifferential_squared
#print axioms integerSupportFamily
#print axioms integerSupportFamily_downClosed
#print axioms halfMatrix
#print axioms integerSupportFamily_compatible
#print axioms halfMatrix_diagonal
#print axioms integerGraphDifferential
#print axioms integerGraphDifferential_squared
#print axioms degreePart
#print axioms familyDifferential_degree
#print axioms familyCochains
#print axioms cochainDifferential
#print axioms cochainDifferential_squared
#print axioms integerGraphCochainDifferential
#print axioms integerGraphCochainDifferential_squared
#print axioms integerGraphFamily
#print axioms AdmissibleColoring
#print axioms integerGraphFamily_downClosed
#print axioms integerGraphFamily_compatible
#print axioms DownClosed

end Verification.EvenFixedGraph
