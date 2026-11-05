/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Even Differential

Actual exterior substitutions and contractions for the even differential.
The coefficient ring is arbitrary: taking `R = ℤ[H]` checks the stronger
formal identity asserted in manuscript.tex 2383--2456.
The finite-sum differential and its restrictions are constructed in the
ambient exterior algebra. The fixed-weight finite basis triples and their
identification with geometric Milnor--Witt summands are not constructed here.
-/

namespace Verification.EvenDifferential

open Finset

section GeneralExterior

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

abbrev contract (d : Module.Dual R M) : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d

/-- Naturality of exterior contraction under a substitution preserving the functional. -/
theorem contract_map (d : Module.Dual R M) (T : M →ₗ[R] M)
    (hd : ∀ v, d (T v) = d v) (x : ExteriorAlgebra R M) :
    contract d (ExteriorAlgebra.map T x) = ExteriorAlgebra.map T (contract d x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [contract, CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
      change contract d (ExteriorAlgebra.map T (ExteriorAlgebra.ι R v * x)) = _
      rw [map_mul, ExteriorAlgebra.map_apply_ι]
      simp only [contract, CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul,
        map_mul, ExteriorAlgebra.map_apply_ι, hd]
      rw [hx]

theorem exterior_maps_commute (T U : M →ₗ[R] M) (hTU : T.comp U = U.comp T)
    (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.map T (ExteriorAlgebra.map U x) =
      ExteriorAlgebra.map U (ExteriorAlgebra.map T x) := by
  have h := congrArg (fun f : M →ₗ[R] M => ExteriorAlgebra.map f) hTU
  dsimp only at h
  rw [← ExteriorAlgebra.map_comp_map, ← ExteriorAlgebra.map_comp_map] at h
  exact congrArg (fun f => f x) h

end GeneralExterior

section Coordinates

variable {R ι κ : Type*} [CommRing R] [DecidableEq ι] [DecidableEq κ]

abbrev Coordinates (R ι κ : Type*) := (Sum ι κ) → R
abbrev Exterior (R ι κ : Type*) [CommRing R] := ExteriorAlgebra R (Coordinates R ι κ)

def mutableVector (j : ι) : Coordinates R ι κ := Pi.single (Sum.inl j) 1
def frozenVector (a : κ) : Coordinates R ι κ := Pi.single (Sum.inr a) 1

/-- `b j i` is the integer half-entry `B_{ji}/2`, mapped into the coefficient ring. -/
def replacementVector (H : R) (b : ι → ι → R) (i : ι) : Coordinates R ι κ :=
  fun z => match z with
    | Sum.inl j => -H * b j i
    | Sum.inr _ => 0

def substitution (H : R) (b : ι → ι → R) (c : ι → κ) (i : ι) :
    Coordinates R ι κ →ₗ[R] Coordinates R ι κ where
  toFun v := v + v (Sum.inr (c i)) • (replacementVector H b i - frozenVector (c i))
  map_add' v w := by simp [add_smul]; abel
  map_smul' a v := by simp [smul_add, smul_smul]

theorem substitution_mutable (H : R) (b : ι → ι → R) (c : ι → κ) (i j : ι) :
    substitution H b c i (mutableVector j) = mutableVector (R := R) (κ := κ) j := by
  simp [substitution, mutableVector, Pi.single_apply]

theorem substitution_frozen_same (H : R) (b : ι → ι → R) (c : ι → κ) (i : ι) :
    substitution H b c i (frozenVector (c i)) = replacementVector (κ := κ) H b i := by
  simp [substitution, frozenVector]

theorem substitution_frozen_other (H : R) (b : ι → ι → R) (c : ι → κ) (i : ι) (a : κ)
    (ha : a ≠ c i) :
    substitution H b c i (frozenVector a) = frozenVector (R := R) (ι := ι) a := by
  simp [substitution, frozenVector, Pi.single_apply, ha, Ne.symm ha]

theorem substitution_frozen_coordinate (H : R) (b : ι → ι → R) (c : ι → κ)
    (i : ι) (a : κ) (ha : a ≠ c i) (v : Coordinates R ι κ) :
    substitution H b c i v (Sum.inr a) = v (Sum.inr a) := by
  simp [substitution, replacementVector, frozenVector, Pi.single_apply, ha, Ne.symm ha]

theorem substitution_replacement (H : R) (b : ι → ι → R) (c : ι → κ) (i j : ι) :
    substitution H b c i (replacementVector H b j) = replacementVector (κ := κ) H b j := by
  simp [substitution, replacementVector]

theorem substitutions_commute (H : R) (b : ι → ι → R) (c : ι → κ) (i j : ι)
    (hc : c i ≠ c j) :
    (substitution H b c i).comp (substitution H b c j) =
      (substitution H b c j).comp (substitution H b c i) := by
  ext v z
  simp only [LinearMap.comp_apply, substitution, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  simp [replacementVector, frozenVector, Pi.single_apply, hc, Ne.symm hc]
  ring

def mutableDual (i : ι) : Module.Dual R (Coordinates R ι κ) := LinearMap.proj (Sum.inl i)

theorem other_dual_preserved (H : R) (b : ι → ι → R) (c : ι → κ) (i j : ι)
    (hB : b i j = 0) (v : Coordinates R ι κ) :
    mutableDual i (substitution H b c j v) = mutableDual (R := R) (κ := κ) i v := by
  simp [mutableDual, substitution, replacementVector, frozenVector, Pi.single_apply, hB]

/-- The actual exterior face map: contraction, then frozen substitution. -/
def exteriorFace (H : R) (b : ι → ι → R) (c : ι → κ) (i : ι) :
    Exterior R ι κ →ₗ[R] Exterior R ι κ :=
  (ExteriorAlgebra.map (substitution H b c i)).toLinearMap.comp (contract (mutableDual i))

theorem exteriorFace_anticommute (H : R) (b : ι → ι → R) (c : ι → κ) (i j : ι)
    (hc : c i ≠ c j) (hij : b i j = 0) (hji : b j i = 0) (x : Exterior R ι κ) :
    exteriorFace H b c i (exteriorFace H b c j x) =
      -(exteriorFace H b c j (exteriorFace H b c i x)) := by
  simp only [exteriorFace, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [contract_map _ _ (other_dual_preserved H b c i j hij),
    contract_map _ _ (other_dual_preserved H b c j i hji)]
  rw [exterior_maps_commute _ _ (substitutions_commute H b c i j hc)]
  rw [show contract (mutableDual (R := R) (κ := κ) i) (contract (mutableDual j) x) =
      -(contract (mutableDual j) (contract (mutableDual i) x)) from
        CliffordAlgebra.contractLeft_comm _ _ x]
  simp only [map_neg]

theorem exteriorFace_same (H : R) (b : ι → ι → R) (c : ι → κ) (i : ι)
    (hii : b i i = 0) (x : Exterior R ι κ) :
    exteriorFace H b c i (exteriorFace H b c i x) = 0 := by
  simp only [exteriorFace, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [contract_map _ _ (other_dual_preserved H b c i i hii)]
  rw [show contract (mutableDual (R := R) (κ := κ) i) (contract (mutableDual i) x) = 0 from
    CliffordAlgebra.contractLeft_contractLeft _ x]
  simp only [map_zero]

/-- Exterior-valued cochains, with the exact sum of the manuscript's face maps. -/
def exteriorDifferential (H : R) (b : ι → ι → R) (c : ι → κ)
    (f : Finset ι → Exterior R ι κ) (J : Finset ι) : Exterior R ι κ :=
  ∑ i ∈ J, exteriorFace H b c i (f (J.erase i))

/-- The assembled differential squares to zero at every independent subset. -/
theorem exteriorDifferential_squared (H : R) (b : ι → ι → R) (c : ι → κ)
    (f : Finset ι → Exterior R ι κ) (J : Finset ι)
    (hind : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → c i ≠ c j ∧ b i j = 0 ∧ b j i = 0) :
    exteriorDifferential H b c (exteriorDifferential H b c f) J = 0 := by
  unfold exteriorDifferential
  simp_rw [map_sum]
  let term : ι × ι → Exterior R ι κ := fun p =>
    if p.1 = p.2 then 0 else
      exteriorFace H b c p.1 (exteriorFace H b c p.2 (f ((J.erase p.1).erase p.2)))
  have hexpand :
      (∑ i ∈ J, ∑ j ∈ J.erase i,
        exteriorFace H b c i (exteriorFace H b c j (f ((J.erase i).erase j)))) =
        ∑ p ∈ J ×ˢ J, term p := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = ∑ j ∈ J.erase i, term (i, j) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [term, if_neg (Ne.symm (Finset.mem_erase.mp hj).1)]
      _ = ∑ j ∈ J, term (i, j) := Finset.sum_erase J (by simp [term])
  rw [hexpand]
  apply Finset.sum_involution (fun p _ => (p.2, p.1))
  · intro p hp
    by_cases h : p.1 = p.2
    · simp [term, h]
    · obtain ⟨hc, hij, hji⟩ := hind p.1 (Finset.mem_product.mp hp).1
        p.2 (Finset.mem_product.mp hp).2 h
      simp only [term, if_neg h, if_neg (Ne.symm h)]
      have herase : (J.erase p.1).erase p.2 = (J.erase p.2).erase p.1 := by
        ext a
        simp only [Finset.mem_erase]
        tauto
      rw [herase]
      exact eq_neg_iff_add_eq_zero.mp (exteriorFace_anticommute H b c p.1 p.2 hc hij hji _)
  · intro p _ hn he
    have h : p.1 = p.2 := congrArg Prod.snd he
    exact hn (by simp [term, h])
  · intro p hp
    exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp).2, (Finset.mem_product.mp hp).1⟩
  · intro p _
    cases p
    rfl

theorem exteriorDifferential_add (H : R) (b : ι → ι → R) (c : ι → κ)
    (f g : Finset ι → Exterior R ι κ) :
    exteriorDifferential H b c (f + g) = exteriorDifferential H b c f + exteriorDifferential H b c g := by
  funext J
  simp [exteriorDifferential, map_add, Finset.sum_add_distrib]

/-- The exact pairwise conditions supplied by an independently colored subset. -/
def Compatible (b : ι → ι → R) (c : ι → κ) (J : Finset ι) : Prop :=
  ∀ i ∈ J, ∀ j ∈ J, i ≠ j → c i ≠ c j ∧ b i j = 0 ∧ b j i = 0

omit [DecidableEq ι] [DecidableEq κ] in
theorem compatible_subset (b : ι → ι → R) (c : ι → κ) (I J : Finset ι)
    (hIJ : I ⊆ J) (hJ : Compatible b c J) : Compatible b c I := by
  intro i hi j hj hij
  exact hJ i (hIJ hi) j (hIJ hj) hij

omit [DecidableEq κ] in
theorem compatible_column_zero (b : ι → ι → R) (c : ι → κ) (J : Finset ι)
    (hJ : Compatible b c J) (i : ι) (hi : i ∈ J) (hii : b i i = 0) :
    ∀ j ∈ J, b j i = 0 := by
  intro j hj
  by_cases h : i = j
  · simpa [← h] using hii
  · exact (hJ i hi j hj h).2.2

noncomputable def compatibleExtend (b : ι → ι → R) (c : ι → κ)
    (f : {I : Finset ι // Compatible b c I} → Exterior R ι κ) : Finset ι → Exterior R ι κ := by
  classical
  exact fun I => if hI : Compatible b c I then f ⟨I, hI⟩ else 0

noncomputable def compatibleDifferential (H : R) (b : ι → ι → R) (c : ι → κ)
    (f : {I : Finset ι // Compatible b c I} → Exterior R ι κ) :
      {I : Finset ι // Compatible b c I} → Exterior R ι κ :=
  fun I => exteriorDifferential H b c (compatibleExtend b c f) I.val

theorem compatibleDifferential_squared (H : R) (b : ι → ι → R) (c : ι → κ)
    (f : {I : Finset ι // Compatible b c I} → Exterior R ι κ)
    (I : {I : Finset ι // Compatible b c I}) :
    compatibleDifferential H b c (compatibleDifferential H b c f) I = 0 := by
  have hlocal : compatibleDifferential H b c (compatibleDifferential H b c f) I =
      exteriorDifferential H b c (exteriorDifferential H b c (compatibleExtend b c f)) I.val := by
    apply Finset.sum_congr rfl
    intro i _
    have hi : Compatible b c (I.val.erase i) :=
      compatible_subset b c _ _ (Finset.erase_subset i I.val) I.property
    simp only [compatibleExtend, dif_pos hi, compatibleDifferential]
  rw [hlocal]
  exact exteriorDifferential_squared H b c _ I.val I.property

/-- The ambient differential is an actual linear map on exterior-valued cochains. -/
def exteriorDifferentialLinear (H : R) (b : ι → ι → R) (c : ι → κ) :
    (Finset ι → Exterior R ι κ) →ₗ[R] (Finset ι → Exterior R ι κ) where
  toFun := exteriorDifferential H b c
  map_add' := exteriorDifferential_add H b c
  map_smul' a f := by funext J; simp [exteriorDifferential, map_smul, Finset.smul_sum]

section FiniteMutable
variable [Fintype ι]

/-- The coordinate formula is exactly the finite exterior substitution in the paper. -/
theorem replacementVector_sum (H : R) (b : ι → ι → R) (i : ι) :
    replacementVector (κ := κ) H b i =
      -H • ∑ j, b j i • mutableVector (R := R) (κ := κ) j := by
  ext z
  cases z with
  | inl a => simp [replacementVector, mutableVector, Pi.single_apply, Finset.sum_apply]
  | inr a => simp [replacementVector, mutableVector, Pi.single_apply, Finset.sum_apply]

/-- Under independence, only mutable coordinates outside the target subset occur. -/
theorem replacementVector_complement (H : R) (b : ι → ι → R) (i : ι) (J : Finset ι)
    (hJ : ∀ j ∈ J, b j i = 0) :
    replacementVector (κ := κ) H b i =
      -H • ∑ j ∈ univ \ J, b j i • mutableVector (R := R) (κ := κ) j := by
  rw [replacementVector_sum]
  congr 1
  symm
  apply Finset.sum_subset (Finset.sdiff_subset)
  intro j _ hj
  have hjJ : j ∈ J := by simpa using hj
  simp [hJ j hjJ]

/-- The frozen generator is sent to the precise exterior linear combination. -/
theorem exterior_substitution_frozen (H : R) (b : ι → ι → R) (c : ι → κ) (i : ι) :
    ExteriorAlgebra.map (substitution H b c i)
      (ExteriorAlgebra.ι R (frozenVector (c i))) =
      -H • ∑ j, b j i • ExteriorAlgebra.ι R (mutableVector (κ := κ) j) := by
  rw [ExteriorAlgebra.map_apply_ι, substitution_frozen_same, replacementVector_sum]
  simp only [map_smul, map_sum]

end FiniteMutable

end Coordinates

section Normalization

variable {ι : Type*} [LinearOrder ι]

def rankBelow (S : Finset ι) (i : ι) : ℕ := (S.filter (fun j => j < i)).card
def mu (S I : Finset ι) : ℕ := ∑ j ∈ I, rankBelow S j

theorem mu_insert (S I : Finset ι) (i : ι) (hi : i ∉ I) :
    mu S (insert i I) = mu S I + rankBelow S i := by
  simp [mu, hi, add_comm]

theorem rankBelow_disjoint_union (I A : Finset ι) (h : Disjoint I A) (i : ι) :
    rankBelow (I ∪ A) i = rankBelow I i + rankBelow A i := by
  rw [rankBelow, Finset.filter_union, Finset.card_union_of_disjoint]
  · rfl
  · exact h.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- The source and target μ exponents differ by ν+r. -/
theorem mu_face_difference (I A : Finset ι) (h : Disjoint I A) (i : ι) (hi : i ∈ A) :
    mu (insert i I ∪ A.erase i) (insert i I) =
      mu (I ∪ A) I + rankBelow I i + rankBelow A i := by
  have hiI : i ∉ I := fun hI => Finset.disjoint_left.mp h hI hi
  have hS : insert i I ∪ A.erase i = I ∪ A := by
    ext j
    by_cases hji : j = i <;> simp [hji, hi]
  rw [hS, mu_insert _ _ _ hiI, rankBelow_disjoint_union I A h]
  omega

variable {R : Type*} [CommRing R]

/-- The basis change removes all g-factors from the pure contraction coefficient. -/
theorem normalize_pure_coefficient (g : R) (hg : g ^ 2 = 1) (m ν r : ℕ) :
    g ^ m * g ^ ν * (-g) ^ r * g ^ (m + ν + r) = (-1 : R) ^ r := by
  calc
    _ = (-1 : R) ^ r * (g ^ (m + ν + r)) ^ 2 := by
      rw [neg_pow]
      simp only [pow_add]
      ring
    _ = (-1 : R) ^ r := by
      rw [← pow_mul, Nat.mul_comm (m + ν + r) 2, pow_mul, hg, one_pow, mul_one]

theorem g_power_mod_two (g : R) (hg : g ^ 2 = 1) (m : ℕ) : g ^ m = g ^ (m % 2) := by
  calc
    g ^ m = g ^ (m % 2 + 2 * (m / 2)) := by rw [Nat.mod_add_div]
    _ = g ^ (m % 2) := by rw [pow_add, pow_mul, hg, one_pow, mul_one]

theorem g_power_self_inverse (g : R) (hg : g ^ 2 = 1) (m : ℕ) : g ^ m * g ^ m = 1 := by
  rw [← pow_two, ← pow_mul, Nat.mul_comm m 2, pow_mul, hg, one_pow]

/-- The diagonal g-power basis change is an actual linear involution. -/
def normalizationLinearEquiv {β : Type*} (g : R) (hg : g ^ 2 = 1) (w : β → ℕ) :
    (β → R) ≃ₗ[R] (β → R) where
  toFun v i := g ^ w i * v i
  invFun v i := g ^ w i * v i
  left_inv v := by funext i; dsimp only; rw [← mul_assoc, g_power_self_inverse g hg, one_mul]
  right_inv v := by funext i; dsimp only; rw [← mul_assoc, g_power_self_inverse g hg, one_mul]
  map_add' v z := by funext i; simp [mul_add]
  map_smul' a v := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The coefficient identity with exactly the mod-two μ specified in the paper. -/
theorem normalize_mu_coefficient (g : R) (hg : g ^ 2 = 1)
    (I A : Finset ι) (h : Disjoint I A) (i : ι) (hi : i ∈ A) :
    g ^ (mu (I ∪ A) I % 2) * g ^ rankBelow I i * (-g) ^ rankBelow A i *
      g ^ (mu (insert i I ∪ A.erase i) (insert i I) % 2) = (-1 : R) ^ rankBelow A i := by
  rw [← g_power_mod_two g hg (mu (I ∪ A) I),
    ← g_power_mod_two g hg (mu (insert i I ∪ A.erase i) (insert i I)),
    mu_face_difference I A h i hi]
  exact normalize_pure_coefficient g hg _ _ _

/-- Multiples of h are unchanged by every basis factor g^m. -/
theorem g_power_times_h (g h : R) (gh : g * h = h) (m : ℕ) : g ^ m * h = h := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, mul_assoc, gh, ih]

theorem epsilon_power_times_h (g h : R) (gh : g * h = h) (m : ℕ) :
    (-g) ^ m * h = (-1 : R) ^ m * h := by
  rw [neg_pow, mul_assoc, g_power_times_h g h gh m]

theorem normalize_h_multiple (g h a : R) (gh : g * h = h) (m n : ℕ) :
    g ^ m * (h * a) * g ^ n = h * a := by
  rw [← mul_assoc, g_power_times_h g h gh m]
  calc
    h * a * g ^ n = (g ^ n * h) * a := by ring
    _ = h * a := by rw [g_power_times_h g h gh n]

end Normalization

#print axioms contract_map
#print axioms exterior_maps_commute
#print axioms substitution_mutable
#print axioms substitution_frozen_same
#print axioms substitution_frozen_other
#print axioms substitution_frozen_coordinate
#print axioms substitution_replacement
#print axioms substitutions_commute
#print axioms other_dual_preserved
#print axioms exteriorFace_anticommute
#print axioms exteriorFace_same
#print axioms exteriorDifferential_squared
#print axioms exteriorDifferential_add
#print axioms compatible_subset
#print axioms compatible_column_zero
#print axioms compatibleDifferential_squared
#print axioms exteriorDifferentialLinear
#print axioms replacementVector_sum
#print axioms replacementVector_complement
#print axioms exterior_substitution_frozen
#print axioms mu_insert
#print axioms rankBelow_disjoint_union
#print axioms mu_face_difference
#print axioms normalize_pure_coefficient
#print axioms g_power_mod_two
#print axioms g_power_self_inverse
#print axioms normalizationLinearEquiv
#print axioms normalize_mu_coefficient
#print axioms g_power_times_h
#print axioms epsilon_power_times_h
#print axioms normalize_h_multiple

end Verification.EvenDifferential

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.EvenDifferential.Compatible
#print axioms Verification.EvenDifferential.Coordinates
#print axioms Verification.EvenDifferential.Exterior
#print axioms Verification.EvenDifferential.compatibleDifferential
#print axioms Verification.EvenDifferential.compatibleExtend
#print axioms Verification.EvenDifferential.contract
#print axioms Verification.EvenDifferential.exteriorDifferential
#print axioms Verification.EvenDifferential.exteriorFace
#print axioms Verification.EvenDifferential.frozenVector
#print axioms Verification.EvenDifferential.mu
#print axioms Verification.EvenDifferential.mutableDual
#print axioms Verification.EvenDifferential.mutableVector
#print axioms Verification.EvenDifferential.rankBelow
#print axioms Verification.EvenDifferential.replacementVector
#print axioms Verification.EvenDifferential.substitution
