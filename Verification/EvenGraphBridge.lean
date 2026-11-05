/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.EvenBasis
import Verification.EvenFixedGraph
import Verification.GraphBlocks

/-!
# Even Graph Bridge

Literal coordinate identities bridging the formal exterior differential and its
pure graph part. The graph differential appears at `H = 0`, after the additional
diagonal sign `(-1)^μ`. For general `H` the extra operator removes one frozen
symbol and inserts a mutable linear combination; it must not be discarded.
-/

namespace Verification.EvenGraphBridge

open Verification.EvenDifferential Verification.EvenAdmissible

section FullFace

variable {R ι κ : Type*} [CommRing R] [DecidableEq ι] [DecidableEq κ]

theorem substitution_rankOne (H : R) (b : ι → ι → R) (c : ι → κ) (i : ι) :
    substitution H b c i = rankOneErase (frozenDual (c i))
      (frozenVector (c i) - replacementVector H b i) := by
  ext v z
  simp only [substitution, rankOneErase, LinearMap.coe_mk, AddHom.coe_mk,
    frozenDual, LinearMap.proj_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem substitution_formula (H : R) (b : ι → ι → R) (c : ι → κ) (i : ι)
    (x : Exterior R ι κ) :
    ExteriorAlgebra.map (substitution H b c i) x =
      x - ExteriorAlgebra.ι R (frozenVector (c i)) * contract (frozenDual (c i)) x +
        ExteriorAlgebra.ι R (replacementVector H b i) * contract (frozenDual (c i)) x := by
  rw [substitution_rankOne, rankOneErase_formula, map_sub, sub_mul]
  abel

theorem substitution_zero_formula (b : ι → ι → R) (c : ι → κ) (i : ι)
    (x : Exterior R ι κ) :
    ExteriorAlgebra.map (substitution 0 b c i) x =
      x - ExteriorAlgebra.ι R (frozenVector (c i)) * contract (frozenDual (c i)) x := by
  rw [substitution_formula]
  have hz : replacementVector (κ := κ) (0 : R) b i = 0 := by ext z; cases z <;> simp [replacementVector]
  simp [hz]

variable [Fintype ι]

def perturbationFace (b : ι → ι → R) (c : ι → κ) (i : ι) :
    Exterior R ι κ →ₗ[R] Exterior R ι κ :=
  (LinearMap.mulLeft R (-∑ j, b j i • ExteriorAlgebra.ι R (mutableVector (κ := κ) j))).comp
    ((contract (frozenDual (c i))).comp (contract (mutableDual i)))

/-- Exact `U + H V`, including every half-matrix coefficient and its sign. -/
theorem exteriorFace_decomposition (H : R) (b : ι → ι → R) (c : ι → κ) (i : ι) :
    exteriorFace H b c i = exteriorFace 0 b c i + H • perturbationFace b c i := by
  apply LinearMap.ext
  intro x
  simp only [exteriorFace, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.add_apply, LinearMap.smul_apply]
  rw [substitution_formula, substitution_zero_formula, replacementVector_sum]
  simp only [map_smul, map_sum, map_neg, perturbationFace, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, neg_smul, neg_mul, smul_mul_assoc, smul_neg]

/-- The perturbation is zero when the contracted form lacks the affected frozen coordinate. -/
theorem perturbationFace_zero_of_frozen_absent (b : ι → ι → R) (c : ι → κ) (i : ι)
    (x : Exterior R ι κ) (hx : contract (frozenDual (c i)) x = 0) :
    perturbationFace b c i x = 0 := by
  have h := CliffordAlgebra.contractLeft_comm (frozenDual (R := R) (c i))
    (mutableDual (R := R) (κ := κ) i) (Q := (0 : QuadraticForm R (Coordinates R ι κ))) x
  change contract (frozenDual (c i)) (contract (mutableDual i) x) =
    -contract (mutableDual i) (contract (frozenDual (c i)) x) at h
  simp only [hx, map_zero, neg_zero] at h
  simp [perturbationFace, h]

end FullFace

section Words

variable {R α : Type*} [CommRing R] [DecidableEq α]

def word (L : List α) : ExteriorAlgebra R (α → R) :=
  (L.map fun a => ExteriorAlgebra.ι R (Pi.single a 1)).prod

theorem word_nil : word (R := R) ([] : List α) = 1 := rfl

theorem word_cons (a : α) (L : List α) :
    word (R := R) (a :: L) = ExteriorAlgebra.ι R (Pi.single a 1) * word L := rfl

theorem word_append (L K : List α) :
    word (R := R) (L ++ K) = word L * word K := by simp [word]

theorem contract_word_absent (a : α) (L : List α) (ha : a ∉ L) :
    contract (LinearMap.proj a : Module.Dual R (α → R)) (word L) = 0 := by
  induction L with
  | nil => simp [word, contract, CliffordAlgebra.contractLeft_one]
  | cons z L ih =>
    have haz : a ≠ z := fun h => ha (by simp [h])
    have haL : a ∉ L := fun h => ha (List.mem_cons_of_mem _ h)
    rw [word_cons]
    have hz := ih haL
    simp only [contract] at hz
    simp [contract, CliffordAlgebra.contractLeft_ι_mul, haz, Ne.symm haz, hz]

theorem contract_word_present (a : α) (L : List α) (hn : L.Nodup) (ha : a ∈ L) :
    contract (LinearMap.proj a : Module.Dual R (α → R)) (word L) =
      (-1 : R) ^ L.idxOf a • word (L.erase a) := by
  induction L with
  | nil => simp at ha
  | cons z L ih =>
    obtain ⟨hzL, hL⟩ := List.nodup_cons.mp hn
    by_cases hza : z = a
    · subst z
      rw [word_cons]
      have hz := contract_word_absent (R := R) a L hzL
      simp only [contract] at hz
      simp [contract, CliffordAlgebra.contractLeft_ι_mul, hz]
    · have haL : a ∈ L := (List.mem_cons.mp ha).resolve_left (Ne.symm hza)
      rw [word_cons]
      simp only [contract, CliffordAlgebra.contractLeft_ι_mul]
      change (Pi.single z (1 : R) : α → R) a • word L - ExteriorAlgebra.ι R (Pi.single z 1) *
        contract (LinearMap.proj a) (word L) = _
      rw [ih hL haL]
      simp [Pi.single_apply, hza, Ne.symm hza, List.idxOf_cons_ne _ hza,
        List.erase_cons_tail, word_cons, pow_succ, mul_smul_comm]

end Words

section OrderedLists

variable {α β : Type*} [LinearOrder α] [DecidableEq β]

theorem idxOf_map_injective (f : α → β) (hf : Function.Injective f) (L : List α) (a : α) :
    (L.map f).idxOf (f a) = L.idxOf a := by
  induction L with
  | nil => rfl
  | cons z L ih =>
    by_cases h : z = a
    · simp [h]
    · simp [List.idxOf_cons_ne _ h, List.idxOf_cons_ne _ (hf.ne h), ih]

theorem idxOf_sorted (L : List α) (hs : L.Sorted (· ≤ ·)) (a : α) (ha : a ∈ L) :
    L.idxOf a = (L.filter fun z => decide (z < a)).length := by
  induction L with
  | nil => simp at ha
  | cons z L ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    by_cases h : z = a
    · subst z
      have hn : (L.filter fun z => decide (z < a)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro z hz
        simpa using not_lt_of_ge (hhead z hz)
      simp [hn]
    · have haL : a ∈ L := (List.mem_cons.mp ha).resolve_left (Ne.symm h)
      have hza : z < a := lt_of_le_of_ne (hhead a haL) h
      simp [List.idxOf_cons_ne _ h, hza, ih htail haL]

theorem sort_erase (A : Finset α) (a : α) :
    (A.sort (· ≤ ·)).erase a = (A.erase a).sort (· ≤ ·) := by
  have hn := (A.sort_nodup (· ≤ ·)).erase a
  have hs := (A.sort_sorted (· ≤ ·)).sublist (List.erase_sublist (a := a))
  have he : ((A.sort (· ≤ ·)).erase a).toFinset = A.erase a := by
    ext z
    simp [(A.sort_nodup (· ≤ ·)).mem_erase_iff]
  have h := (List.toFinset_sort (· ≤ ·) hn).mpr hs
  simpa only [he] using h.symm

theorem idxOf_sort (A : Finset α) (a : α) (ha : a ∈ A) :
    (A.sort (· ≤ ·)).idxOf a = rankBelow A a := by
  rw [idxOf_sorted _ (A.sort_sorted (· ≤ ·)) a (by simpa using ha)]
  rw [← List.toFinset_card_of_nodup ((A.sort_nodup (· ≤ ·)).filter _)]
  simp [List.toFinset_filter, rankBelow]

end OrderedLists

section Monomials

variable {R ι κ : Type*} [CommRing R] [LinearOrder ι] [LinearOrder κ]

local instance sumWordBEq : BEq (ι ⊕ κ) := instBEqOfDecidableEq

def monomialList (A : Finset ι) (F : Finset κ) : List (ι ⊕ κ) :=
  (A.sort (· ≤ ·)).map Sum.inl ++ (F.sort (· ≤ ·)).map Sum.inr

def monomial (A : Finset ι) (F : Finset κ) : Exterior R ι κ := word (monomialList A F)

theorem monomialList_nodup (A : Finset ι) (F : Finset κ) : (monomialList A F).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(A.sort_nodup _).map Sum.inl_injective, (F.sort_nodup _).map Sum.inr_injective, ?_⟩
  intro z hz hz'
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hz
  simp at hz'

theorem mutable_mem_monomialList (A : Finset ι) (F : Finset κ) (i : ι) :
    Sum.inl i ∈ monomialList A F ↔ i ∈ A := by simp [monomialList]

theorem frozen_mem_monomialList (A : Finset ι) (F : Finset κ) (a : κ) :
    Sum.inr a ∈ monomialList A F ↔ a ∈ F := by simp [monomialList]

theorem monomialList_erase (A : Finset ι) (F : Finset κ) (i : ι) (hi : i ∈ A) :
    (monomialList A F).erase (Sum.inl i) = monomialList (A.erase i) F := by
  unfold monomialList
  rw [List.erase_append_left (a := (Sum.inl i : ι ⊕ κ))
    ((F.sort (· ≤ ·)).map Sum.inr) (by simp [hi]),
    ← List.map_erase (f := Sum.inl (β := κ)) Sum.inl_injective, sort_erase]

theorem monomialList_idxOf (A : Finset ι) (F : Finset κ) (i : ι) (hi : i ∈ A) :
    (monomialList A F).idxOf (Sum.inl i) = rankBelow A i := by
  unfold monomialList
  rw [List.idxOf_append_of_mem (a := (Sum.inl i : ι ⊕ κ)) (by simp [hi]),
    idxOf_map_injective (Sum.inl (β := κ)) Sum.inl_injective,
    idxOf_sort A i hi]

theorem contract_monomial (A : Finset ι) (F : Finset κ) (i : ι) :
    contract (mutableDual (R := R) (κ := κ) i) (monomial A F) =
      if i ∈ A then (-1 : R) ^ rankBelow A i • monomial (A.erase i) F else 0 := by
  by_cases hi : i ∈ A
  · rw [if_pos hi]
    change contract (LinearMap.proj (Sum.inl i)) (word (monomialList A F)) = _
    rw [contract_word_present _ _ (monomialList_nodup A F)
      ((mutable_mem_monomialList A F i).mpr hi), monomialList_erase A F i hi,
      monomialList_idxOf A F i hi]
    rfl
  · rw [if_neg hi]
    exact contract_word_absent _ _ (by simpa only [mutable_mem_monomialList] using hi)

theorem zero_substitution_coordinate (b : ι → ι → R) (c : ι → κ) (i : ι) (z : ι ⊕ κ) :
    substitution 0 b c i (Pi.single z (1 : R)) =
      if z = Sum.inr (c i) then 0 else Pi.single z 1 := by
  cases z with
  | inl j => simpa [mutableVector] using substitution_mutable (0 : R) b c i j
  | inr a =>
    by_cases h : a = c i
    · subst a
      rw [if_pos rfl]
      change substitution 0 b c i (frozenVector (c i)) = 0
      rw [substitution_frozen_same]
      ext z
      cases z <;> simp [replacementVector]
    · simpa [frozenVector, h] using substitution_frozen_other (0 : R) b c i a h

theorem zero_substitution_word (b : ι → ι → R) (c : ι → κ) (i : ι) (L : List (ι ⊕ κ)) :
    ExteriorAlgebra.map (substitution 0 b c i) (word L) =
      if (Sum.inr (c i) : ι ⊕ κ) ∈ L then 0 else word L := by
  classical
  induction L with
  | nil => simp [word]
  | cons z L ih =>
    rw [word_cons, map_mul, ExteriorAlgebra.map_apply_ι, zero_substitution_coordinate, ih]
    by_cases hz : z = Sum.inr (c i) <;> by_cases hL : Sum.inr (c i) ∈ L <;>
      simp [hz, hL, eq_comm]

/-- Literal H=0 face matrix on ordered mutable-then-frozen exterior words. -/
theorem exteriorFace_zero_monomial (b : ι → ι → R) (c : ι → κ) (i : ι)
    (A : Finset ι) (F : Finset κ) :
    exteriorFace 0 b c i (monomial A F) =
      if i ∈ A ∧ c i ∉ F then (-1 : R) ^ rankBelow A i • monomial (A.erase i) F else 0 := by
  simp only [exteriorFace, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [contract_monomial]
  by_cases hi : i ∈ A
  · rw [if_pos hi, map_smul]
    unfold monomial
    rw [zero_substitution_word]
    by_cases hc : c i ∈ F <;> simp [frozen_mem_monomialList, hi, hc]
  · simp [hi]

def signedMonomial (I A : Finset ι) (F : Finset κ) : Exterior R ι κ :=
  (-1 : R) ^ mu (I ∪ A) I • monomial A F

theorem mu_incidence_coefficient (I A : Finset ι) (hIA : Disjoint I A) (i : ι) (hi : i ∈ A) :
    (-1 : R) ^ mu (I ∪ A) I * (-1 : R) ^ rankBelow A i =
      (-1 : R) ^ rankBelow I i *
        (-1 : R) ^ mu (insert i I ∪ A.erase i) (insert i I) := by
  rw [mu_face_difference I A hIA i hi]
  simp only [pow_add]
  have hν := g_power_self_inverse (-1 : R) (by simp) (rankBelow I i)
  calc
    _ = ((-1 : R) ^ rankBelow I i * (-1 : R) ^ rankBelow I i) *
        ((-1 : R) ^ mu (I ∪ A) I * (-1 : R) ^ rankBelow A i) := by rw [hν, one_mul]
    _ = _ := by ring

/-- The second, ordinary sign normalization gives exactly simplicial incidence. -/
theorem exteriorFace_zero_signedMonomial (b : ι → ι → R) (c : ι → κ) (i : ι)
    (I A : Finset ι) (F : Finset κ) (hIA : Disjoint I A) :
    exteriorFace 0 b c i (signedMonomial I A F) =
      if i ∈ A ∧ c i ∉ F then
        Verification.GraphBlocks.incidence R I i • signedMonomial (insert i I) (A.erase i) F
      else 0 := by
  rw [signedMonomial, map_smul, exteriorFace_zero_monomial]
  by_cases h : i ∈ A ∧ c i ∉ F
  · rw [if_pos h, if_pos h]
    simp only [signedMonomial, smul_smul]
    rw [mu_incidence_coefficient I A hIA i h.1]
    rfl
  · simp [h]

variable {G : SimpleGraph ι} {c : ι → κ}

/-- Evaluation on actual ordered exterior words, with the paper's additional sign. -/
noncomputable def signedWordRealization :
    (Verification.GraphBlocks.MonomialIndex G c →₀ R) →ₗ[R] Exterior R ι κ :=
  Finsupp.linearCombination R (fun x => signedMonomial x.I x.A x.F)

theorem signedWordRealization_single (x : Verification.GraphBlocks.MonomialIndex G c) (r : R) :
    signedWordRealization (Finsupp.single x r) = r • signedMonomial x.I x.A x.F := by
  exact Finsupp.linearCombination_single R r x

open Classical in
/-- On each independent target face, the literal exterior matrix entry is exactly the
monomial graph differential entry. No conjugacy or square-zero law is assumed here. -/
theorem graph_monomial_face (b : ι → ι → R)
    (x : Verification.GraphBlocks.MonomialIndex G c) (i : ι)
    (hJ : G.IsIndepSet ((insert i x.I : Finset ι) : Set ι)) :
    exteriorFace 0 b c i (signedMonomial x.I x.A x.F) =
      signedWordRealization (if h : Verification.GraphBlocks.CanAdd x i then
        Finsupp.single (Verification.GraphBlocks.addMonomial x i h)
          (Verification.GraphBlocks.incidence R x.I i) else 0) := by
  classical
  rw [exteriorFace_zero_signedMonomial b c i x.I x.A x.F x.disjoint]
  by_cases h : i ∈ x.A ∧ c i ∉ x.F
  · have hc : Verification.GraphBlocks.CanAdd x i := ⟨h.1, h.2, hJ⟩
    rw [if_pos h, dif_pos hc, signedWordRealization_single]
    rfl
  · have hc : ¬Verification.GraphBlocks.CanAdd x i := fun hi => h ⟨hi.1, hi.2.1⟩
    simp [h, hc]

end Monomials

section CanonicalBasis

open Verification.EvenBasis

variable {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ]
  [LinearOrder ι] [LinearOrder κ]

local instance basisSumOrder : LinearOrder (ι ⊕ κ) := Sum.Lex.linearOrder
local instance basisSumPartialOrder : PartialOrder (ι ⊕ κ) := basisSumOrder.toPartialOrder
local instance basisSumPreorder : Preorder (ι ⊕ κ) := basisSumOrder.toPreorder
local instance basisSumLE : LE (ι ⊕ κ) := basisSumOrder.toLE
local instance basisSumLT : LT (ι ⊕ κ) := basisSumOrder.toLT
local instance basisSumDecidableLE : DecidableRel ((· ≤ ·) : (ι ⊕ κ) → (ι ⊕ κ) → Prop) :=
  basisSumOrder.toDecidableLE
local instance basisSumBEq : BEq (ι ⊕ κ) := instBEqOfDecidableEq

omit [Fintype ι] [Fintype κ] in
theorem monomialList_sorted (A : Finset ι) (F : Finset κ) :
    (monomialList A F).Sorted (· ≤ ·) := by
  apply List.pairwise_append.mpr
  refine ⟨List.pairwise_map.mpr ?_, List.pairwise_map.mpr ?_, ?_⟩
  · exact (A.sort_sorted (· ≤ ·)).imp (fun h => Sum.Lex.inl h)
  · exact (F.sort_sorted (· ≤ ·)).imp (fun h => Sum.Lex.inr h)
  · intro x hx y hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hy
    exact Sum.Lex.sep _ _

omit [Fintype ι] [Fintype κ] in
theorem monomialList_toFinset (A : Finset ι) (F : Finset κ) :
    (monomialList A F).toFinset = A.disjSum F := by
  ext z
  cases z <;> simp [monomialList]

omit [Fintype ι] [Fintype κ] in
theorem allowed_index_word (c : ι → κ) (I : Finset ι) (n : ℕ)
    (a : WedgeIndex (Allowed (forbiddenCoordinates c I)) n) :
    List.ofFn (fun k => (a k).val) =
      monomialList ((allowedTripleEquiv c I n a).val.1) ((allowedTripleEquiv c I n a).val.2) := by
  let L := List.ofFn (fun k => (a k).val)
  have hn : L.Nodup := List.nodup_ofFn.mpr (Subtype.val_injective.comp a.injective)
  have hs : L.Sorted (· ≤ ·) := List.pairwise_ofFn.mpr (by
    intro i j hij
    exact a.monotone hij.le)
  have hT : L.toFinset =
      ((Finset.univ.image a).map (Function.Embedding.subtype _)) := by
    ext z
    simp [L, List.mem_ofFn, Finset.mem_image, Finset.mem_map]
  have hAF : L.toFinset =
      ((allowedTripleEquiv c I n a).val.1).disjSum ((allowedTripleEquiv c I n a).val.2) := by
    rw [hT]
    ext z
    cases z <;> simp [allowedTripleEquiv, wedgeFinsetEquiv, allowedFinsetEquiv, subsetTripleEquiv]
  have hsort := (List.toFinset_sort (· ≤ ·) hn).mpr hs
  have hsort' := (List.toFinset_sort (· ≤ ·)
    (monomialList_nodup (allowedTripleEquiv c I n a).val.1 (allowedTripleEquiv c I n a).val.2)).mpr
      (monomialList_sorted _ _)
  rw [monomialList_toFinset, ← hAF] at hsort'
  exact hsort.symm.trans hsort'

theorem word_ofFn {α : Type*} [DecidableEq α] (n : ℕ) (v : Fin n → α) :
    word (R := R) (List.ofFn v) = ExteriorAlgebra.ιMulti R n (fun k => Pi.single (v k) 1) := by
  simp only [word, List.map_ofFn, ExteriorAlgebra.ιMulti_apply, Function.comp_def]

theorem extend_ιMulti {α : Type*} [DecidableEq α] (S : Finset α) (n : ℕ)
    (v : Fin n → Allowed S) :
    ExteriorAlgebra.map (extendAllowed (R := R) S)
      (ExteriorAlgebra.ιMulti R n (fun k => Pi.single (v k) 1)) =
      ExteriorAlgebra.ιMulti R n (fun k => Pi.single (v k).val 1) := by
  rw [ExteriorAlgebra.map_apply_ιMulti]
  congr 1
  funext k
  exact extendAllowed_single S (v k)

omit [Fintype ι] [Fintype κ] in
theorem allowedToAdmissible_monomial (c : ι → κ) (I : Finset ι) (n : ℕ)
    (a : WedgeIndex (Allowed (forbiddenCoordinates c I)) n) :
    (allowedToAdmissible c I n (orderedWedge (R := R) n a) : Exterior R ι κ) =
      monomial ((allowedTripleEquiv c I n a).val.1) ((allowedTripleEquiv c I n a).val.2) := by
  rw [allowedToAdmissible_val, exteriorPower_map_coe]
  simp only [orderedWedge, exteriorPower.ιMulti_apply_coe]
  trans ExteriorAlgebra.ιMulti R n (fun k => Pi.single (a k).val 1)
  · rw [ExteriorAlgebra.map_apply_ιMulti]
    congr 1
    funext k
    ext z
    by_cases hz : z ∈ forbiddenCoordinates c I
    · have hne : (a k).val ≠ z := by intro h; exact (a k).property (h ▸ hz)
      simp [extendAllowed, hz, Pi.single_apply, hne, Ne.symm hne]
    · simp [extendAllowed, hz, Pi.single_apply, Subtype.ext_iff]
  · rw [← word_ofFn, allowed_index_word]
    rfl

/-- Exact equality with the canonical basis already proved independent and spanning. -/
theorem admissibleTripleBasis_monomial (c : ι → κ) (I : Finset ι) (n : ℕ)
    (AF : TripleIndex c I n) :
    (admissibleTripleBasis (R := R) c I n AF : Exterior R ι κ) = monomial AF.val.1 AF.val.2 := by
  rw [admissibleTripleBasis_apply, allowedToAdmissible_monomial, Equiv.apply_symm_apply]

end CanonicalBasis

#print axioms substitution_rankOne
#print axioms substitution_formula
#print axioms substitution_zero_formula
#print axioms perturbationFace
#print axioms exteriorFace_decomposition
#print axioms perturbationFace_zero_of_frozen_absent
#print axioms word
#print axioms word_nil
#print axioms word_cons
#print axioms word_append
#print axioms contract_word_absent
#print axioms contract_word_present
#print axioms idxOf_map_injective
#print axioms idxOf_sorted
#print axioms sort_erase
#print axioms idxOf_sort
#print axioms monomialList
#print axioms monomial
#print axioms monomialList_nodup
#print axioms mutable_mem_monomialList
#print axioms frozen_mem_monomialList
#print axioms monomialList_erase
#print axioms monomialList_idxOf
#print axioms contract_monomial
#print axioms zero_substitution_coordinate
#print axioms zero_substitution_word
#print axioms exteriorFace_zero_monomial
#print axioms signedMonomial
#print axioms mu_incidence_coefficient
#print axioms exteriorFace_zero_signedMonomial
#print axioms signedWordRealization
#print axioms signedWordRealization_single
#print axioms graph_monomial_face
#print axioms monomialList_sorted
#print axioms monomialList_toFinset
#print axioms allowed_index_word
#print axioms word_ofFn
#print axioms extend_ιMulti
#print axioms allowedToAdmissible_monomial
#print axioms admissibleTripleBasis_monomial

end Verification.EvenGraphBridge

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.EvenGraphBridge.basisSumBEq
#print axioms Verification.EvenGraphBridge.basisSumDecidableLE
#print axioms Verification.EvenGraphBridge.basisSumLE
#print axioms Verification.EvenGraphBridge.basisSumLT
#print axioms Verification.EvenGraphBridge.basisSumOrder
#print axioms Verification.EvenGraphBridge.basisSumPartialOrder
#print axioms Verification.EvenGraphBridge.basisSumPreorder
#print axioms Verification.EvenGraphBridge.sumWordBEq
