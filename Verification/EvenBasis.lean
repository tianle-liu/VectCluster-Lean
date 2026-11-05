/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.EvenAdmissible
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Sum.Order

/-!
# Even Basis

Ordered coordinate wedges form a genuine basis over every commutative ring.
This file supplies the independence and spanning bridge for the even model.
-/

namespace Verification.EvenBasis

open Verification.EvenDifferential Verification.EvenAdmissible

section OrderedBasis

variable {R α : Type*} [CommRing R] [Fintype α] [LinearOrder α]

abbrev WedgeIndex (α : Type*) [LinearOrder α] (n : ℕ) := Fin n ↪o α

noncomputable instance wedgeIndexFintype (n : ℕ) : Fintype (WedgeIndex α n) :=
  Fintype.ofFinite _

noncomputable instance wedgeIndexDecidableEq (n : ℕ) : DecidableEq (WedgeIndex α n) :=
  Classical.decEq _

noncomputable def orderedWedge (n : ℕ) (a : WedgeIndex α n) :
    ExteriorAlgebra.exteriorPower R n (α → R) :=
  exteriorPower.ιMulti R n (fun k => Pi.single (a k) 1)

noncomputable def wedgeCoordinate (n : ℕ) (a : WedgeIndex α n) :
    Module.Dual R (ExteriorAlgebra.exteriorPower R n (α → R)) :=
  exteriorPower.pairingDual R (α → R) n
    (exteriorPower.ιMulti R n (fun k => LinearMap.proj (a k)))

omit [Fintype α] in
theorem wedgeCoordinate_orderedWedge (n : ℕ) (a b : WedgeIndex α n) :
    wedgeCoordinate (R := R) n a (orderedWedge n b) = if a = b then 1 else 0 := by
  classical
  by_cases h : a = b
  · subst b
    simpa [wedgeCoordinate, orderedWedge] using
      exteriorPower.pairingDual_apply_apply_eq_one
        (R := R) (fun i : α => Pi.single i 1) (fun i => LinearMap.proj i)
        (by intro i; simp) (by intro i j h; simp [h, Ne.symm h]) n a
  · simpa [wedgeCoordinate, orderedWedge, h] using
      exteriorPower.pairingDual_apply_apply_eq_one_zero
        (R := R) (fun i : α => Pi.single i 1) (fun i => LinearMap.proj i)
        (by intro i j h; simp [h, Ne.symm h]) n a b h

omit [Fintype α] in
theorem injective_tuple_sorted (n : ℕ) (v : Fin n → α) (hv : Function.Injective v) :
    ∃ (a : WedgeIndex α n) (σ : Equiv.Perm (Fin n)), v = a ∘ σ := by
  classical
  let S := Finset.univ.image v
  have hS : S.card = n := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hv]
    simp
  let e : Fin n ≃ S := Equiv.ofBijective
    (fun k => ⟨v k, Finset.mem_image_of_mem v (Finset.mem_univ k)⟩)
    ⟨fun i j h => hv (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨k, rfl⟩⟩
  let o := S.orderIsoOfFin hS
  refine ⟨S.orderEmbOfFin hS, e.trans o.toEquiv.symm, ?_⟩
  funext k
  exact (congrArg Subtype.val (o.apply_symm_apply (e k))).symm

noncomputable def coordinateAnalysis (n : ℕ) :
    ExteriorAlgebra.exteriorPower R n (α → R) →ₗ[R] (WedgeIndex α n → R) :=
  LinearMap.pi (fun a => wedgeCoordinate n a)

noncomputable def coordinateSynthesis (n : ℕ) :
    (WedgeIndex α n → R) →ₗ[R] ExteriorAlgebra.exteriorPower R n (α → R) where
  toFun f := ∑ a, f a • orderedWedge n a
  map_add' f g := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r f := by simp [Finset.smul_sum, smul_smul]

omit [Fintype α] in
theorem analysis_orderedWedge (n : ℕ) (a : WedgeIndex α n) :
    coordinateAnalysis (R := R) n (orderedWedge n a) = Pi.single a 1 := by
  classical
  ext b
  simp [coordinateAnalysis, wedgeCoordinate_orderedWedge, Pi.single_apply, eq_comm]

theorem synthesis_single (n : ℕ) (a : WedgeIndex α n) :
    coordinateSynthesis (R := R) n (Pi.single a 1) = orderedWedge n a := by
  classical
  simp [coordinateSynthesis, Pi.single_apply]

theorem synthesis_analysis (n : ℕ) :
    (coordinateSynthesis (R := R) (α := α) n).comp (coordinateAnalysis n) = LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply (Pi.basisFun R α).ext_alternating
  intro v hv
  obtain ⟨a, σ, rfl⟩ := injective_tuple_sorted n v hv
  have hperm := (exteriorPower.ιMulti R n (M := α → R)).map_perm
    (fun k => Pi.single (a k) 1) σ
  change coordinateSynthesis n (coordinateAnalysis n
    (exteriorPower.ιMulti R n (fun i => (Pi.basisFun R α) ((a ∘ σ) i)) )) = _
  simp only [Pi.basisFun_apply]
  change coordinateSynthesis n (coordinateAnalysis n
    (exteriorPower.ιMulti R n ((fun k => Pi.single (a k) 1) ∘ σ))) = _
  rw [hperm]
  simp only [Units.smul_def, map_zsmul, show exteriorPower.ιMulti R n (fun k => Pi.single (a k) 1) =
    orderedWedge (R := R) n a from rfl, analysis_orderedWedge, synthesis_single]
  exact hperm.symm

theorem analysis_synthesis (n : ℕ) :
    (coordinateAnalysis (R := R) (α := α) n).comp (coordinateSynthesis n) = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro f
  funext a
  simp [coordinateSynthesis, coordinateAnalysis, wedgeCoordinate_orderedWedge]

noncomputable def orderedExteriorEquiv (n : ℕ) :
    ExteriorAlgebra.exteriorPower R n (α → R) ≃ₗ[R] (WedgeIndex α n → R) :=
  LinearEquiv.ofLinear (coordinateAnalysis n) (coordinateSynthesis n)
    (analysis_synthesis n) (synthesis_analysis n)

#print axioms wedgeCoordinate_orderedWedge
#print axioms injective_tuple_sorted
#print axioms analysis_orderedWedge
#print axioms synthesis_single
#print axioms synthesis_analysis
#print axioms analysis_synthesis
#print axioms orderedExteriorEquiv

end OrderedBasis

section CoordinateRestriction

variable {R α : Type*} [CommRing R] [DecidableEq α]

abbrev Allowed (S : Finset α) := {a : α // a ∉ S}

def restrictAllowed (S : Finset α) : (α → R) →ₗ[R] (Allowed S → R) where
  toFun v a := v a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def extendAllowed (S : Finset α) : (Allowed S → R) →ₗ[R] (α → R) where
  toFun v a := if h : a ∈ S then 0 else v ⟨a, h⟩
  map_add' _ _ := by ext a; by_cases h : a ∈ S <;> simp [h]
  map_smul' _ _ := by ext a; by_cases h : a ∈ S <;> simp [h]

theorem restrict_extend (S : Finset α) :
    (restrictAllowed (R := R) S).comp (extendAllowed S) = LinearMap.id := by
  ext v a
  simp [restrictAllowed, extendAllowed, a.property]

theorem extend_restrict (S : Finset α) :
    (extendAllowed (R := R) S).comp (restrictAllowed S) = coordinateMask S := by
  ext v a
  simp [restrictAllowed, extendAllowed, coordinateMask]

theorem mask_extend (S : Finset α) :
    (coordinateMask (R := R) S).comp (extendAllowed S) = extendAllowed S := by
  ext v a
  by_cases h : a ∈ S <;> simp [extendAllowed, coordinateMask, h]

theorem extendAllowed_single (S : Finset α) (a : Allowed S) :
    extendAllowed (R := R) S (Pi.single a 1) = Pi.single a.val 1 := by
  ext z
  by_cases hz : z ∈ S
  · have hne : a.val ≠ z := by intro h; exact a.property (h ▸ hz)
    simp [extendAllowed, hz, Pi.single_apply, hne, Ne.symm hne]
  · simp [extendAllowed, hz, Pi.single_apply, Subtype.ext_iff]

end CoordinateRestriction

section PowerCoe

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

theorem exteriorPower_map_coe (n : ℕ) (T : M →ₗ[R] N)
    (x : ExteriorAlgebra.exteriorPower R n M) :
    (exteriorPower.map n T x : ExteriorAlgebra R N) = ExteriorAlgebra.map T x := by
  have h : (ExteriorAlgebra.exteriorPower R n N).subtype.comp (exteriorPower.map n T) =
      (ExteriorAlgebra.map T).toLinearMap.comp (ExteriorAlgebra.exteriorPower R n M).subtype := by
    apply exteriorPower.linearMap_ext
    ext v
    simp [ExteriorAlgebra.map_apply_ιMulti]
  exact LinearMap.congr_fun h x

end PowerCoe

theorem extend_orderedWedge {R α : Type*} [CommRing R] [LinearOrder α]
    (S : Finset α) (n : ℕ) (a : WedgeIndex (Allowed S) n) :
    (exteriorPower.map n (extendAllowed (R := R) S) (orderedWedge n a) :
      ExteriorAlgebra R (α → R)) =
      ExteriorAlgebra.ιMulti R n (fun k => Pi.single (a k).val 1) := by
  rw [exteriorPower_map_coe]
  change ExteriorAlgebra.map (extendAllowed (R := R) S)
    (ExteriorAlgebra.ιMulti R n (fun k => Pi.single (a k) (1 : R))) = _
  rw [ExteriorAlgebra.map_apply_ιMulti]
  congr 1
  funext k
  exact extendAllowed_single _ _

section Admissible

variable {R ι κ : Type*} [CommRing R] [DecidableEq ι] [DecidableEq κ]

noncomputable def allowedToAdmissible (c : ι → κ) (I : Finset ι) (n : ℕ) :
    ExteriorAlgebra.exteriorPower R n (Allowed (forbiddenCoordinates c I) → R) →ₗ[R]
      admissibleDegree (R := R) c I n where
  toFun x := ⟨(exteriorPower.map n (extendAllowed (R := R) (forbiddenCoordinates c I)) x).val, by
    constructor
    · exact (exteriorPower.map n (extendAllowed (R := R) (forbiddenCoordinates c I)) x).property
    · apply (permittedForms_iff_mask c I _).mpr
      rw [exteriorPower_map_coe]
      change ((ExteriorAlgebra.map (coordinateMask (forbiddenCoordinates c I))).comp
        (ExteriorAlgebra.map (extendAllowed (forbiddenCoordinates c I)))) x.val = _
      rw [ExteriorAlgebra.map_comp_map, mask_extend]⟩
  map_add' x y := by
    apply Subtype.ext
    exact congrArg (fun z : ExteriorAlgebra.exteriorPower R n (Coordinates R ι κ) => z.val)
      ((exteriorPower.map n (extendAllowed (R := R) (forbiddenCoordinates c I))).map_add x y)
  map_smul' r x := by
    apply Subtype.ext
    exact congrArg (fun z : ExteriorAlgebra.exteriorPower R n (Coordinates R ι κ) => z.val)
      ((exteriorPower.map n (extendAllowed (R := R) (forbiddenCoordinates c I))).map_smul r x)

noncomputable def admissibleToAllowed (c : ι → κ) (I : Finset ι) (n : ℕ) :
    admissibleDegree (R := R) c I n →ₗ[R]
      ExteriorAlgebra.exteriorPower R n (Allowed (forbiddenCoordinates c I) → R) :=
  (exteriorPower.map n (restrictAllowed (forbiddenCoordinates c I))).comp
    ((admissibleDegree (R := R) c I n).subtype.codRestrict _ (fun x => x.property.1))

theorem allowedToAdmissible_val (c : ι → κ) (I : Finset ι) (n : ℕ)
    (x : ExteriorAlgebra.exteriorPower R n (Allowed (forbiddenCoordinates c I) → R)) :
    (allowedToAdmissible c I n x : Exterior R ι κ) =
      (exteriorPower.map n (extendAllowed (R := R) (forbiddenCoordinates c I)) x :
        Exterior R ι κ) := rfl

theorem allowed_admissible_inverse (c : ι → κ) (I : Finset ι) (n : ℕ) :
    (admissibleToAllowed (R := R) c I n).comp (allowedToAdmissible c I n) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change exteriorPower.map n (restrictAllowed (forbiddenCoordinates c I))
    (exteriorPower.map n (extendAllowed (forbiddenCoordinates c I)) x) = x
  have h := congrArg (fun f => f x)
    (exteriorPower.map_comp (n := n) (extendAllowed (R := R) (forbiddenCoordinates c I))
      (restrictAllowed (forbiddenCoordinates c I)))
  simpa [restrict_extend, exteriorPower.map_id] using h.symm

theorem admissible_allowed_inverse (c : ι → κ) (I : Finset ι) (n : ℕ) :
    (allowedToAdmissible (R := R) c I n).comp (admissibleToAllowed c I n) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (exteriorPower.map n (extendAllowed (forbiddenCoordinates c I))
    (exteriorPower.map n (restrictAllowed (forbiddenCoordinates c I))
      ⟨x.val, x.property.1⟩) : Exterior R ι κ) = x.val
  rw [exteriorPower_map_coe, exteriorPower_map_coe]
  change ((ExteriorAlgebra.map (extendAllowed (forbiddenCoordinates c I))).comp
    (ExteriorAlgebra.map (restrictAllowed (forbiddenCoordinates c I)))) x.val = x.val
  rw [ExteriorAlgebra.map_comp_map, extend_restrict]
  exact (permittedForms_iff_mask c I x.val).mp x.property.2

noncomputable def admissibleExteriorEquiv (c : ι → κ) (I : Finset ι) (n : ℕ) :
    admissibleDegree (R := R) c I n ≃ₗ[R]
      ExteriorAlgebra.exteriorPower R n (Allowed (forbiddenCoordinates c I) → R) :=
  LinearEquiv.ofLinear (admissibleToAllowed c I n) (allowedToAdmissible c I n)
    (allowed_admissible_inverse c I n) (admissible_allowed_inverse c I n)

end Admissible

#print axioms restrict_extend
#print axioms extend_restrict
#print axioms mask_extend
#print axioms exteriorPower_map_coe
#print axioms allowedToAdmissible
#print axioms admissibleToAllowed
#print axioms allowed_admissible_inverse
#print axioms admissible_allowed_inverse
#print axioms admissibleExteriorEquiv

section FiniteIndices

variable {α : Type*} [LinearOrder α]

noncomputable def wedgeFinsetEquiv (n : ℕ) :
    WedgeIndex α n ≃ {T : Finset α // T.card = n} where
  toFun a := ⟨Finset.univ.image a, by rw [Finset.card_image_of_injective _ a.injective]; simp⟩
  invFun T := T.val.orderEmbOfFin T.property
  left_inv a := (Finset.orderEmbOfFin_unique' _ (by intro k; simp)).symm
  right_inv T := by apply Subtype.ext; exact Finset.image_orderEmbOfFin_univ _ _

noncomputable def allowedFinsetEquiv (S : Finset α) (n : ℕ) :
    {T : Finset (Allowed S) // T.card = n} ≃
      {T : Finset α // Disjoint S T ∧ T.card = n} where
  toFun T := ⟨T.val.map (Function.Embedding.subtype _), by
    constructor
    · apply Finset.disjoint_left.mpr
      intro a ha hT
      exact (Finset.property_of_mem_map_subtype _ hT) ha
    · simpa using T.property⟩
  invFun T := ⟨T.val.subtype (fun a => a ∉ S), by
    rw [Finset.card_subtype, Finset.filter_eq_self.mpr]
    · exact T.property.2
    · intro a ha hS
      exact Finset.disjoint_left.mp T.property.1 hS ha⟩
  left_inv T := by
    apply Subtype.ext
    ext a
    simp [a.property]
  right_inv T := by
    apply Subtype.ext
    apply Finset.subtype_map_of_mem
    intro a ha hS
    exact Finset.disjoint_left.mp T.property.1 hS ha

end FiniteIndices

section TripleIndices

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- For a fixed stratum `I`, these are exactly the manuscript's remaining basis labels. -/
abbrev TripleIndex (c : ι → κ) (I : Finset ι) (n : ℕ) :=
  {AF : Finset ι × Finset κ //
    Disjoint I AF.1 ∧ Disjoint (I.image c) AF.2 ∧ AF.1.card + AF.2.card = n}

theorem forbidden_disjoint_iff (c : ι → κ) (I : Finset ι) (T : Finset (ι ⊕ κ)) :
    Disjoint (forbiddenCoordinates c I) T ↔
      Disjoint I T.toLeft ∧ Disjoint (I.image c) T.toRight := by
  simp only [Finset.disjoint_left, forbiddenCoordinates, Finset.mem_union,
    Finset.mem_image, Finset.mem_toLeft, Finset.mem_toRight]
  constructor
  · intro h
    exact ⟨fun a ha hT => h (Or.inl ⟨a, ha, rfl⟩) hT,
      fun a ha hT => h (Or.inr ⟨a, ha, rfl⟩) hT⟩
  · rintro ⟨hL, hR⟩ z (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) hT
    · exact hL ha hT
    · exact hR ha hT

noncomputable def subsetTripleEquiv (c : ι → κ) (I : Finset ι) (n : ℕ) :
    {T : Finset (ι ⊕ κ) // Disjoint (forbiddenCoordinates c I) T ∧ T.card = n} ≃
      TripleIndex c I n where
  toFun T := ⟨(T.val.toLeft, T.val.toRight),
    (forbidden_disjoint_iff c I T.val).mp T.property.1 |>.1,
    (forbidden_disjoint_iff c I T.val).mp T.property.1 |>.2,
    Finset.card_toLeft_add_card_toRight.trans T.property.2⟩
  invFun AF := ⟨AF.val.1.disjSum AF.val.2, by
    constructor
    · rw [forbidden_disjoint_iff]
      simpa using And.intro AF.property.1 AF.property.2.1
    · simpa using AF.property.2.2⟩
  left_inv T := by apply Subtype.ext; exact Finset.toLeft_disjSum_toRight
  right_inv AF := by apply Subtype.ext; simp

end TripleIndices

section BasisEquivalence

variable {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ]
  [LinearOrder ι] [LinearOrder κ]

local instance sumCoordinateOrder : LinearOrder (ι ⊕ κ) := Sum.Lex.linearOrder

noncomputable def allowedTripleEquiv (c : ι → κ) (I : Finset ι) (n : ℕ) :
    WedgeIndex (Allowed (forbiddenCoordinates c I)) n ≃ TripleIndex c I n :=
  (wedgeFinsetEquiv n).trans ((allowedFinsetEquiv _ n).trans (subsetTripleEquiv c I n))

/-- The finite coefficient module on the exact manuscript triples is canonically isomorphic
to the actual admissible homogeneous exterior submodule. -/
noncomputable def admissibleTripleEquiv (c : ι → κ) (I : Finset ι) (n : ℕ) :
    admissibleDegree (R := R) c I n ≃ₗ[R] (TripleIndex c I n → R) :=
  (admissibleExteriorEquiv c I n).trans ((orderedExteriorEquiv n).trans
    (LinearEquiv.piCongrLeft R (fun _ : TripleIndex c I n => R) (allowedTripleEquiv c I n)))

noncomputable def orderedExteriorBasis {α : Type*} [Fintype α] [LinearOrder α] (n : ℕ) :
    Basis (WedgeIndex α n) R (ExteriorAlgebra.exteriorPower R n (α → R)) :=
  (Pi.basisFun R (WedgeIndex α n)).map (orderedExteriorEquiv n).symm

theorem orderedExteriorBasis_apply {α : Type*} [Fintype α] [LinearOrder α]
    (n : ℕ) (a : WedgeIndex α n) :
    orderedExteriorBasis (R := R) n a = orderedWedge n a := by
  simp only [orderedExteriorBasis, Basis.map_apply, Pi.basisFun_apply]
  exact synthesis_single n a

/-- This `Basis` packages both linear independence and spanning, with the exact allowed
mutable/frozen finite subsets as indices. -/
noncomputable def admissibleTripleBasis (c : ι → κ) (I : Finset ι) (n : ℕ) :
    Basis (TripleIndex c I n) R (admissibleDegree (R := R) c I n) :=
  ((orderedExteriorBasis n).map (admissibleExteriorEquiv c I n).symm).reindex
    (allowedTripleEquiv c I n)

theorem admissibleTripleBasis_apply (c : ι → κ) (I : Finset ι) (n : ℕ)
    (AF : TripleIndex c I n) :
    admissibleTripleBasis (R := R) c I n AF =
      allowedToAdmissible c I n (orderedWedge n ((allowedTripleEquiv c I n).symm AF)) := by
  simp only [admissibleTripleBasis, Basis.reindex_apply, Basis.map_apply,
    orderedExteriorBasis_apply]
  rfl

theorem admissibleTripleBasis_independent (c : ι → κ) (I : Finset ι) (n : ℕ) :
    LinearIndependent R (admissibleTripleBasis (R := R) c I n) :=
  (admissibleTripleBasis c I n).linearIndependent

theorem admissibleTripleBasis_spans (c : ι → κ) (I : Finset ι) (n : ℕ) :
    Submodule.span R (Set.range (admissibleTripleBasis (R := R) c I n)) = ⊤ :=
  (admissibleTripleBasis c I n).span_eq

noncomputable def fixedWeightTripleEquiv (c : ι → κ) (I : Finset ι) (s : ℕ)
    (hs : I.card ≤ s) :
    fixedWeight (R := R) c I s ≃ₗ[R] (TripleIndex c I (s - I.card) → R) :=
  (LinearEquiv.ofEq _ _ (by simp [fixedWeight, hs])).trans
    (admissibleTripleEquiv c I (s - I.card))

omit [Fintype ι] [Fintype κ] [LinearOrder ι] in
theorem tripleIndex_weight (c : ι → κ) (I : Finset ι) (s : ℕ) (hs : I.card ≤ s)
    (AF : TripleIndex c I (s - I.card)) :
    I.card + AF.val.1.card + AF.val.2.card = s := by
  have h := AF.property.2.2
  omega

end BasisEquivalence

#print axioms wedgeFinsetEquiv
#print axioms allowedFinsetEquiv
#print axioms forbidden_disjoint_iff
#print axioms subsetTripleEquiv
#print axioms allowedTripleEquiv
#print axioms admissibleTripleEquiv
#print axioms orderedExteriorBasis
#print axioms orderedExteriorBasis_apply
#print axioms admissibleTripleBasis
#print axioms admissibleTripleBasis_apply
#print axioms admissibleTripleBasis_independent
#print axioms admissibleTripleBasis_spans
#print axioms fixedWeightTripleEquiv
#print axioms tripleIndex_weight
#print axioms extendAllowed_single
#print axioms orderedWedge
#print axioms wedgeCoordinate
#print axioms coordinateAnalysis
#print axioms coordinateSynthesis
#print axioms extendAllowed
#print axioms restrictAllowed
#print axioms extend_orderedWedge
#print axioms allowedToAdmissible_val

end Verification.EvenBasis

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.EvenBasis.Allowed
#print axioms Verification.EvenBasis.TripleIndex
#print axioms Verification.EvenBasis.WedgeIndex
#print axioms Verification.EvenBasis.sumCoordinateOrder
#print axioms Verification.EvenBasis.wedgeIndexDecidableEq
#print axioms Verification.EvenBasis.wedgeIndexFintype
