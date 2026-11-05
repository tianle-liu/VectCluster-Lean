/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Tactic.Abel

/-!
# Cancellation in arbitrary module complexes

This file constructs a genuine `HomologicalComplex` and `HomotopyEquiv`
for cancellation in all degrees, as needed by `lem:even-reduction`.
The input is an actual degree-reversing partial contraction `h` with
`h² = 0` and `h d h = h`. The surviving projection is constructed as
`1 - d h - h d`; its fixed-point modules form the residual complex.
No homotopy equivalence, residual differential, or geometric conclusion
is assumed. Identifying the manuscript's filtered integer pivots with
this contraction remains a separate application.
-/

namespace Verification.ComplexCancellation

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

variable {ι : Type*} {c : ComplexShape ι}
variable {R : Type*} [Ring R]
variable (K : HomologicalComplex (ModuleCat R) c)

/-- Algebraic data of the chosen contractible pairs, in every degree. -/
structure PartialContraction where
  hom : ∀ i j, K.X i ⟶ K.X j
  shape : ∀ i j, ¬ c.Rel j i → hom i j = 0
  square : ∀ i j k, hom i j ≫ hom j k = 0
  regular : ∀ i j, hom i j ≫ K.d j i ≫ hom i j = hom i j

variable {K} (h : PartialContraction K)

/-- The contractible-part endomorphism `d h + h d`. -/
noncomputable def contractiblePart : K ⟶ K := Homotopy.nullHomotopicMap h.hom

/-- The complementary chain projection; its chain property is constructed. -/
noncomputable def survivorProjection : K ⟶ K := 𝟙 K - contractiblePart h

theorem contractiblePart_idempotent : contractiblePart h ≫ contractiblePart h =
    contractiblePart h := by
  apply HomologicalComplex.Hom.ext
  funext i
  change (K.d i (c.next i) ≫ h.hom (c.next i) i +
      h.hom i (c.prev i) ≫ K.d (c.prev i) i) ≫
    (K.d i (c.next i) ≫ h.hom (c.next i) i +
      h.hom i (c.prev i) ≫ K.d (c.prev i) i) = _
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
  rw [h.regular (c.next i) i]
  rw [← Category.assoc (h.hom (c.next i) i) (h.hom i (c.prev i)), h.square,
    zero_comp, comp_zero, zero_add]
  rw [K.d_comp_d_assoc, zero_comp, comp_zero, add_zero]
  have he := congrArg (fun f => f ≫ K.d (c.prev i) i) (h.regular i (c.prev i))
  simp only [Category.assoc] at he
  rw [he]
  rfl

theorem survivorProjection_idempotent : survivorProjection h ≫ survivorProjection h =
    survivorProjection h := by
  simp only [survivorProjection, Preadditive.sub_comp, Preadditive.comp_sub,
    Category.id_comp, Category.comp_id, contractiblePart_idempotent]
  abel

/-- The actual surviving module in a given degree. -/
noncomputable def survivorModule (i : ι) : Submodule R (K.X i) where
  carrier := {x | (survivorProjection h).f i x = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (survivorProjection h).f i x = x at hx
    change (survivorProjection h).f i y = y at hy
    change (survivorProjection h).f i (x + y) = x + y
    rw [map_add, hx, hy]
  smul_mem' := by
    intro a x hx
    change (survivorProjection h).f i x = x at hx
    change (survivorProjection h).f i (a • x) = a • x
    rw [map_smul, hx]

theorem differential_preserves_survivors (i j : ι) (x : survivorModule h i) :
    K.d i j x.val ∈ survivorModule h j := by
  change (survivorProjection h).f j (K.d i j x.val) = K.d i j x.val
  have he := congrArg (fun f : K.X i ⟶ K.X j => f x.val)
    ((survivorProjection h).comm i j)
  have hx : (survivorProjection h).f i x.val = x.val := x.property
  simpa only [ModuleCat.comp_apply, hx] using he.symm

/-- Restriction of the original differential, with no assumed square-zero law. -/
noncomputable def survivorDifferential (i j : ι) : survivorModule h i →ₗ[R] survivorModule h j where
  toFun x := ⟨K.d i j x.val, differential_preserves_survivors h i j x⟩
  map_add' x y := by apply Subtype.ext; exact map_add (K.d i j).hom _ _
  map_smul' a x := by apply Subtype.ext; exact map_smul (K.d i j).hom _ _

/-- The residual complex, supported in exactly the same arbitrary complex shape. -/
noncomputable def survivorComplex : HomologicalComplex (ModuleCat R) c where
  X i := ModuleCat.of R (survivorModule h i)
  d i j := ModuleCat.ofHom (survivorDifferential h i j)
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change K.d i j x.val = 0
    rw [K.shape i j hij]
    rfl
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change K.d j k (K.d i j x.val) = 0
    have he := congrArg (fun f : K.X i ⟶ K.X k => f x.val) (K.d_comp_d i j k)
    exact he

/-- The surviving subcomplex is included by the actual subtype maps. -/
noncomputable def survivorInclusion : survivorComplex h ⟶ K where
  f i := ModuleCat.ofHom (survivorModule h i).subtype
  comm' i j _ := by
    apply ModuleCat.hom_ext
    rfl

/-- The constructed projection lands in the surviving submodule. -/
noncomputable def survivorRetraction : K ⟶ survivorComplex h where
  f i := ModuleCat.ofHom {
    toFun x := ⟨(survivorProjection h).f i x, by
      have he := congrArg (fun f : K ⟶ K => f.f i x) (survivorProjection_idempotent h)
      exact he⟩
    map_add' x y := by apply Subtype.ext; exact map_add ((survivorProjection h).f i).hom _ _
    map_smul' a x := by apply Subtype.ext; exact map_smul ((survivorProjection h).f i).hom _ _ }
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : K.X i ⟶ K.X j => f x) ((survivorProjection h).comm i j)

theorem retraction_inclusion : survivorRetraction h ≫ survivorInclusion h =
    survivorProjection h := by
  apply HomologicalComplex.Hom.ext
  funext i
  rfl

theorem inclusion_retraction : survivorInclusion h ≫ survivorRetraction h =
    𝟙 (survivorComplex h) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact x.property

/-- Explicit homotopy `-h` from the surviving projection to the identity. -/
noncomputable def projectionHomotopy : Homotopy (survivorProjection h) (𝟙 K) where
  hom i j := -h.hom i j
  zero i j hij := by rw [h.shape i j hij, neg_zero]
  comm i := by
    change (𝟙 (K.X i) - (dNext i h.hom + prevD i h.hom)) =
      dNext i (fun i j => -h.hom i j) + prevD i (fun i j => -h.hom i j) + 𝟙 (K.X i)
    rw [show (fun i j => -h.hom i j) = -h.hom from rfl, map_neg, map_neg]
    abel

/-- Cancellation in every degree as a genuine mathlib homotopy equivalence. -/
noncomputable def cancellation : HomotopyEquiv K (survivorComplex h) where
  hom := survivorRetraction h
  inv := survivorInclusion h
  homotopyHomInvId := by rw [retraction_inclusion]; exact projectionHomotopy h
  homotopyInvHomId := Homotopy.ofEq (inclusion_retraction h)

section SinglePivot

/-- A degree-reversing family supported at one selected pivot. -/
noncomputable def singleHom (a b : ι) (H : K.X b ⟶ K.X a) :
    ∀ i j, K.X i ⟶ K.X j := by
  classical
  intro i j
  exact if hi : i = b then
    if hj : j = a then eqToHom (congrArg K.X hi) ≫ H ≫ eqToHom (congrArg K.X hj.symm)
    else 0
    else 0

/-- A single normalized pivot supplies a contraction for the entire complex. -/
noncomputable def singleContraction (a b : ι) (hab : a ≠ b) (hr : c.Rel a b)
    (H : K.X b ⟶ K.X a) (hH : H ≫ K.d a b ≫ H = H) : PartialContraction K where
  hom := singleHom a b H
  shape i j hij := by
    classical
    by_cases hi : i = b
    · subst i
      by_cases hj : j = a
      · subst j
        exact False.elim (hij hr)
      · simp [singleHom, hj]
    · simp [singleHom, hi]
  square i j k := by
    classical
    by_cases hi : i = b
    · subst i
      by_cases hj : j = a
      · subst j
        simp [singleHom, hab]
      · simp [singleHom, hj]
    · simp [singleHom, hi]
  regular i j := by
    classical
    by_cases hi : i = b
    · subst i
      by_cases hj : j = a
      · subst j
        simpa [singleHom] using hH
      · simp [singleHom, hj]
    · simp [singleHom, hi]

/-- The source-degree projection is the usual elimination formula. -/
theorem single_projection_source (a b : ι) (hab : a ≠ b) (hr : c.Rel a b)
    (H : K.X b ⟶ K.X a) (hH : H ≫ K.d a b ≫ H = H) :
    (survivorProjection (singleContraction a b hab hr H hH)).f a =
      𝟙 (K.X a) - K.d a b ≫ H := by
  change 𝟙 (K.X a) - (dNext a (singleHom a b H) + prevD a (singleHom a b H)) = _
  rw [dNext_eq _ hr]
  simp [prevD, singleHom, hab]

/-- The target-degree projection subtracts the image of the inverse pivot. -/
theorem single_projection_target (a b : ι) (hab : a ≠ b) (hr : c.Rel a b)
    (H : K.X b ⟶ K.X a) (hH : H ≫ K.d a b ≫ H = H) :
    (survivorProjection (singleContraction a b hab hr H hH)).f b =
      𝟙 (K.X b) - H ≫ K.d a b := by
  change 𝟙 (K.X b) - (dNext b (singleHom a b H) + prevD b (singleHom a b H)) = _
  rw [prevD_eq _ hr]
  simp [dNext, singleHom, Ne.symm hab]

/-- Other chain groups are untouched, however long the surrounding complex is. -/
theorem single_projection_other (a b : ι) (hab : a ≠ b) (hr : c.Rel a b)
    (H : K.X b ⟶ K.X a) (hH : H ≫ K.d a b ≫ H = H)
    (i : ι) (hia : i ≠ a) (hib : i ≠ b) :
    (survivorProjection (singleContraction a b hab hr H hH)).f i = 𝟙 (K.X i) := by
  change 𝟙 (K.X i) - (dNext i (singleHom a b H) + prevD i (singleHom a b H)) = _
  simp [dNext, prevD, singleHom, hia, hib]

/-- The residual chain module equals the full original module away from the pivot degrees. -/
theorem survivorModule_other (a b : ι) (hab : a ≠ b) (hr : c.Rel a b)
    (H : K.X b ⟶ K.X a) (hH : H ≫ K.d a b ≫ H = H)
    (i : ι) (hia : i ≠ a) (hib : i ≠ b) :
    survivorModule (singleContraction a b hab hr H hH) i = ⊤ := by
  apply Submodule.ext
  intro x
  change ((survivorProjection (singleContraction a b hab hr H hH)).f i x = x) ↔ True
  rw [single_projection_other a b hab hr H hH i hia hib]
  simp

variable {M N : ModuleCat R}

/-- The inverse pivot, inserted into the full chain groups. -/
noncomputable def pivotHom (a b : ι) (A : M ≅ N)
    (inc : M ⟶ K.X a) (proj : K.X b ⟶ N) : K.X b ⟶ K.X a :=
  proj ≫ A.inv ≫ inc

/-- Only the literal invertible matrix block is assumed; the regularity is proved. -/
theorem pivotHom_regular (a b : ι) (A : M ≅ N)
    (inc : M ⟶ K.X a) (proj : K.X b ⟶ N)
    (pivot : inc ≫ K.d a b ≫ proj = A.hom) :
    pivotHom a b A inc proj ≫ K.d a b ≫ pivotHom a b A inc proj =
      pivotHom a b A inc proj := by
  dsimp only [pivotHom]
  calc
    (proj ≫ A.inv ≫ inc) ≫ K.d a b ≫ (proj ≫ A.inv ≫ inc) =
        proj ≫ A.inv ≫ (inc ≫ K.d a b ≫ proj) ≫ A.inv ≫ inc := by
      simp only [Category.assoc]
    _ = proj ≫ A.inv ≫ A.hom ≫ A.inv ≫ inc := by rw [pivot]
    _ = proj ≫ A.inv ≫ inc := by simp

/-- The chosen inverse block becomes a normalized contraction without any two-term truncation. -/
noncomputable def pivotContraction (a b : ι) (hab : a ≠ b) (hr : c.Rel a b)
    (A : M ≅ N) (inc : M ⟶ K.X a) (proj : K.X b ⟶ N)
    (pivot : inc ≫ K.d a b ≫ proj = A.hom) : PartialContraction K :=
  singleContraction a b hab hr (pivotHom a b A inc proj)
    (pivotHom_regular a b A inc proj pivot)

/-- Genuine all-degree chain-homotopy equivalence cancelling an invertible pivot. -/
noncomputable def pivotCancellation (a b : ι) (hab : a ≠ b) (hr : c.Rel a b)
    (A : M ≅ N) (inc : M ⟶ K.X a) (proj : K.X b ⟶ N)
    (pivot : inc ≫ K.d a b ≫ proj = A.hom) :
    HomotopyEquiv K (survivorComplex (pivotContraction a b hab hr A inc proj pivot)) :=
  cancellation _

/-- The selected source summand is actually removed by the constructed projection. -/
theorem pivot_projection_kills_source (a b : ι) (hab : a ≠ b) (hr : c.Rel a b)
    (A : M ≅ N) (inc : M ⟶ K.X a) (proj : K.X b ⟶ N)
    (pivot : inc ≫ K.d a b ≫ proj = A.hom) :
    inc ≫ (survivorProjection (pivotContraction a b hab hr A inc proj pivot)).f a = 0 := by
  change inc ≫ (survivorProjection (singleContraction a b hab hr _ _)).f a = 0
  rw [single_projection_source, Preadditive.comp_sub, Category.comp_id]
  have he := congrArg (fun f => f ≫ A.inv ≫ inc) pivot
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at he
  change inc - inc ≫ K.d a b ≫ (proj ≫ A.inv ≫ inc) = 0
  rw [he, sub_self]

/-- The selected target coordinate vanishes on every survivor. -/
theorem pivot_projection_kills_target (a b : ι) (hab : a ≠ b) (hr : c.Rel a b)
    (A : M ≅ N) (inc : M ⟶ K.X a) (proj : K.X b ⟶ N)
    (pivot : inc ≫ K.d a b ≫ proj = A.hom) :
    (survivorProjection (pivotContraction a b hab hr A inc proj pivot)).f b ≫ proj = 0 := by
  change (survivorProjection (singleContraction a b hab hr _ _)).f b ≫ proj = 0
  rw [single_projection_target, Preadditive.sub_comp, Category.id_comp]
  have he := congrArg (fun f => proj ≫ A.inv ≫ f) pivot
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at he
  change proj - (proj ≫ A.inv ≫ inc) ≫ K.d a b ≫ proj = 0
  simp only [Category.assoc]
  rw [he, sub_self]

end SinglePivot

#print axioms contractiblePart
#print axioms survivorProjection
#print axioms contractiblePart_idempotent
#print axioms survivorProjection_idempotent
#print axioms survivorModule
#print axioms differential_preserves_survivors
#print axioms survivorDifferential
#print axioms survivorComplex
#print axioms survivorInclusion
#print axioms survivorRetraction
#print axioms retraction_inclusion
#print axioms inclusion_retraction
#print axioms projectionHomotopy
#print axioms cancellation

#print axioms singleHom
#print axioms singleContraction
#print axioms pivotHom
#print axioms pivotHom_regular
#print axioms pivotContraction
#print axioms pivotCancellation

#print axioms single_projection_source
#print axioms single_projection_target
#print axioms single_projection_other
#print axioms survivorModule_other

#print axioms pivot_projection_kills_source
#print axioms pivot_projection_kills_target

end Verification.ComplexCancellation

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.ComplexCancellation.PartialContraction
