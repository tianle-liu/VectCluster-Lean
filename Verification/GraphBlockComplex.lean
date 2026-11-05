/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphBlockSquare
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Graph Block Complex

Degreewise augmented independence cochains and their monomial presentation.
All modules and differentials are actual finite-support coefficient modules.
The degree is the cardinality of the independent set, so degree zero is the
empty simplex. No comparison with geometric or Witt cohomology is assumed.
-/

namespace Verification.GraphBlockComplex

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open Verification.GraphBlocks Finset

section Grading

variable (R : Type*) [CommRing R] {α β : Type*}

/-- Coefficients concentrated in one explicitly specified degree. -/
def degreeModule (deg : α → ℕ) (p : ℕ) : Submodule R (α →₀ R) :=
  Finsupp.supported R R {a | deg a = p}

theorem mem_degreeModule (deg : α → ℕ) (p : ℕ) (f : α →₀ R) :
    f ∈ degreeModule R deg p ↔ ∀ a, deg a ≠ p → f a = 0 :=
  Finsupp.mem_supported' _ _

/-- These modules really are free on precisely the basis elements of degree `p`. -/
noncomputable def degreeBasisEquiv (deg : α → ℕ) (p : ℕ) :
    degreeModule R deg p ≃ₗ[R] ({a : α // deg a = p} →₀ R) :=
  Finsupp.supportedEquivFinsupp _

theorem linearCombination_degree (deg : α → ℕ) (v : α → (α →₀ R))
    (hv : ∀ a, v a ∈ degreeModule R deg (deg a + 1))
    (p : ℕ) (f : degreeModule R deg p) :
    Finsupp.linearCombination R v f.val ∈ degreeModule R deg (p+1) := by
  apply (mem_degreeModule R deg (p+1) _).mpr
  intro b hb
  rw [Finsupp.linearCombination_apply, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : deg a = p
  · have hvb := (mem_degreeModule R deg (deg a+1) _).mp (hv a) b (by simpa [ha] using hb)
    simp [hvb]
  · have hfa := (mem_degreeModule R deg p _).mp f.property a ha
    simp [hfa]

variable (deg : α → ℕ) (D : (α →₀ R) →ₗ[R] (α →₀ R))
variable (preserves : ∀ p, ∀ f : degreeModule R deg p, D f.val ∈ degreeModule R deg (p+1))

/-- Restrict an actual differential to its homogeneous source and target. -/
def degreeDifferential (p : ℕ) : degreeModule R deg p →ₗ[R] degreeModule R deg (p+1) where
  toFun f := ⟨D f.val, preserves p f⟩
  map_add' f g := by apply Subtype.ext; exact map_add D _ _
  map_smul' a f := by apply Subtype.ext; exact map_smul D _ _

variable (square : D.comp D = 0)

include square in
theorem degreeDifferential_square (p : ℕ) :
    (degreeDifferential R deg D preserves (p+1)).comp
      (degreeDifferential R deg D preserves p) = 0 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  exact LinearMap.congr_fun square f.val

/-- A genuine degree-indexed cochain complex, with the inherited differential. -/
noncomputable def gradedComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of R (degreeModule R deg p))
    (fun p => ModuleCat.ofHom (degreeDifferential R deg D preserves p))
    (fun p => ModuleCat.hom_ext (degreeDifferential_square R deg D preserves square p))

/-- Reindexing a homogeneous coefficient module along a degree-preserving equivalence. -/
noncomputable def degreeReindex (deg' : β → ℕ) (e : α ≃ β)
    (he : ∀ a, deg' (e a) = deg a) (p : ℕ) :
    degreeModule R deg p ≃ₗ[R] degreeModule R deg' p where
  toFun f := ⟨Finsupp.domLCongr (R := R) e f.val, by
    apply (mem_degreeModule R deg' p _).mpr
    intro b hb
    have hdeg : deg (e.symm b) ≠ p := by simpa only [← he, e.apply_symm_apply] using hb
    exact (mem_degreeModule R deg p _).mp f.property (e.symm b) hdeg⟩
  invFun f := ⟨Finsupp.domLCongr (R := R) e.symm f.val, by
    apply (mem_degreeModule R deg p _).mpr
    intro a ha
    have hdeg : deg' (e a) ≠ p := by simpa only [he] using ha
    exact (mem_degreeModule R deg' p _).mp f.property (e a) hdeg⟩
  left_inv f := by apply Subtype.ext; exact (Finsupp.domLCongr (R := R) e).symm_apply_apply f.val
  right_inv f := by apply Subtype.ext; exact (Finsupp.domLCongr (R := R) e).apply_symm_apply f.val
  map_add' f g := by apply Subtype.ext; exact map_add (Finsupp.domLCongr (R := R) e) _ _
  map_smul' a f := by apply Subtype.ext; exact map_smul (Finsupp.domLCongr (R := R) e) _ _

end Grading

section Graph

universe u

variable (R : Type u) [CommRing R]
variable {V C : Type} [Fintype V] [LinearOrder V] [DecidableEq C]
variable (G : SimpleGraph V) (c : V → C)

/-- Degree of a monomial is its independent-set cardinality. -/
def monomialDegree (x : MonomialIndex G c) : ℕ := x.I.card

/-- Augmented simplex degree is cardinality, including the empty simplex. -/
def blockDegree (b : BlockIndex G c) : ℕ := b.I.card

theorem blockBasis_degree (b : BlockIndex G c) :
    blockBasisDifferential R b ∈ degreeModule R (blockDegree G c) (blockDegree G c b+1) := by
  classical
  unfold blockBasisDifferential
  apply Submodule.sum_mem
  intro i _
  split_ifs with hi
  · apply Finsupp.single_mem_supported
    change (insert i b.I).card = b.I.card+1
    exact Finset.card_insert_of_not_mem hi.2.1
  · exact Submodule.zero_mem _

theorem monomialBasis_degree (x : MonomialIndex G c) :
    monomialBasisDifferential R x ∈ degreeModule R (monomialDegree G c)
      (monomialDegree G c x+1) := by
  classical
  unfold monomialBasisDifferential
  apply Submodule.sum_mem
  intro i _
  split_ifs with hi
  · apply Finsupp.single_mem_supported
    exact addMonomial_degree x i hi
  · exact Submodule.zero_mem _

theorem blockDifferential_degree (p : ℕ) (f : degreeModule R (blockDegree G c) p) :
    blockDifferential R f.val ∈ degreeModule R (blockDegree G c) (p+1) :=
  linearCombination_degree R (blockDegree G c) (blockBasisDifferential R)
    (blockBasis_degree R G c) p f

theorem monomialDifferential_degree (p : ℕ) (f : degreeModule R (monomialDegree G c) p) :
    monomialDifferential R f.val ∈ degreeModule R (monomialDegree G c) (p+1) :=
  linearCombination_degree R (monomialDegree G c) (monomialBasisDifferential R)
    (monomialBasis_degree R G c) p f

/-- The original coefficient equivalence, now in each actual cochain degree. -/
noncomputable def degreeCoefficientEquiv (p : ℕ) :
    degreeModule R (monomialDegree G c) p ≃ₗ[R] degreeModule R (blockDegree G c) p :=
  degreeReindex R (monomialDegree G c) (blockDegree G c) (indexEquiv G c)
    (fun _ => rfl) p

theorem degreeCoefficientEquiv_commutes (p : ℕ) :
    (degreeCoefficientEquiv R G c (p+1)).toLinearMap.comp
      (degreeDifferential R (monomialDegree G c) (monomialDifferential R)
        (monomialDifferential_degree R G c) p) =
    (degreeDifferential R (blockDegree G c) (blockDifferential R)
      (blockDifferential_degree R G c) p).comp (degreeCoefficientEquiv R G c p).toLinearMap := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  exact LinearMap.congr_fun (coefficient_differential_commutes R (G := G) (c := c)) f.val

/-- A simplex of one fixed induced-independence block as a total block index. -/
def simplexToBlock (SF : Finset V × Finset C) (J : SimplexIndex G c SF) : BlockIndex G c :=
  ⟨SF.1, SF.2, J.val, J.property.1, J.property.2⟩

omit [Fintype V] [LinearOrder V] in
theorem simplexToBlock_injective (SF : Finset V × Finset C) :
    Function.Injective (simplexToBlock G c SF) := by
  intro J K h
  apply Subtype.ext
  exact congrArg BlockIndex.I h

/-- The actual independent sets of the fixed induced subgraph, in augmented degrees. -/
def simplexDegree (SF : Finset V × Finset C) (J : SimplexIndex G c SF) : ℕ := J.val.card

def simplexCanAdd (SF : Finset V × Finset C) (J : SimplexIndex G c SF) (i : V) : Prop :=
  i ∈ available c SF.1 SF.2 ∧ i ∉ J.val ∧ G.IsIndepSet ((insert i J.val : Finset V) : Set V)

def addSimplex (SF : Finset V × Finset C) (J : SimplexIndex G c SF) (i : V)
    (hi : simplexCanAdd G c SF J i) : SimplexIndex G c SF :=
  ⟨insert i J.val, hi.2.2, by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi.1
    · exact J.property.2 hj⟩

omit [Fintype V] in
theorem simplexToBlock_add (SF : Finset V × Finset C) (J : SimplexIndex G c SF) (i : V)
    (hi : simplexCanAdd G c SF J i) :
    simplexToBlock G c SF (addSimplex G c SF J i hi) =
      addBlock (simplexToBlock G c SF J) i hi := by
  apply BlockIndex.ext <;> rfl

/-- Literal augmented simplicial incidence within the selected block. -/
noncomputable def simplexBasisDifferential (SF : Finset V × Finset C)
    (J : SimplexIndex G c SF) : SimplexIndex G c SF →₀ R := by
  classical
  exact ∑ i : V, if hi : simplexCanAdd G c SF J i then
    Finsupp.single (addSimplex G c SF J i hi) (incidence R J.val i) else 0

noncomputable def simplexDifferential (SF : Finset V × Finset C) :
    (SimplexIndex G c SF →₀ R) →ₗ[R] (SimplexIndex G c SF →₀ R) :=
  Finsupp.linearCombination R (simplexBasisDifferential R G c SF)

/-- The literal inclusion of this simplex coefficient module into all blocks. -/
noncomputable def simplexEmbedding (SF : Finset V × Finset C) :
    (SimplexIndex G c SF →₀ R) →ₗ[R] (BlockIndex G c →₀ R) :=
  Finsupp.lmapDomain R R (simplexToBlock G c SF)

omit [Fintype V] [LinearOrder V] in
theorem simplexEmbedding_injective (SF : Finset V × Finset C) :
    Function.Injective (simplexEmbedding R G c SF) :=
  Finsupp.mapDomain_injective (simplexToBlock_injective G c SF)

omit [Fintype V] [LinearOrder V] in
theorem simplexEmbedding_single (SF : Finset V × Finset C) (J : SimplexIndex G c SF) (r : R) :
    simplexEmbedding R G c SF (Finsupp.single J r) = Finsupp.single (simplexToBlock G c SF J) r :=
  Finsupp.mapDomain_single

theorem simplexBasis_transport (SF : Finset V × Finset C) (J : SimplexIndex G c SF) :
    simplexEmbedding R G c SF (simplexBasisDifferential R G c SF J) =
      blockBasisDifferential R (simplexToBlock G c SF J) := by
  classical
  unfold simplexBasisDifferential blockBasisDifferential
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : simplexCanAdd G c SF J i
  · have hb : CanAddBlock (simplexToBlock G c SF J) i := hi
    simp only [dif_pos hi, dif_pos hb, simplexEmbedding_single, simplexToBlock_add]
    rfl
  · have hb : ¬ CanAddBlock (simplexToBlock G c SF J) i := hi
    simp only [dif_neg hi, dif_neg hb, map_zero]

theorem simplexDifferential_embedding (SF : Finset V × Finset C) :
    (simplexEmbedding R G c SF).comp (simplexDifferential R G c SF) =
      (blockDifferential R).comp (simplexEmbedding R G c SF) := by
  apply Finsupp.lhom_ext
  intro J r
  simp only [LinearMap.comp_apply, simplexDifferential, Finsupp.linearCombination_single,
    map_smul, simplexEmbedding_single, blockDifferential, simplexBasis_transport]

theorem simplexBasis_degree (SF : Finset V × Finset C) (J : SimplexIndex G c SF) :
    simplexBasisDifferential R G c SF J ∈ degreeModule R (simplexDegree G c SF)
      (simplexDegree G c SF J+1) := by
  classical
  unfold simplexBasisDifferential
  apply Submodule.sum_mem
  intro i _
  split_ifs with hi
  · apply Finsupp.single_mem_supported
    change (insert i J.val).card = J.val.card+1
    exact Finset.card_insert_of_not_mem hi.2.1
  · exact Submodule.zero_mem _

theorem simplexDifferential_degree (SF : Finset V × Finset C) (p : ℕ)
    (f : degreeModule R (simplexDegree G c SF) p) :
    simplexDifferential R G c SF f.val ∈ degreeModule R (simplexDegree G c SF) (p+1) :=
  linearCombination_degree R (simplexDegree G c SF) (simplexBasisDifferential R G c SF)
    (simplexBasis_degree R G c SF) p f

/-- Projection onto one fixed `(S,F)` simplex block. -/
noncomputable def simplexProjection (SF : Finset V × Finset C) :
    (BlockIndex G c →₀ R) →ₗ[R] (SimplexIndex G c SF →₀ R) :=
  Finsupp.lcomapDomain (R := R) (M := R) (simplexToBlock G c SF) (simplexToBlock_injective G c SF)

omit [Fintype V] [LinearOrder V] in
theorem simplexProjection_apply (SF : Finset V × Finset C)
    (f : BlockIndex G c →₀ R) (J : SimplexIndex G c SF) :
    simplexProjection R G c SF f J = f (simplexToBlock G c SF J) := rfl

omit [Fintype V] [LinearOrder V] in
theorem simplexProjection_embedding (SF : Finset V × Finset C) :
    (simplexProjection R G c SF).comp (simplexEmbedding R G c SF) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  ext J
  change Finsupp.mapDomain (simplexToBlock G c SF) f (simplexToBlock G c SF J) = f J
  exact Finsupp.mapDomain_apply (simplexToBlock_injective G c SF) f J

omit [Fintype V] [LinearOrder V] in
theorem simplexProjection_single (SF : Finset V × Finset C) (J : SimplexIndex G c SF) (r : R) :
    simplexProjection R G c SF (Finsupp.single (simplexToBlock G c SF J) r) =
      Finsupp.single J r :=
  Finsupp.comapDomain_single _ _ _ _

omit [Fintype V] [LinearOrder V] in
theorem simplexProjection_single_other (SF : Finset V × Finset C)
    (b : BlockIndex G c) (r : R) (hb : (b.S,b.F) ≠ SF) :
    simplexProjection R G c SF (Finsupp.single b r) = 0 := by
  classical
  ext J
  rw [simplexProjection_apply]
  have hne : b ≠ simplexToBlock G c SF J := by
    intro he
    apply hb
    exact congrArg (fun z : BlockIndex G c => (z.S,z.F)) he
  simp [hne, Ne.symm hne]

omit [Fintype V] [LinearOrder V] in
theorem block_has_simplex (SF : Finset V × Finset C) (b : BlockIndex G c)
    (hb : (b.S,b.F) = SF) : ∃ J : SimplexIndex G c SF, simplexToBlock G c SF J = b := by
  subst SF
  refine ⟨⟨b.I, b.independent, b.subset⟩, ?_⟩
  apply BlockIndex.ext <;> rfl

theorem simplexProjection_basisDifferential (SF : Finset V × Finset C) (b : BlockIndex G c) :
    simplexProjection R G c SF (blockBasisDifferential R b) =
      simplexDifferential R G c SF (simplexProjection R G c SF (Finsupp.single b 1)) := by
  classical
  by_cases hb : (b.S,b.F) = SF
  · obtain ⟨J, rfl⟩ := block_has_simplex G c SF b hb
    rw [simplexProjection_single, simplexDifferential, Finsupp.linearCombination_single, one_smul,
      ← simplexBasis_transport R G c SF J]
    exact LinearMap.congr_fun (simplexProjection_embedding R G c SF) _
  · rw [simplexProjection_single_other R G c SF b 1 hb, map_zero]
    unfold blockBasisDifferential
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with hi
    · exact simplexProjection_single_other R G c SF (addBlock b i hi) _ hb
    · exact map_zero _

theorem simplexProjection_differential (SF : Finset V × Finset C) :
    (simplexProjection R G c SF).comp (blockDifferential R) =
      (simplexDifferential R G c SF).comp (simplexProjection R G c SF) := by
  apply Finsupp.lhom_ext
  intro b r
  simp only [LinearMap.comp_apply, blockDifferential, Finsupp.linearCombination_single,
    map_smul, simplexProjection_basisDifferential]
  have he : Finsupp.single b r = r • Finsupp.single b 1 := by simp
  rw [he, map_smul, map_smul]

section Family

variable [Fintype C]

/-- Actual finite product of the independent-set coefficient modules of all labeled blocks. -/
noncomputable def blockFamilyEquiv : (BlockIndex G c →₀ R) ≃ₗ[R]
    ((SF : Finset V × Finset C) → (SimplexIndex G c SF →₀ R)) :=
  (Finsupp.domLCongr (blockSigmaEquiv G c)).trans (Finsupp.sigmaFinsuppLEquivPiFinsupp R)

omit [LinearOrder V] in
theorem blockFamilyEquiv_apply (f : BlockIndex G c →₀ R) (SF : Finset V × Finset C) :
    blockFamilyEquiv R G c f SF = simplexProjection R G c SF f := by
  ext J
  rfl

/-- A genuine finite product in each cochain degree. -/
noncomputable def degreeFamilyEquiv (p : ℕ) :
    degreeModule R (blockDegree G c) p ≃ₗ[R]
      ((SF : Finset V × Finset C) → degreeModule R (simplexDegree G c SF) p) where
  toFun f SF := ⟨blockFamilyEquiv R G c f.val SF, by
    apply (mem_degreeModule R (simplexDegree G c SF) p _).mpr
    intro J hJ
    exact (mem_degreeModule R (blockDegree G c) p _).mp f.property (simplexToBlock G c SF J) hJ⟩
  invFun f := ⟨(blockFamilyEquiv R G c).symm (fun SF => (f SF).val), by
    apply (mem_degreeModule R (blockDegree G c) p _).mpr
    intro b hb
    exact (mem_degreeModule R (simplexDegree G c (b.S,b.F)) p _).mp (f (b.S,b.F)).property
      ⟨b.I,b.independent,b.subset⟩ hb⟩
  left_inv f := by
    apply Subtype.ext
    exact (blockFamilyEquiv R G c).symm_apply_apply f.val
  right_inv f := by
    funext SF
    apply Subtype.ext
    exact congrFun ((blockFamilyEquiv R G c).apply_symm_apply (fun SF => (f SF).val)) SF
  map_add' f g := by
    funext SF
    apply Subtype.ext
    exact congrFun (map_add (blockFamilyEquiv R G c) f.val g.val) SF
  map_smul' a f := by
    funext SF
    apply Subtype.ext
    exact congrFun (map_smul (blockFamilyEquiv R G c) a f.val) SF

theorem degreeFamilyEquiv_differential (p : ℕ) (f : degreeModule R (blockDegree G c) p)
    (SF : Finset V × Finset C) :
    degreeFamilyEquiv R G c (p+1)
      (degreeDifferential R (blockDegree G c) (blockDifferential R)
        (blockDifferential_degree R G c) p f) SF =
    degreeDifferential R (simplexDegree G c SF) (simplexDifferential R G c SF)
      (simplexDifferential_degree R G c SF) p (degreeFamilyEquiv R G c p f SF) := by
  apply Subtype.ext
  change blockFamilyEquiv R G c (blockDifferential R f.val) SF =
    simplexDifferential R G c SF (blockFamilyEquiv R G c f.val SF)
  simp only [blockFamilyEquiv_apply]
  exact LinearMap.congr_fun (simplexProjection_differential R G c SF) f.val

end Family

/-- The monomial differential squares to zero by the proved actual conjugation. -/
theorem monomialDifferential_square :
    (monomialDifferential (G := G) (c := c) R).comp (monomialDifferential R) = 0 := by
  apply LinearMap.ext
  intro f
  apply (coefficientEquiv R G c).injective
  have hc (x : MonomialIndex G c →₀ R) :=
    LinearMap.congr_fun (coefficient_differential_commutes R (G := G) (c := c)) x
  change coefficientEquiv R G c (monomialDifferential R (monomialDifferential R f)) =
    coefficientEquiv R G c 0
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hc
  rw [hc, hc, map_zero]
  exact LinearMap.congr_fun (Verification.GraphBlockSquare.blockDifferential_squared R
    (G := G) (c := c)) _

/-- The independently defined incidence differential of each induced complex squares to zero. -/
theorem simplexDifferential_square (SF : Finset V × Finset C) :
    (simplexDifferential R G c SF).comp (simplexDifferential R G c SF) = 0 := by
  apply LinearMap.ext
  intro f
  apply (simplexEmbedding_injective R G c SF)
  have hc (x : SimplexIndex G c SF →₀ R) :=
    LinearMap.congr_fun (simplexDifferential_embedding R G c SF) x
  change simplexEmbedding R G c SF (simplexDifferential R G c SF
    (simplexDifferential R G c SF f)) = simplexEmbedding R G c SF 0
  simp only [LinearMap.comp_apply] at hc
  rw [hc, hc, map_zero]
  exact LinearMap.congr_fun (Verification.GraphBlockSquare.blockDifferential_squared R
    (G := G) (c := c)) _

/-- Actual monomial cochain complex, with degree `|I|`. -/
noncomputable def monomialComplex : CochainComplex (ModuleCat R) ℕ :=
  gradedComplex R (monomialDegree G c) (monomialDifferential R)
    (monomialDifferential_degree R G c) (monomialDifferential_square R G c)

/-- Actual direct-block cochain complex, with augmented simplex degree `|I|`. -/
noncomputable def blockComplex : CochainComplex (ModuleCat R) ℕ :=
  gradedComplex R (blockDegree G c) (blockDifferential R)
    (blockDifferential_degree R G c)
    (Verification.GraphBlockSquare.blockDifferential_squared R (G := G) (c := c))

/-- Actual augmented independence cochains of `Ind(G[S \ c⁻¹(F)])`. -/
noncomputable def simplexComplex (SF : Finset V × Finset C) : CochainComplex (ModuleCat R) ℕ :=
  gradedComplex R (simplexDegree G c SF) (simplexDifferential R G c SF)
    (simplexDifferential_degree R G c SF) (simplexDifferential_square R G c SF)

/-- The basis reorganization is now an isomorphism of actual cochain complexes. -/
noncomputable def monomialBlockIso : monomialComplex R G c ≅ blockComplex R G c :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (degreeCoefficientEquiv R G c p).toModuleIso)
    (by
      intro p q hpq
      have he : p+1 = q := hpq
      subst q
      simp only [monomialComplex, blockComplex, gradedComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      exact (degreeCoefficientEquiv_commutes R G c p).symm)

/-- Homology transport between the two constructed algebraic complexes. -/
noncomputable def monomialBlockHomologyIso (p : ℕ) :
    (monomialComplex R G c).homology p ≅ (blockComplex R G c).homology p :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) p).mapIso
    (monomialBlockIso R G c)

section FamilyComplex

variable [Fintype C]

/-- Coordinatewise simplicial incidence on the finite product of degree modules. -/
noncomputable def familyDegreeDifferential (p : ℕ) :
    ((SF : Finset V × Finset C) → degreeModule R (simplexDegree G c SF) p) →ₗ[R]
    ((SF : Finset V × Finset C) → degreeModule R (simplexDegree G c SF) (p+1)) :=
  LinearMap.pi (fun SF =>
    (degreeDifferential R (simplexDegree G c SF) (simplexDifferential R G c SF)
      (simplexDifferential_degree R G c SF) p).comp (LinearMap.proj SF))

omit [Fintype C] in
theorem familyDegreeDifferential_square (p : ℕ) :
    (familyDegreeDifferential R G c (p+1)).comp (familyDegreeDifferential R G c p) = 0 := by
  apply LinearMap.ext
  intro f
  funext SF
  apply Subtype.ext
  exact LinearMap.congr_fun (simplexDifferential_square R G c SF) (f SF).val

/-- The finite product of the actual augmented independence cochain complexes. -/
noncomputable def familyComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of R
    ((SF : Finset V × Finset C) → degreeModule R (simplexDegree G c SF) p))
    (fun p => ModuleCat.ofHom (familyDegreeDifferential R G c p))
    (fun p => ModuleCat.hom_ext (familyDegreeDifferential_square R G c p))

/-- Degreewise splitting into all fixed induced-independence complexes. -/
noncomputable def blockFamilyIso : blockComplex R G c ≅ familyComplex R G c :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (degreeFamilyEquiv R G c p).toModuleIso)
    (by
      intro p q hpq
      have he : p+1 = q := hpq
      subst q
      simp only [blockComplex, gradedComplex, familyComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      funext SF
      exact (degreeFamilyEquiv_differential R G c p f SF).symm)

/-- The complete uncompressed algebraic block decomposition as a chain isomorphism. -/
noncomputable def monomialFamilyIso : monomialComplex R G c ≅ familyComplex R G c :=
  (monomialBlockIso R G c).trans (blockFamilyIso R G c)

/-- The projection to one actual simplex complex. -/
noncomputable def familyProjection (SF : Finset V × Finset C) :
    familyComplex R G c ⟶ simplexComplex R G c SF :=
  CochainComplex.ofHom _ _
    (fun p => ModuleCat.hom_ext (familyDegreeDifferential_square R G c p)) _ _
    (fun p => ModuleCat.hom_ext (degreeDifferential_square R (simplexDegree G c SF)
      (simplexDifferential R G c SF) (simplexDifferential_degree R G c SF)
      (simplexDifferential_square R G c SF) p))
    (fun _ => ModuleCat.ofHom (LinearMap.proj SF)) (fun _ => rfl)

/-- This cone is proved to be a categorical product of the individual complexes. -/
noncomputable def familyIsProduct : CategoryTheory.Limits.IsLimit
    (CategoryTheory.Limits.Fan.mk (familyComplex R G c) (familyProjection R G c)) := by
  apply HomologicalComplex.isLimitOfEval
  intro p
  refine (CategoryTheory.Limits.isLimitMapConeFanMkEquiv
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) p)
    (simplexComplex R G c) (familyProjection R G c)).symm ?_
  exact ModuleCat.productConeIsLimit
    (fun SF : Finset V × Finset C => ModuleCat.of R (degreeModule R (simplexDegree G c SF) p))

/-- The homology of the constructed product is the product of actual simplex homology modules. -/
noncomputable def familyHomologyProductIso (p : ℕ) :
    (familyComplex R G c).homology p ≅ ModuleCat.of R
      ((SF : Finset V × Finset C) → (simplexComplex R G c SF).homology p) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) p
  letI : CategoryTheory.Limits.PreservesLimit
      (CategoryTheory.Discrete.functor (simplexComplex R G c)) H :=
    CategoryTheory.Limits.preservesProduct_of_preservesBiproduct (f := simplexComplex R G c) H
  let hlim := CategoryTheory.Limits.isLimitFanMkObjOfIsLimit H
    (simplexComplex R G c) (familyProjection R G c) (familyIsProduct R G c)
  exact hlim.conePointUniqueUpToIso (ModuleCat.productConeIsLimit
    (fun SF => (simplexComplex R G c SF).homology p))

/-- The uncompressed `(S,F)` formula at the level of actual algebraic cohomology. -/
noncomputable def uncompressedHomologyIso (p : ℕ) :
    (monomialComplex R G c).homology p ≅ ModuleCat.of R
      ((SF : Finset V × Finset C) → (simplexComplex R G c SF).homology p) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) p).mapIso
    (monomialFamilyIso R G c)).trans (familyHomologyProductIso R G c p)

end FamilyComplex

end Graph

#print axioms degreeModule
#print axioms mem_degreeModule
#print axioms degreeBasisEquiv
#print axioms linearCombination_degree
#print axioms degreeDifferential
#print axioms degreeDifferential_square
#print axioms gradedComplex
#print axioms degreeReindex
#print axioms monomialDegree
#print axioms blockDegree
#print axioms blockBasis_degree
#print axioms monomialBasis_degree
#print axioms blockDifferential_degree
#print axioms monomialDifferential_degree
#print axioms degreeCoefficientEquiv
#print axioms degreeCoefficientEquiv_commutes

#print axioms simplexToBlock
#print axioms simplexToBlock_injective
#print axioms simplexDegree
#print axioms simplexCanAdd
#print axioms addSimplex
#print axioms simplexToBlock_add
#print axioms simplexBasisDifferential
#print axioms simplexDifferential
#print axioms simplexEmbedding
#print axioms simplexEmbedding_injective
#print axioms simplexEmbedding_single
#print axioms simplexBasis_transport
#print axioms simplexDifferential_embedding
#print axioms simplexBasis_degree
#print axioms simplexDifferential_degree

#print axioms simplexProjection
#print axioms simplexProjection_apply
#print axioms simplexProjection_embedding
#print axioms simplexProjection_single
#print axioms simplexProjection_single_other
#print axioms block_has_simplex
#print axioms simplexProjection_basisDifferential
#print axioms simplexProjection_differential
#print axioms blockFamilyEquiv
#print axioms blockFamilyEquiv_apply
#print axioms degreeFamilyEquiv
#print axioms degreeFamilyEquiv_differential

#print axioms monomialDifferential_square
#print axioms simplexDifferential_square
#print axioms monomialComplex
#print axioms blockComplex
#print axioms simplexComplex
#print axioms monomialBlockIso
#print axioms monomialBlockHomologyIso
#print axioms familyDegreeDifferential
#print axioms familyDegreeDifferential_square
#print axioms familyComplex
#print axioms blockFamilyIso
#print axioms monomialFamilyIso
#print axioms familyProjection
#print axioms familyIsProduct
#print axioms familyHomologyProductIso
#print axioms uncompressedHomologyIso

end Verification.GraphBlockComplex
