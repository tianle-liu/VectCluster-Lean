/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphSmallCoverTF
import Verification.GraphOrderApplications
import Verification.GraphChainTF

/-!
# Graph Cover Theorem

Complete graph-cover theorem in the original vertex order: an actual
homotopy equivalence to a finite free complex supported in [-a,0], and all-
induced integral chain-homology freeness when a is at most two.
-/

namespace Verification.GraphCoverTheorem

open Classical CategoryTheory CategoryTheory.Limits
open Verification.GraphCover Verification.GraphCoverOrder Verification.GraphCoverCancellation
  Verification.GraphCoverProjection Verification.GraphChainMatrix Verification.GraphSmallCoverTF
  Verification.GraphOrderChange Verification.GraphOrderApplications Verification.GraphChainTF

variable {R V : Type} [CommRing R] [Fintype V] [baseOrder : LinearOrder V]
  (G : SimpleGraph V) (C T : Finset V) (hC : Covers G C)

omit [Fintype V] baseOrder in
/-- The finite maximum is independent of the chosen decidable-equality implementation. -/
theorem coverRank_decidable (d e : DecidableEq V) :
    @coverRank V d G C=@coverRank V e G C := by
  cases Subsingleton.elim d e
  rfl

/-- The actual surviving free complex, constructed after a signed change of vertex order. -/
noncomputable def finiteCoverComplex : CochainComplex (ModuleCat R) ℤ :=
  @survivorComplex R V _ _ (@coverOrder V baseOrder C) G C T hC
    (@coverOrder_property V baseOrder C)

/-- The original signed chain complex is homotopy equivalent to this specified finite model. -/
noncomputable def finiteCoverHomotopyEquiv :
    HomotopyEquiv (chainComplex (R := R) G T) (finiteCoverComplex G C T hC) :=
  (HomotopyEquiv.ofIso (coverOrderIso G C T hC)).trans
    (@coverHomotopyEquiv R V _ _ (@coverOrder V baseOrder C) G C T hC
      (@coverOrder_property V baseOrder C))

theorem finiteCover_free (p : ℤ) : Module.Free R ((finiteCoverComplex (R := R) G C T hC).X p) :=
  Module.Free.of_basis (@survivorComplexBasis R V _ _ (@coverOrder V baseOrder C)
    G C T hC (@coverOrder_property V baseOrder C) p)

theorem finiteCover_finite (p : ℤ) : Module.Finite R ((finiteCoverComplex (R := R) G C T hC).X p) :=
  Module.Finite.of_basis (@survivorComplexBasis R V _ _ (@coverOrder V baseOrder C)
    G C T hC (@coverOrder_property V baseOrder C) p)

/-- Chain dimensions -1 through a-1 correspond to cochain degrees -a through zero. -/
theorem finiteCover_supported (p : ℤ) (hp : p < -(coverRank G C : ℤ) ∨ 0 < p) :
    Subsingleton ((finiteCoverComplex (R := R) G C T hC).X p) := by
  apply @survivorComplex_supported R V _ _ (@coverOrder V baseOrder C)
    G C T hC (@coverOrder_property V baseOrder C) p
  simpa only [coverRank_decidable G C _ (inferInstance : DecidableEq V)] using hp

include hC in
/-- The same range bound holds for actual original-order homology. -/
theorem cover_homology_zero (p : ℤ) (hp : p < -(coverRank G C : ℤ) ∨ 0 < p) :
    IsZero ((chainComplex (R := R) G T).homology p) := by
  letI := finiteCover_supported (R := R) G C T hC p hp
  have hz : IsZero ((finiteCoverComplex (R := R) G C T hC).homology p) := by
    apply HomologicalComplex.ExactAt.isZero_homology
    apply ShortComplex.exact_of_isZero_X₂
    change IsZero ((finiteCoverComplex (R := R) G C T hC).X p)
    exact ModuleCat.isZero_of_subsingleton _
  exact ((finiteCoverHomotopyEquiv (R := R) G C T hC).toHomologyIso p).isZero_iff.mpr hz

include hC in
set_option maxHeartbeats 200000 in
/-- The small-cover freeness conclusion in the original, completely arbitrary, vertex order. -/
theorem cover_homology_free [IsDomain R] [IsPrincipalIdealRing R]
    (ha : coverRank G C ≤ 2) (p : ℤ) :
    Module.Free R ((chainComplex (R := R) G T).homology p) := by
  let o : LinearOrder V := @coverOrder V baseOrder C
  have ho : @CoverOrdered V o C := @coverOrder_property V baseOrder C
  have hao : @coverRank V o.toDecidableEq G C ≤ 2 := by
    rw [coverRank_decidable G C o.toDecidableEq baseOrder.toDecidableEq]
    exact ha
  letI : Module.Free R ((complexFor (R := R) G T o).homology p) := by
    change Module.Free R ((@chainComplex R _ V _ o G T).homology p)
    exact @ordered_cover_homology_free R V _ _ _ o G C T hC ho _ hao p
  let E : (complexFor (R := R) G T o).homology p ≃ₗ[R]
      (complexFor (R := R) G T baseOrder).homology p :=
    (orderHomologyIso (R := R) G T baseOrder o p).symm.toLinearEquiv
  exact Module.Free.of_equiv E

include hC in
/-- Precisely the manuscript's all-induced integral chain-freeness hypothesis. -/
theorem small_cover_chainGraphFree (ha : coverRank G C ≤ 2) : ChainGraphFree G := by
  intro T p
  let M := (chainComplex (R := ℤ) G T).homology p
  have hex : ∃ ι : Type, Nonempty (M ≃+ (ι →₀ ℤ)) := by
    letI : Module ℤ M := ModuleCat.isModule M
    letI : Module.Free ℤ M := cover_homology_free (R := ℤ) G C T hC ha p
    exact ⟨Module.Free.ChooseBasisIndex ℤ M,⟨(Module.Free.chooseBasis ℤ M).repr.toAddEquiv⟩⟩
  obtain ⟨ι,⟨e⟩⟩ := hex
  exact Module.Free.of_equiv e.symm.toIntLinearEquiv

#print axioms coverRank_decidable
#print axioms cover_homology_zero
#print axioms finiteCoverComplex
#print axioms finiteCoverHomotopyEquiv
#print axioms finiteCover_free
#print axioms finiteCover_finite
#print axioms finiteCover_supported
#print axioms cover_homology_free
#print axioms small_cover_chainGraphFree

end Verification.GraphCoverTheorem
