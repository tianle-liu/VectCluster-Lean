/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathWordKills
import Mathlib.Data.Fintype.Vector
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Path First Boundary

Actual finite free presentation of the normalized weight-preserving first
path boundary. Its columns are exactly isolated mutable singleton words and
literal local slide differences. The g-normalization and the full rho-raising
cellular differential are separate subsequent comparisons.
-/

namespace Verification.PathFirstBoundary

open Classical Verification.PathWords Verification.PathWordSlides Verification.PathWordKills

instance wordFintype (n : ℕ) : Fintype (Word n) :=
  inferInstanceAs (Fintype (List.Vector Bool n))

/-- Literal local slide on the original finite binary-word generators. -/
def Slide {n : ℕ} (u v : Word n) : Prop := ∃ pre post,
  u.val=pre ++ true :: true :: false :: post ∧
  v.val=pre ++ false :: true :: true :: post

/-- Initial position mutable for Y, frozen for Z. -/
def Killed (initialMutable : Bool) {n : ℕ} (w : Word n) : Prop :=
  if initialMutable then KilledY w.val else KilledZ w.val

/-- Explicit finite source generators of the first boundary. -/
abbrev BoundaryIndex (initialMutable : Bool) (n : ℕ) :=
  {w : Word n // Killed initialMutable w} ⊕ {uv : Word n × Word n // Slide uv.1 uv.2}

noncomputable instance boundaryFintype (initialMutable : Bool) (n : ℕ) :
    Fintype (BoundaryIndex initialMutable n) := inferInstance

variable {R : Type*} [CommRing R] (initialMutable : Bool) (n : ℕ)

/-- The actual normalized integer/unit relation column. -/
noncomputable def relationColumn : BoundaryIndex initialMutable n → (Word n →₀ R)
  | Sum.inl w => Finsupp.single w.val 1
  | Sum.inr uv => Finsupp.single uv.val.1 1-Finsupp.single uv.val.2 1

/-- The literal first differential, with no cokernel or freeness condition assumed. -/
noncomputable def firstBoundary : (BoundaryIndex initialMutable n →₀ R) →ₗ[R] (Word n →₀ R) :=
  Finsupp.linearCombination R (relationColumn initialMutable n)

/-- The actual degree-zero homology presentation. -/
abbrev Cokernel := (Word n →₀ R) ⧸ LinearMap.range (firstBoundary (R := R) initialMutable n)

theorem killed_boundary (w : Word n) (h : Killed initialMutable w) :
    Finsupp.single w (1 : R) ∈ LinearMap.range (firstBoundary initialMutable n) := by
  refine ⟨Finsupp.single (Sum.inl ⟨w,h⟩) 1,?_⟩
  simp only [firstBoundary,Finsupp.linearCombination_single,one_smul,relationColumn]

theorem slide_boundary (u v : Word n) (h : Slide u v) :
    Finsupp.single u (1 : R)-Finsupp.single v 1 ∈
      LinearMap.range (firstBoundary initialMutable n) := by
  refine ⟨Finsupp.single (Sum.inr ⟨(u,v),h⟩) 1,?_⟩
  simp only [firstBoundary,Finsupp.linearCombination_single,one_smul,relationColumn]

/-- Every finite slide path supplies an actual relation in the first-boundary image. -/
theorem connected_boundary {u v : List Bool} (h : WordConnected u v) :
    ∀ (hu : u.length=n) (hv : v.length=n),
      Finsupp.single (⟨u,hu⟩ : Word n) (1 : R)-Finsupp.single ⟨v,hv⟩ 1 ∈
        LinearMap.range (firstBoundary initialMutable n) := by
  induction h with
  | refl w => intro hu hv; simpa only [sub_self] using (LinearMap.range (firstBoundary (R := R) initialMutable n)).zero_mem
  | slide pre post =>
    intro hu hv
    exact slide_boundary initialMutable n ⟨_,hu⟩ ⟨_,hv⟩ ⟨pre,post,rfl,rfl⟩
  | symm h ih =>
    intro hu hv
    simpa only [neg_sub] using (LinearMap.range (firstBoundary (R := R) initialMutable n)).neg_mem (ih hv hu)
  | @trans u v w h₁ h₂ ih₁ ih₂ =>
    intro hu hw
    have hv : v.length=n := (wordConnected_length h₁).symm.trans hu
    simpa only [sub_add_sub_cancel] using
      (LinearMap.range (firstBoundary (R := R) initialMutable n)).add_mem (ih₁ hu hv) (ih₂ hv hw)

/-- A component containing a singleton relation is actually killed in the cokernel. -/
theorem connected_killed_boundary (u v : Word n) (h : WordConnected u.val v.val)
    (hv : Killed initialMutable v) :
    Finsupp.single u (1 : R) ∈ LinearMap.range (firstBoundary initialMutable n) := by
  have hh := connected_boundary (R := R) initialMutable n h u.property v.property
  have hk := killed_boundary (R := R) initialMutable n v hv
  simpa only [sub_add_cancel] using
    (LinearMap.range (firstBoundary (R := R) initialMutable n)).add_mem hh hk

/-- Every forbidden Z parity word lies in the actual finite first-boundary image. -/
theorem badZ_boundary (w : Word n) (h : ¬GoodZ w.val) :
    Finsupp.single w (1 : R) ∈ LinearMap.range (firstBoundary false n) := by
  obtain ⟨v,hv,hk⟩ := badZ_killed w.val h
  have hn : v.length=n := (wordConnected_length hv).symm.trans w.property
  exact connected_killed_boundary false n w ⟨v,hn⟩ hv hk

/-- The same claim for all original even-length Y presentations. -/
theorem badY_boundary (heven : n % 2=0) (w : Word n) (h : ¬GoodY w.val) :
    Finsupp.single w (1 : R) ∈ LinearMap.range (firstBoundary true n) := by
  obtain ⟨v,hv,hk⟩ := badY_killed w.val (by rw [w.property]; exact heven) h
  have hn : v.length=n := (wordConnected_length hv).symm.trans w.property
  exact connected_killed_boundary true n w ⟨v,hn⟩ hv hk

#print axioms wordFintype
#print axioms Slide
#print axioms Killed
#print axioms BoundaryIndex
#print axioms boundaryFintype
#print axioms relationColumn
#print axioms firstBoundary
#print axioms Cokernel
#print axioms killed_boundary
#print axioms slide_boundary
#print axioms connected_boundary
#print axioms connected_killed_boundary
#print axioms badZ_boundary
#print axioms badY_boundary

end Verification.PathFirstBoundary
