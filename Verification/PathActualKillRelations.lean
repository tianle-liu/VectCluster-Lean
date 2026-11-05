/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathActualSlideRelations

/-!
# Path Actual Kill Relations

Every isolated mutable word relation is a literal actual first-boundary
column, including both constant ends and the frozen initial Z coordinate.
-/

namespace Verification.PathActualKillRelations

open Classical Verification.PathWords Verification.PathWordKills Verification.PathFirstBoundary
  Verification.PathFirstBasis Verification.PathFirstBoundaryCutout Verification.PathFirstColumnExtraction
  Verification.PathFirstCofaceRelations Verification.PathEndpointWords Verification.PathEndpointWordRemoval
  Verification.PathNormalWordRecursion Verification.PathActualSlideRelations

variable {R : Type*} [CommRing R]

theorem rightNormal_prefix_iff (pre w : List Bool) (hw : w ≠ []) :
    RightNormal (pre++w) ↔ RightNormal w := by
  induction pre with
  | nil => rfl
  | cons a pre ih =>
    rw [List.cons_append,rightNormal_cons a (pre++w) (by simp [hw]),ih]

theorem right_kill_compress (pre tail : List Bool)
    (h : RightNormal (pre++false::true::false::tail)) : RightNormal (pre++false::tail) := by
  apply (rightNormal_prefix_iff pre (false::tail) (List.cons_ne_nil _ _)).mpr
  have hh := (rightNormal_prefix_iff pre (false::true::false::tail) (List.cons_ne_nil _ _)).mp h
  exact (rightNormal_cons true (false::tail) (List.cons_ne_nil _ _)).mp
    ((rightNormal_cons false (true::false::tail) (List.cons_ne_nil _ _)).mp hh)

theorem left_kill_compress (pre tail : List Bool)
    (h : LeftNormal (pre++false::true::false::tail)) : LeftNormal (pre++false::tail) := by
  cases pre with
  | nil => rfl
  | cons a pre =>
    have ha : false=a := (List.cons.inj h).1
    rw [← ha]
    rfl

theorem vacant_pad (post : List Bool) (h : RightVacant post) :
    ∃ tail, post++[false]=false::tail := by
  rcases h with rfl | ⟨tail,rfl⟩
  · exact ⟨[],rfl⟩
  · exact ⟨tail++[false],rfl⟩

theorem z_padded_kill (g : R) (hg : g*g=1) (n : ℕ) (w : Word (n+1))
    (pre tail : List Bool) (hpad : pre++false::true::false::tail=w.val++[false]) :
    Finsupp.single w (1 : R) ∈ LinearMap.range (zBoundary g n) := by
  have hlen := congrArg List.length hpad
  simp only [List.length_append,List.length_cons,List.length_nil,w.property] at hlen
  have hj : pre.length+1 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr (by omega)
  have hl : (pre++false::tail).length=n := by
    simp only [List.length_append,List.length_cons]
    omega
  have hn : RightNormal (pre++false::tail) :=
    right_kill_compress pre tail (hpad.symm ▸ rightNormal_append_false w.val)
  let s : OneSource RightNormal n := (⟨pre.length+1,hj⟩,⟨_,hl,hn⟩)
  have he : zColumn g n s=prefixFactor (-g) pre • Finsupp.single w 1 := by
    rw [zColumn_extract]
    change zExtract n (Verification.PathFirstCofaces.cofaceColumn (-g) 0 pre.length (pre++false::tail))=_
    rw [kill_column,map_smul,hpad,zExtract_single]
  apply cancel_unit_mem _ (prefixFactor (-g) pre)
    (prefixFactor_squared (-g) (by simpa only [neg_mul_neg] using hg) pre)
  rw [← he]
  exact ⟨Finsupp.single s 1,zBoundary_single g n s⟩

theorem y_padded_kill (g : R) (hg : g*g=1) (a : ℕ) (w : Word (2*a))
    (pre tail : List Bool) (hpad : pre++false::true::false::tail=false::(w.val++[false])) :
    Finsupp.single w (1 : R) ∈ LinearMap.range (yBoundary g a) := by
  have hlen := congrArg List.length hpad
  simp only [List.length_append,List.length_cons,List.length_nil,w.property] at hlen
  have hj : pre.length+1 ∈ Finset.Icc 1 (2*a) := Finset.mem_Icc.mpr (by omega)
  have hl : (pre++false::tail).length=2*a := by
    simp only [List.length_append,List.length_cons]
    omega
  have hfull : BothNormal (false::(w.val++[false])) := by
    refine ⟨rfl,?_⟩
    simpa only [List.cons_append] using rightNormal_append_false (false::w.val)
  have hn : BothNormal (pre++false::tail) := by
    have hh := hpad.symm ▸ hfull
    exact ⟨left_kill_compress pre tail hh.1,right_kill_compress pre tail hh.2⟩
  let s : OneSource BothNormal (2*a) := (⟨pre.length+1,hj⟩,⟨_,hl,hn⟩)
  have he : yColumn g a s=prefixFactor (-g) pre • Finsupp.single w 1 := by
    rw [yColumn_extract]
    change yExtract a (Verification.PathFirstCofaces.cofaceColumn (-g) 0 pre.length (pre++false::tail))=_
    rw [kill_column,map_smul,hpad,yExtract_single]
  apply cancel_unit_mem _ (prefixFactor (-g) pre)
    (prefixFactor_squared (-g) (by simpa only [neg_mul_neg] using hg) pre)
  rw [← he]
  exact ⟨Finsupp.single s 1,yBoundary_single g a s⟩

theorem z_killed_boundary (g : R) (hg : g*g=1) (n : ℕ) (w : Word (n+1)) (hw : KilledZ w.val) :
    Finsupp.single w (1 : R) ∈ LinearMap.range (zBoundary g n) := by
  obtain ⟨pre,post,hp,he⟩ := hw
  obtain ⟨tail,ht⟩ := vacant_pad post hp
  apply z_padded_kill g hg n w pre tail
  rw [he]
  simp only [List.append_assoc,List.cons_append,ht]

theorem y_killed_boundary (g : R) (hg : g*g=1) (a : ℕ) (w : Word (2*a)) (hw : KilledY w.val) :
    Finsupp.single w (1 : R) ∈ LinearMap.range (yBoundary g a) := by
  rcases hw with hz | ⟨post,hp,he⟩
  · obtain ⟨pre,post,hp,he⟩ := hz
    obtain ⟨tail,ht⟩ := vacant_pad post hp
    apply y_padded_kill g hg a w (false::pre) tail
    rw [he]
    simp only [List.append_assoc,List.cons_append,ht]
  · obtain ⟨tail,ht⟩ := vacant_pad post hp
    apply y_padded_kill g hg a w [] tail
    rw [he]
    simp only [List.nil_append,List.cons_append,ht]

#print axioms rightNormal_prefix_iff
#print axioms right_kill_compress
#print axioms left_kill_compress
#print axioms vacant_pad
#print axioms z_padded_kill
#print axioms y_padded_kill
#print axioms z_killed_boundary
#print axioms y_killed_boundary

end Verification.PathActualKillRelations
