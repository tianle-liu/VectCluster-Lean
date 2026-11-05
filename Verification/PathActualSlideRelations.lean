/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathFirstColumnExtraction

/-!
# Path Actual Slide Relations

Every original local g-slide is a unit multiple of a literal column of
the actual rho-zero Y/Z first boundary, including its endpoint basis maps.
-/

namespace Verification.PathActualSlideRelations

open Classical Verification.PathWords Verification.PathFirstBoundary Verification.PathFirstBasis
  Verification.PathFirstBoundaryCutout Verification.PathFirstColumnExtraction
  Verification.PathFirstCofaceRelations Verification.PathEndpointWords Verification.PathEndpointWordRemoval

variable {R : Type*} [CommRing R]

theorem cancel_unit_mem {M : Type*} [AddCommGroup M] [Module R M]
    (S : Submodule R M) (c : R) (hc : c*c=1) (x : M) (hx : c • x ∈ S) : x ∈ S := by
  simpa only [smul_smul,hc,one_smul] using S.smul_mem c hx

theorem z_slide_column (g : R) (hg : g*g=1) (n : ℕ) (u v : Word (n+1)) (h : Slide u v) :
    ∃ s : OneSource RightNormal n, ∃ c : R, c*c=1 ∧
      zColumn g n s=c • (Finsupp.single u 1-g • Finsupp.single v 1) := by
  obtain ⟨pre,post,hu,hv⟩ := h
  have hlen := u.property
  rw [hu] at hlen
  simp only [List.length_append,List.length_cons] at hlen
  have hj : pre.length+1 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr (by omega)
  have hl : (pre++true::(post++[false])).length=n := by
    simp only [List.length_append,List.length_cons,List.length_singleton,List.length_nil]
    omega
  have hn : RightNormal (pre++true::(post++[false])) := by
    simpa only [List.append_assoc,List.cons_append] using rightNormal_append_false (pre++true::post)
  let s : OneSource RightNormal n := (⟨pre.length+1,hj⟩,⟨_,hl,hn⟩)
  refine ⟨s,prefixFactor (-g) pre*(-g),relation_factor_squared g hg pre,?_⟩
  rw [zColumn_extract]
  change zExtract n (Verification.PathFirstCofaces.cofaceColumn (-g) 0 pre.length (pre++true::(post++[false])))=_
  rw [slide_column g hg,map_smul,map_sub,map_smul]
  have hU : pre++true::true::false::(post++[false])=u.val++[false] := by
    rw [hu]
    simp only [List.append_assoc,List.cons_append]
  have hV : pre++false::true::true::(post++[false])=v.val++[false] := by
    rw [hv]
    simp only [List.append_assoc,List.cons_append]
  rw [hU,hV,zExtract_single,zExtract_single]

theorem z_slide_boundary (g : R) (hg : g*g=1) (n : ℕ) (u v : Word (n+1)) (h : Slide u v) :
    Finsupp.single u (1 : R)-g • Finsupp.single v 1 ∈ LinearMap.range (zBoundary g n) := by
  obtain ⟨s,c,hc,hs⟩ := z_slide_column g hg n u v h
  apply cancel_unit_mem _ c hc
  rw [← hs]
  exact ⟨Finsupp.single s 1,zBoundary_single g n s⟩

theorem y_slide_column (g : R) (hg : g*g=1) (a : ℕ) (u v : Word (2*a)) (h : Slide u v) :
    ∃ s : OneSource BothNormal (2*a), ∃ c : R, c*c=1 ∧
      yColumn g a s=c • (Finsupp.single u 1-g • Finsupp.single v 1) := by
  obtain ⟨pre,post,hu,hv⟩ := h
  have hlen := u.property
  rw [hu] at hlen
  simp only [List.length_append,List.length_cons] at hlen
  have hj : pre.length+2 ∈ Finset.Icc 1 (2*a) := Finset.mem_Icc.mpr (by omega)
  have hl : (false::(pre++true::(post++[false]))).length=2*a := by
    simp only [List.length_append,List.length_cons,List.length_singleton,List.length_nil]
    omega
  have hn : BothNormal (false::(pre++true::(post++[false]))) := by
    refine ⟨rfl,?_⟩
    simpa only [List.append_assoc,List.cons_append] using rightNormal_append_false (false::(pre++true::post))
  let s : OneSource BothNormal (2*a) := (⟨pre.length+2,hj⟩,⟨_,hl,hn⟩)
  refine ⟨s,prefixFactor (-g) (false::pre)*(-g),relation_factor_squared g hg (false::pre),?_⟩
  rw [yColumn_extract]
  change yExtract a (Verification.PathFirstCofaces.cofaceColumn (-g) 0 (false::pre).length
    ((false::pre)++true::(post++[false])))=_
  rw [slide_column g hg,map_smul,map_sub,map_smul]
  have hU : (false::pre)++true::true::false::(post++[false])=false::(u.val++[false]) := by
    rw [hu]
    simp only [List.append_assoc,List.cons_append]
  have hV : (false::pre)++false::true::true::(post++[false])=false::(v.val++[false]) := by
    rw [hv]
    simp only [List.append_assoc,List.cons_append]
  rw [hU,hV,yExtract_single,yExtract_single]

theorem y_slide_boundary (g : R) (hg : g*g=1) (a : ℕ) (u v : Word (2*a)) (h : Slide u v) :
    Finsupp.single u (1 : R)-g • Finsupp.single v 1 ∈ LinearMap.range (yBoundary g a) := by
  obtain ⟨s,c,hc,hs⟩ := y_slide_column g hg a u v h
  apply cancel_unit_mem _ c hc
  rw [← hs]
  exact ⟨Finsupp.single s 1,yBoundary_single g a s⟩

#print axioms cancel_unit_mem
#print axioms z_slide_column
#print axioms z_slide_boundary
#print axioms y_slide_column
#print axioms y_slide_boundary

end Verification.PathActualSlideRelations
