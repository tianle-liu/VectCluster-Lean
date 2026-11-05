/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathCofaceNormalForms
import Verification.PathFirstRangeInclusion

/-!
# Path Actual Column Relations

Conversely, every actual rho-zero first column is one of the original
kill or g-slide relations multiplied by its computed incidence coefficient.
-/

namespace Verification.PathActualColumnRelations

open Classical Verification.PathWords Verification.PathFirstBoundary Verification.PathSignNormalization
  Verification.PathFirstBasis Verification.PathFirstBoundaryCutout Verification.PathFirstColumnExtraction
  Verification.PathFirstCofaceRelations Verification.PathEndpointWords Verification.PathEndpointWordRemoval
  Verification.PathNormalizedBasis Verification.PathPaddedRelations Verification.PathCofaceNormalForms

variable {R : Type*} [CommRing R]

theorem signed_killed (g : R) (m : Bool) (n : ℕ) (w : Word n) (hw : Killed m w) :
    Finsupp.single w (1 : R) ∈ LinearMap.range (signedBoundary g m n) := by
  refine ⟨Finsupp.single (Sum.inl ⟨w,hw⟩) 1,?_⟩
  simp only [signedBoundary,Finsupp.linearCombination_single,one_smul,signedColumn]

theorem signed_slide (g : R) (m : Bool) (n : ℕ) (u v : Word n) (h : Slide u v) :
    Finsupp.single u (1 : R)-g • Finsupp.single v 1 ∈ LinearMap.range (signedBoundary g m n) := by
  refine ⟨Finsupp.single (Sum.inr ⟨(u,v),h⟩) 1,?_⟩
  simp only [signedBoundary,Finsupp.linearCombination_single,one_smul,signedColumn]

theorem zColumn_mem_signed (g : R) (hg : g*g=1) (n : ℕ) (s : OneSource RightNormal n) :
    zColumn g n s ∈ LinearMap.range (signedBoundary g false (n+1)) := by
  have hb := Finset.mem_Icc.mp s.1.property
  have hi : s.1.val-1 < s.2.val.length := by rw [s.2.property.1]; omega
  obtain ⟨pre,bit,tail,hp,hv⟩ := split_at s.2.val (s.1.val-1) hi
  have hn := s.2.property.2
  have hl := s.2.property.1
  rw [hv] at hn hl
  simp only [List.length_append,List.length_cons] at hl
  cases bit with
  | false =>
    have hlen : (pre++false::true::false::tail).length=n+2 := by
      simp only [List.length_append,List.length_cons]; omega
    let W : NormalWord RightNormal (n+2) := ⟨_,hlen,right_kill_expand pre tail hn⟩
    let w : Word (n+1) := rightWordEquiv (n+1) W
    have hpad : pre++false::true::false::tail=w.val++[false] := right_padded (n+1) W
    have he : zColumn g n s=prefixFactor (-g) pre • Finsupp.single w 1 := by
      rw [zColumn_extract,← hp,hv,kill_column,map_smul,hpad,zExtract_single]
    rw [he]
    exact (LinearMap.range (signedBoundary g false (n+1))).smul_mem _
      (signed_killed g false (n+1) w (z_kill_of_padded w.val pre tail hpad))
  | true =>
    obtain ⟨ht,hU,hV⟩ := right_slide_expand pre tail hn
    have hu : (pre++true::true::false::tail).length=n+2 := by
      simp only [List.length_append,List.length_cons]; omega
    have hv' : (pre++false::true::true::tail).length=n+2 := by
      simp only [List.length_append,List.length_cons]; omega
    let U : NormalWord RightNormal (n+2) := ⟨_,hu,hU⟩
    let V : NormalWord RightNormal (n+2) := ⟨_,hv',hV⟩
    let u : Word (n+1) := rightWordEquiv (n+1) U
    let v : Word (n+1) := rightWordEquiv (n+1) V
    have hpadU : pre++true::true::false::tail=u.val++[false] := right_padded (n+1) U
    have hpadV : pre++false::true::true::tail=v.val++[false] := right_padded (n+1) V
    have he : zColumn g n s=(prefixFactor (-g) pre*(-g)) •
        (Finsupp.single u 1-g • Finsupp.single v 1) := by
      rw [zColumn_extract,← hp,hv,slide_column g hg,map_smul,map_sub,map_smul,
        hpadU,hpadV,zExtract_single,zExtract_single]
    rw [he]
    exact (LinearMap.range (signedBoundary g false (n+1))).smul_mem _
      (signed_slide g false (n+1) u v (z_slide_of_padded u v pre tail ht hpadU hpadV))

theorem yColumn_mem_signed (g : R) (hg : g*g=1) (a : ℕ) (s : OneSource BothNormal (2*a)) :
    yColumn g a s ∈ LinearMap.range (signedBoundary g true (2*a)) := by
  have hb := Finset.mem_Icc.mp s.1.property
  have hi : s.1.val-1 < s.2.val.length := by rw [s.2.property.1]; omega
  obtain ⟨pre,bit,tail,hp,hv⟩ := split_at s.2.val (s.1.val-1) hi
  have hn := s.2.property.2
  have hl := s.2.property.1
  rw [hv] at hn hl
  simp only [List.length_append,List.length_cons] at hl
  cases bit with
  | false =>
    have hlen : (pre++false::true::false::tail).length=2*a+2 := by
      simp only [List.length_append,List.length_cons]; omega
    let W : NormalWord BothNormal (2*a+2) :=
      ⟨_,hlen,left_kill_expand pre tail hn.1,right_kill_expand pre tail hn.2⟩
    let w : Word (2*a) := bothWordEquiv (2*a) W
    have hpad : pre++false::true::false::tail=false::(w.val++[false]) := both_padded (2*a) W
    have he : yColumn g a s=prefixFactor (-g) pre • Finsupp.single w 1 := by
      rw [yColumn_extract,← hp,hv,kill_column,map_smul,hpad,yExtract_single]
    rw [he]
    exact (LinearMap.range (signedBoundary g true (2*a))).smul_mem _
      (signed_killed g true (2*a) w (y_kill_of_padded w.val pre tail hpad))
  | true =>
    obtain ⟨ht,hRU,hRV⟩ := right_slide_expand pre tail hn.2
    obtain ⟨hp',hLU,hLV⟩ := left_slide_expand pre tail hn.1
    have hu : (pre++true::true::false::tail).length=2*a+2 := by
      simp only [List.length_append,List.length_cons]; omega
    have hv' : (pre++false::true::true::tail).length=2*a+2 := by
      simp only [List.length_append,List.length_cons]; omega
    let U : NormalWord BothNormal (2*a+2) := ⟨_,hu,hLU,hRU⟩
    let V : NormalWord BothNormal (2*a+2) := ⟨_,hv',hLV,hRV⟩
    let u : Word (2*a) := bothWordEquiv (2*a) U
    let v : Word (2*a) := bothWordEquiv (2*a) V
    have hpadU : pre++true::true::false::tail=false::(u.val++[false]) := both_padded (2*a) U
    have hpadV : pre++false::true::true::tail=false::(v.val++[false]) := both_padded (2*a) V
    have he : yColumn g a s=(prefixFactor (-g) pre*(-g)) •
        (Finsupp.single u 1-g • Finsupp.single v 1) := by
      rw [yColumn_extract,← hp,hv,slide_column g hg,map_smul,map_sub,map_smul,
        hpadU,hpadV,yExtract_single,yExtract_single]
    rw [he]
    exact (LinearMap.range (signedBoundary g true (2*a))).smul_mem _
      (signed_slide g true (2*a) u v (y_slide_of_padded u v pre tail hp' ht hpadU hpadV))

#print axioms signed_killed
#print axioms signed_slide
#print axioms zColumn_mem_signed
#print axioms yColumn_mem_signed

end Verification.PathActualColumnRelations
