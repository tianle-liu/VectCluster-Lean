/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathLeftEndpoint

/-!
# Path Right Endpoint

The right endpoint is imposed on the literal word module. The resulting
idempotent is compatible with every valid rho face, including the final face.
-/

namespace Verification.PathRightEndpoint

open Classical Verification.PathRhoFaces Verification.PathRhoWords
  Verification.PathRhoFinite Verification.PathRhoEndpoint

variable {R : Type*} [CommRing R] (k : R)

noncomputable def projectionColumn : List Bool → (List Bool →₀ R)
  | [] => Finsupp.single [] 1
  | [a] => evaluation k a • Finsupp.single [false] 1
  | a::b::tail => prepend a (projectionColumn (b::tail))

noncomputable def projection : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R) :=
  Finsupp.linearCombination R (projectionColumn k)

theorem projection_single (w : List Bool) :
    projection k (Finsupp.single w 1)=projectionColumn k w := by
  simp only [projection,Finsupp.linearCombination_single,one_smul]

theorem column_length (w : List Bool) :
    ∃ c : R, ∃ v : List Bool, v.length=w.length ∧
      projectionColumn k w=c • Finsupp.single v 1 := by
  induction w with
  | nil => exact ⟨1,[],rfl,(one_smul _ _).symm⟩
  | cons a w ih =>
    cases w with
    | nil => exact ⟨evaluation k a,[false],rfl,rfl⟩
    | cons b tail =>
      rcases ih with ⟨c,v,hv,hc⟩
      refine ⟨c,a::v,by simpa only [List.length_cons] using congrArg Nat.succ hv,?_⟩
      rw [projectionColumn,hc,map_smul,prepend_single]

theorem projection_mem_layer (n : ℕ) (x : List Bool →₀ R) (hx : x ∈ layer (R := R) n) :
    projection k x ∈ layer (R := R) n := by
  have hh : layer (R := R) n ≤ (layer n).comap (projection k) := by
    conv_lhs => rw [layer,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change projection k (Finsupp.single w 1) ∈ layer (R := R) n
    rw [projection_single]
    rcases column_length k w with ⟨c,v,hv,hc⟩
    rw [hc]
    exact (layer n).smul_mem c (Finsupp.single_mem_supported R 1 (hv.trans hw))
  exact hh hx

theorem prepend_mem_layer (a : Bool) (n : ℕ) (x : List Bool →₀ R)
    (hx : x ∈ layer (R := R) n) : prepend a x ∈ layer (R := R) (n+1) := by
  have hh : layer (R := R) n ≤ (layer (n+1)).comap (prepend a) := by
    conv_lhs => rw [layer,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change w.length=n at hw
    change prepend a (Finsupp.single w 1) ∈ layer (R := R) (n+1)
    rw [prepend_single]
    exact Finsupp.single_mem_supported R 1 (by change (a::w).length=n+1; simp only [List.length_cons,hw])
  exact hh hx

/-- A nonempty suffix retains the rightmost coordinate after prefixing. -/
theorem projection_prepend (a : Bool) (n : ℕ) (hn : 0 < n)
    (x : List Bool →₀ R) (hx : x ∈ layer (R := R) n) :
    projection k (prepend a x)=prepend a (projection k x) := by
  let D := (projection k).comp (prepend a)-(prepend a).comp (projection k)
  have hh : layer (R := R) n ≤ LinearMap.ker D := by
    rw [layer,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change w.length=n at hw
    change projection k (prepend a (Finsupp.single w 1))-
      prepend a (projection k (Finsupp.single w 1))=0
    cases w with
    | nil => simp only [List.length_nil] at hw; omega
    | cons b tail =>
      simp only [prepend_single,projection_single,projectionColumn,sub_self]
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hh hx))

theorem projection_idempotent : (projection k).comp (projection k)=projection k := by
  have hc : ∀ w : List Bool, projection k (projectionColumn k w)=projectionColumn k w := by
    intro w
    induction w with
    | nil => simp only [projectionColumn,projection_single,projectionColumn]
    | cons a w ih =>
      cases w with
      | nil =>
        simp only [projectionColumn,map_smul,projection_single,evaluation,
          Bool.false_eq_true,↓reduceIte,one_smul]
      | cons b tail =>
        rw [projectionColumn,projection_prepend k a (b::tail).length (by simp)]
        · rw [ih]
        · rw [← projection_single]
          exact projection_mem_layer k _ _ (Finsupp.single_mem_supported R 1 rfl)
  apply Finsupp.lhom_ext
  intro w r
  have hr : Finsupp.single w r=r • Finsupp.single w (1 : R) := by simp
  rw [hr,map_smul,map_smul]
  congr 1
  simpa only [LinearMap.comp_apply,projection_single] using hc w

variable (ε ρ : R)

/-- The final face has precisely the scalar relation k²=ρk. -/
theorem final_face_quotient (hk : k*k=ρ*k) (a b c : Bool) :
    projection k (face ε ρ 0 (projection k (Finsupp.single [a,b,c] 1)))=
      projection k (face ε ρ 0 (Finsupp.single [a,b,c] 1)) := by
  cases a <;> cases b <;> cases c <;>
    simp [projection,face,Finsupp.linearCombination_single,projectionColumn,map_smul,prepend_single,
      faceColumn,phase,repeatFactor,evaluation,smul_smul,hk,mul_assoc,mul_comm,mul_left_comm]
  congr 1
  calc
    k*(k*ε)=(k*k)*ε := by ring
    _=(ρ*k)*ε := by rw [hk]
    _=k*(ε*ρ) := by ring


/-- Prefixing three coordinates does not move a nonempty suffix endpoint. -/
theorem projection_prefix_three (a b c : Bool) (n : ℕ) (hn : 0 < n)
    (x : List Bool →₀ R) (hx : x ∈ layer (R := R) n) :
    projection k (prepend a (prepend b (prepend c x)))=
      prepend a (prepend b (prepend c (projection k x))) := by
  rw [projection_prepend k a (n+2) (by omega) _
    (prepend_mem_layer b (n+1) _ (prepend_mem_layer c n x hx))]
  rw [projection_prepend k b (n+1) (by omega) _ (prepend_mem_layer c n x hx)]
  rw [projection_prepend k c n hn x hx]

theorem head_face_quotient (a b c : Bool) (n : ℕ) (hn : 0 < n)
    (x : List Bool →₀ R) (hx : x ∈ layer (R := R) n) :
    projection k (face ε ρ 0 (projection k (prepend a (prepend b (prepend c x)))))=
      projection k (face ε ρ 0 (prepend a (prepend b (prepend c x)))) := by
  rw [projection_prefix_three k a b c n hn x hx,face_head,face_head]
  cases b with
  | false => simp only [Bool.false_eq_true,↓reduceIte,map_zero]
  | true =>
    simp only [↓reduceIte,map_smul]
    rw [projection_prepend k (a || c) n hn _ (projection_mem_layer k n x hx),
      projection_prepend k (a || c) n hn x hx]
    have hid := congrArg (fun f : _ →ₗ[R] _ => f x) (projection_idempotent k)
    change projection k (projection k x)=projection k x at hid
    rw [hid]

/-- Recursion through a prefix, with the nonempty target condition explicit. -/
theorem tail_face_quotient (i : ℕ) (a : Bool) (n : ℕ) (hn : 3 ≤ n)
    (x : List Bool →₀ R) (hx : x ∈ layer (R := R) n)
    (h : projection k (face ε ρ i (projection k x))=projection k (face ε ρ i x)) :
    projection k (face ε ρ (i+1) (projection k (prepend a x)))=
      projection k (face ε ρ (i+1) (prepend a x)) := by
  rw [projection_prepend k a n (by omega) x hx,face_prepend,face_prepend,map_smul,map_smul]
  rw [projection_prepend k a (n-2) (by omega) _
    (face_mem_layer ε ρ i n _ (projection_mem_layer k n x hx))]
  rw [projection_prepend k a (n-2) (by omega) _ (face_mem_layer ε ρ i n x hx),h]

theorem word_face_quotient (hk : k*k=ρ*k) (i : ℕ) (w : List Bool)
    (hw : i+3 ≤ w.length) :
    projection k (face ε ρ i (projection k (Finsupp.single w 1)))=
      projection k (face ε ρ i (Finsupp.single w 1)) := by
  induction i generalizing w with
  | zero =>
    rcases Verification.PathRhoBraid.exists_prefix_three w hw with ⟨a,b,c,tail,rfl⟩
    cases tail with
    | nil => exact final_face_quotient k ε ρ hk a b c
    | cons d tail =>
      simpa only [prepend_single] using head_face_quotient k ε ρ a b c
        (d::tail).length (by simp) (Finsupp.single (d::tail) 1)
          (Finsupp.single_mem_supported R 1 rfl)
  | succ i ih =>
    cases w with
    | nil => simp only [List.length_nil] at hw; omega
    | cons a tail =>
      have ht : i+3 ≤ tail.length := by simp only [List.length_cons] at hw; omega
      simpa only [prepend_single] using tail_face_quotient k ε ρ i a tail.length (by omega)
        (Finsupp.single tail 1) (Finsupp.single_mem_supported R 1 rfl) (ih tail ht)

/-- Quotient compatibility for every vector in a valid finite source layer. -/
theorem projection_face_quotient (hk : k*k=ρ*k) (i n : ℕ) (hn : i+3 ≤ n)
    (x : List Bool →₀ R) (hx : x ∈ layer (R := R) n) :
    projection k (face ε ρ i (projection k x))=projection k (face ε ρ i x) := by
  let D := (projection k).comp ((face ε ρ i).comp (projection k))-
    (projection k).comp (face ε ρ i)
  have hh : layer (R := R) n ≤ LinearMap.ker D := by
    rw [layer,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change projection k (face ε ρ i (projection k (Finsupp.single w 1)))-
      projection k (face ε ρ i (Finsupp.single w 1))=0
    exact sub_eq_zero.mpr (word_face_quotient k ε ρ hk i w (by change w.length=n at hw; omega))
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hh hx))

#print axioms projectionColumn
#print axioms projection
#print axioms projection_single
#print axioms column_length
#print axioms projection_mem_layer
#print axioms prepend_mem_layer
#print axioms projection_prepend
#print axioms projection_idempotent
#print axioms final_face_quotient

#print axioms projection_prefix_three
#print axioms head_face_quotient
#print axioms tail_face_quotient
#print axioms word_face_quotient
#print axioms projection_face_quotient

end Verification.PathRightEndpoint
