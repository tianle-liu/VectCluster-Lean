/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedHomologyTF
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Quot

/-!
# Incidence Saturation

The integral saturation behind reduced H₀: the span of ordinary signed
edge differences is the kernel of the literal connected-component projection.
No homology-freeness result is supplied as an assumption.
-/

namespace Verification.IncidenceSaturation

open Classical

variable {R α : Type*} [CommRing R] (r : α → α → Prop)

/-- Span of the actual oriented edge boundaries. -/
def edgeSpan : Submodule R (α →₀ R) :=
  Submodule.span R {x | ∃ a b, r a b ∧ x=Finsupp.single a 1-Finsupp.single b 1}

/-- Projection sending a vertex to its equivalence class under edge paths. -/
noncomputable def componentProjection : (α →₀ R) →ₗ[R] (Quot r →₀ R) :=
  Finsupp.lmapDomain R R (Quot.mk r)

theorem difference_mem (a b : α) (h : Relation.EqvGen r a b) :
    Finsupp.single a (1 : R)-Finsupp.single b 1 ∈ edgeSpan (R := R) r := by
  induction h with
  | rel a b h => exact Submodule.subset_span ⟨a,b,h,rfl⟩
  | refl a => simpa only [sub_self] using (edgeSpan (R := R) r).zero_mem
  | symm a b _ ih => simpa only [neg_sub] using (edgeSpan (R := R) r).neg_mem ih
  | trans a b c _ _ hab hbc =>
    simpa only [sub_add_sub_cancel] using (edgeSpan (R := R) r).add_mem hab hbc

/-- The defining span is exactly the kernel, including disconnected and empty graphs. -/
theorem edgeSpan_eq_ker : edgeSpan (R := R) r=LinearMap.ker (componentProjection r) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨a,b,h,rfl⟩
    change componentProjection r (Finsupp.single a (1 : R)-Finsupp.single b 1)=0
    simp only [map_sub,componentProjection,Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single,Quot.sound h,sub_self]
  · let N := edgeSpan (R := R) r
    let L : (Quot r →₀ R) →ₗ[R] ((α →₀ R) ⧸ N) :=
      Finsupp.linearCombination R (fun q => N.mkQ (Finsupp.single q.out 1))
    have he : N.mkQ=L.comp (componentProjection r) := by
      apply Finsupp.lhom_ext
      intro a c
      have hd : Finsupp.single a (1 : R)-Finsupp.single (Quot.mk r a).out 1 ∈ N :=
        difference_mem r a _ (Quot.eqvGen_exact (Quot.out_eq (Quot.mk r a)).symm)
      have hq : N.mkQ (Finsupp.single a 1)=N.mkQ (Finsupp.single (Quot.mk r a).out 1) := by
        rw [← sub_eq_zero,← map_sub]
        exact (Submodule.Quotient.mk_eq_zero N).mpr hd
      have hs : Finsupp.single a c=c • Finsupp.single a (1 : R) := by simp
      rw [hs,map_smul,map_smul]
      congr 1
      simp only [LinearMap.comp_apply,componentProjection,Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_single,L,Finsupp.linearCombination_single,one_smul,hq]
    intro x hx
    apply (Submodule.Quotient.mk_eq_zero N).mp
    change N.mkQ x=0
    rw [he,LinearMap.comp_apply,LinearMap.mem_ker.mp hx,map_zero]

/-- Signed graph incidence images are saturated over any domain. -/
theorem edgeSpan_saturated [IsDomain R] (a : R) (ha : a ≠ 0) (x : α →₀ R)
    (hx : a • x ∈ edgeSpan (R := R) r) : x ∈ edgeSpan (R := R) r := by
  rw [edgeSpan_eq_ker,LinearMap.mem_ker] at hx ⊢
  rw [map_smul] at hx
  exact (eq_zero_or_eq_zero_of_smul_eq_zero hx).resolve_left ha

/-- The actual vertex module modulo all signed edges has no integral torsion. -/
theorem incidence_quotient_tf [IsDomain R] :
    NoZeroSMulDivisors R ((α →₀ R) ⧸ edgeSpan (R := R) r) :=
  (Verification.GradedHomologyTF.quotient_tf_iff _).mpr (edgeSpan_saturated r)

#print axioms edgeSpan
#print axioms componentProjection
#print axioms difference_mem
#print axioms edgeSpan_eq_ker
#print axioms edgeSpan_saturated
#print axioms incidence_quotient_tf

end Verification.IncidenceSaturation
