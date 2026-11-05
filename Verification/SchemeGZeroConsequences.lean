/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SchemeGZeroInput

/-!
# Scheme G Zero Consequences

Consequences of ordinary G-theory functoriality and localization.
The vanishing of the closed pushforwards and the induction conclusions
are proved here, rather than included in the reference interfaces.
-/
noncomputable section
namespace Verification.SchemeGZeroConsequences
open CategoryTheory AlgebraicGeometry
variable {G : Scheme → Type*} [∀ X,AddCommGroup (G X)]
variable (T : SchemeGZeroInput.Theory G)

def unitMap (X : Scheme) : ℤ →+ G X where
  toFun n := n • T.unit X
  map_zero' := zero_zsmul _
  map_add' _ _ := add_zsmul _ _ _

def isoEquiv {X Y : Scheme} (e : X≅Y) : G X ≃+ G Y where
  toFun := T.restrict e.inv inferInstance
  invFun := T.restrict e.hom inferInstance
  left_inv x := by
    have h := T.restrict_comp e.hom e.inv inferInstance inferInstance
    simp only [e.hom_inv_id,T.restrict_id] at h
    exact (congrArg (fun f => f x) h).symm
  right_inv y := by
    have h := T.restrict_comp e.inv e.hom inferInstance inferInstance
    simp only [e.inv_hom_id,T.restrict_id] at h
    exact (congrArg (fun f => f y) h).symm
  map_add' := (T.restrict e.inv inferInstance).map_add

theorem isoEquiv_unit {X Y : Scheme} (e : X≅Y) : isoEquiv T e (T.unit X)=T.unit Y :=
  T.restrict_unit e.inv inferInstance

theorem unit_generated_of_iso {X Y : Scheme} (e : X≅Y)
    (h : Function.Surjective (unitMap T Y)) : Function.Surjective (unitMap T X) := by
  intro x
  obtain ⟨n,hn⟩ := h (isoEquiv T e x)
  refine ⟨n,(isoEquiv T e).injective ?_⟩
  change isoEquiv T e (n • T.unit X)=isoEquiv T e x
  rw [map_zsmul,isoEquiv_unit]
  exact hn

theorem unit_injective_of_iso {X Y : Scheme} (e : X≅Y)
    (h : Function.Injective (unitMap T Y)) : Function.Injective (unitMap T X) := by
  intro a b hab
  apply h
  have hm := congrArg (isoEquiv T e) hab
  simpa only [unitMap,AddMonoidHom.coe_mk,ZeroHom.coe_mk,map_zsmul,isoEquiv_unit] using hm

theorem restriction_bijective (L : SchemeGZeroInput.Localization T)
    {U X : Scheme} [IsNoetherian X] (j : U⟶X) (hj : IsOpenImmersion j)
    (ι : Type) [Fintype ι] (Z : ι→Scheme) (i : ∀ a,Z a⟶X)
    (hi : ∀ a,IsClosedImmersion (i a))
    (hd : Pairwise (fun a b => Disjoint (Set.range (i a).base) (Set.range (i b).base)))
    (hc : (⋃ a,Set.range (i a).base)=(Set.range j.base)ᶜ)
    (hgen : ∀ a,Function.Surjective (unitMap T (Z a)))
    (hzero : ∀ a,T.push (i a) (hi a) (T.unit (Z a))=0) :
    Function.Bijective (T.restrict j hj) := by
  refine ⟨?_,L.surjective j hj⟩
  intro x y hxy
  have hz : T.restrict j hj (x-y)=0 := by rw [map_sub,hxy,sub_self]
  obtain ⟨b,hb⟩ := L.kernel j hj ι Z i hi hd hc (x-y) hz
  apply sub_eq_zero.mp
  rw [hb]
  apply Finset.sum_eq_zero
  intro a _
  obtain ⟨n,hn⟩ := hgen a (b a)
  rw [← hn]
  change T.push (i a) (hi a) (n • T.unit (Z a))=0
  rw [map_zsmul,hzero,zsmul_zero]

theorem unit_bijective_of_restriction {U X : Scheme} (j : U⟶X) (hj : IsOpenImmersion j)
    (hres : Function.Bijective (T.restrict j hj))
    (hunit : Function.Bijective (unitMap T U)) : Function.Bijective (unitMap T X) := by
  have hcomp : (T.restrict j hj).comp (unitMap T X)=unitMap T U := by
    apply AddMonoidHom.ext
    intro n
    change T.restrict j hj (n • T.unit X)=n • T.unit U
    rw [map_zsmul,T.restrict_unit]
  constructor
  · intro a b hab
    apply hunit.1
    have h := congrArg (T.restrict j hj) hab
    exact (congrArg (fun f : ℤ→+G U => f a) hcomp).symm.trans
      (h.trans (congrArg (fun f : ℤ→+G U => f b) hcomp))
  · intro x
    obtain ⟨n,hn⟩ := hunit.2 (T.restrict j hj x)
    refine ⟨n,hres.1 ?_⟩
    exact (congrArg (fun f : ℤ→+G U => f n) hcomp).trans hn

#print axioms unitMap
#print axioms isoEquiv
#print axioms isoEquiv_unit
#print axioms unit_generated_of_iso
#print axioms unit_injective_of_iso
#print axioms restriction_bijective
#print axioms unit_bijective_of_restriction
end Verification.SchemeGZeroConsequences
