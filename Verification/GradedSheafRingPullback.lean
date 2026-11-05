/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SheafGradedLaurentResidue

/-!
# Graded Sheaf Ring Pullback

Total section pullback is the direct sum of the actual coefficient-sheaf
maps. Ring preservation is an ordinary graded-cohomology reference input;
identity, composition, and every homogeneous component are proved internally.
-/
noncomputable section
namespace Verification.GradedSheafRingPullback
open CategoryTheory AlgebraicGeometry Opposite
open scoped DirectSum
open Verification.GradedSectionTotal Verification.SheafGradedLaurentResidue
variable (site : GrothendieckTopology Scheme.{0})
variable (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable {S T U A B C : Type} [CommRing S] [CommRing T] [CommRing U]
variable [Ring A] [Ring B] [Ring C]
variable (ES : (⨁ q,Section site N S q) ≃+ A)
variable (ET : (⨁ q,Section site N T q) ≃+ B)
variable (EU : (⨁ q,Section site N U q) ≃+ C)

def additive (f : S →+* T) : A →+ B :=
  reindexMap ES ET id (fun q => ActualSheafContractionRestriction.pullback site (N q) f)

theorem additive_degree (f : S →+* T) (q : ℤ) (a : Section site N S q) :
    additive site N ES ET f (includeDegree ES q a)=
      includeDegree ET q (ActualSheafContractionRestriction.pullback site (N q) f a) :=
  reindexMap_degree ES ET id _ q a

theorem additive_comp (f : S →+* T) (g : T →+* U) :
    additive site N ES EU (g.comp f)=
      (additive site N ET EU g).comp (additive site N ES ET f) := by
  apply hom_ext ES
  intro q a
  rw [AddMonoidHom.comp_apply,additive_degree,additive_degree,additive_degree,
    ActualSheafContractionRestriction.pullback_comp,AddMonoidHom.comp_apply]

theorem additive_id : additive site N ES ES (RingHom.id S)=AddMonoidHom.id A := by
  apply hom_ext ES
  intro q a
  rw [additive_degree]
  change includeDegree ES q ((N q).val.map (Spec.map (𝟙 (CommRingCat.of S))).op a)=includeDegree ES q a
  simp only [Spec.map_id,op_id,CategoryTheory.Functor.map_id,ModuleCat.id_apply]

structure Multiplicative (f : S →+* T) : Prop where
  one : additive site N ES ET f 1=1
  mul : ∀ a b,additive site N ES ET f (a*b)=additive site N ES ET f a*additive site N ES ET f b

def ringHom (f : S →+* T) (h : Multiplicative site N ES ET f) : A →+* B where
  __ := additive site N ES ET f
  map_one' := h.one
  map_mul' := h.mul

theorem ringHom_degree (f : S →+* T) (h : Multiplicative site N ES ET f) (q : ℤ) (a : Section site N S q) :
    ringHom site N ES ET f h (includeDegree ES q a)=
      includeDegree ET q (ActualSheafContractionRestriction.pullback site (N q) f a) :=
  additive_degree site N ES ET f q a

theorem ringHom_comp (f : S →+* T) (g : T →+* U)
    (hf : Multiplicative site N ES ET f) (hg : Multiplicative site N ET EU g)
    (hgf : Multiplicative site N ES EU (g.comp f)) :
    ringHom site N ES EU (g.comp f) hgf=(ringHom site N ET EU g hg).comp (ringHom site N ES ET f hf) := by
  apply RingHom.ext
  intro a
  exact congrArg (fun h : A →+ C => h a) (additive_comp site N ES ET EU f g)

#print axioms additive
#print axioms additive_degree
#print axioms additive_comp
#print axioms additive_id
#print axioms Multiplicative
#print axioms ringHom
#print axioms ringHom_degree
#print axioms ringHom_comp
end Verification.GradedSheafRingPullback
