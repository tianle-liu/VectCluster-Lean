/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.Functor

/-!
# Module Additive Lift Complex

Forgetting the integer module structure and changing universes preserves
cohomology. Degreewise additive equivalences therefore suffice to compare a
small integer complex with an abelian-group complex in any universe.
-/
noncomputable section
namespace Verification.ModuleAdditiveLiftComplex
open CategoryTheory CategoryTheory.Limits
universe v

def functor : ModuleCat.{0} ℤ ⥤ AddCommGrp.{v} :=
  forget₂ (ModuleCat.{0} ℤ) AddCommGrp.{0} ⋙ AddCommGrp.uliftFunctor.{v,0}

def additive : (functor.{v}).Additive := by
  unfold functor
  infer_instance
attribute [instance] additive

def preservesHomology : (functor.{v}).PreservesHomology := by
  unfold functor
  infer_instance
attribute [instance] preservesHomology

def complex (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) : CochainComplex AddCommGrp.{v} ℕ :=
  ((functor.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).obj C

def homologyEquiv (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) :
    C.homology p ≃+ (complex.{v} C).homology p :=
  (AddEquiv.ulift.symm).trans
    (((C.sc p).mapHomologyIso (functor.{v})).symm.addCommGroupIsoToAddEquiv)

def iso (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (D : CochainComplex AddCommGrp.{v} ℕ)
    (e : ∀ p, C.X p ≃+ D.X p)
    (h : ∀ p x, D.d p (p+1) (e p x) = e (p+1) (C.d p (p+1) x)) :
    complex.{v} C ≅ D :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (AddEquiv.ulift.trans (e p)).toAddCommGrpIso) (by
      intro p q hpq
      have hq : p+1=q := hpq
      subst q
      apply AddCommGrp.hom_ext
      apply AddMonoidHom.ext
      intro x
      exact h p x.down)

#print axioms functor
#print axioms additive
#print axioms preservesHomology
#print axioms complex
#print axioms homologyEquiv
#print axioms iso
end Verification.ModuleAdditiveLiftComplex
