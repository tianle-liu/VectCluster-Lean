/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCoefficientCochains
import Verification.StrictProjectiveModel

/-!
# Strict Coefficient Comparison

Coefficient cohomology from the actual cross-category strict-model
universal property. Ordinary bounded-projective Hom-complex computation
is isolated as a uniform homological-algebra input. J need not be fully
faithful. The cochain and ambient Hom universes may differ.
-/
noncomputable section
namespace Verification.StrictCoefficientComparison
open CategoryTheory CategoryTheory.Limits
universe w v u v' u'
variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{w} A]

def target (M : A) (q : ℕ) : DerivedCategory A :=
  ((DerivedCategory.singleFunctor A 0).obj M)⟦(q : ℤ)⟧

structure StandardHomology where
  comparison : ∀ (P : CochainComplex A ℤ),ProjectiveConeTerms.Bounded P →
    (∀ i,Projective (P.X i)) → P.IsStrictlyLE 0 → ∀ (M : A) (q : ℕ),
    ((StrictCoefficientCochains.complex P M).homology q ≃+
      (DerivedCategory.Q.obj P ⟶ target M q))

variable {D : Type u'} [Category.{v'} D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (H : StandardHomology (A := A)) {X : D} (P : StrictProjectiveModel.Model J X)
variable (hp : P.complex.IsStrictlyLE 0)

def cohomologyEquiv (M : A) (q : ℕ) :
    (StrictCoefficientCochains.complex P.complex M).homology q ≃+
      (X ⟶ J.obj (target M q)) :=
  (H.comparison P.complex P.bounded P.projective hp M q).trans
    (AddEquiv.ofBijective (StrictTriangleHom.comparison J P.comparison (target M q))
      (P.universal (target M q)))

include H hp in
theorem ambient_subsingleton (M : A) (q : ℕ)
    (hz : IsZero ((StrictCoefficientCochains.complex P.complex M).homology q)) :
    Subsingleton (X ⟶ J.obj (target M q)) := by
  let e := cohomologyEquiv J H P hp M q
  have hzero (x : (StrictCoefficientCochains.complex P.complex M).homology q) : x=0 :=
    congrArg (fun f : (StrictCoefficientCochains.complex P.complex M).homology q ⟶
      (StrictCoefficientCochains.complex P.complex M).homology q => f x)
      (hz.eq_of_src (𝟙 _) 0)
  have hezero (f : X ⟶ J.obj (target M q)) : f=0 := by
    calc f=e (e.symm f) := (e.apply_symm_apply f).symm
         _=e 0 := congrArg e (hzero (e.symm f))
         _=0 := map_zero e
  exact ⟨fun f g => (hezero f).trans (hezero g).symm⟩

include H hp in
theorem ambient_zero {h q : ℕ} (hb : P.complex.IsStrictlyGE (-(h : ℤ))) (hq : h<q)
    (M : A) : IsZero (AddCommGrp.of (X ⟶ J.obj (target M q))) := by
  letI := ambient_subsingleton J H P hp M q
    (StrictCoefficientCochains.homology_zero P.complex M hb hq)
  exact AddCommGrp.isZero_of_subsingleton _

#print axioms target
#print axioms StandardHomology
#print axioms cohomologyEquiv
#print axioms ambient_subsingleton
#print axioms ambient_zero
end Verification.StrictCoefficientComparison
