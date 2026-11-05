/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ThomPermutationInput
import Verification.GradedMilnorWittSheaf

/-!
# Graded Milnor Witt Thom Orientation

Uniform ordinary quadratic Thom action on genuine graded MW sections.
The action of any power and its totalization are derived internally.
-/
noncomputable section
namespace Verification.GradedMilnorWittThomOrientation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ)

variable (R : Type) [CommRing R]
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (T : LocalizedThomSections.Standard J L G R site M N)


variable (O : ThomPermutationInput.Standard J L G R site M N T)

variable (W : GradedMilnorWittSheaf.Standard site N)
open Verification.GradedSectionTotal

structure Normalization : Prop where
  negative : ∀ (S : Type) [CommRing S] [Algebra R S] (_hs : Algebra.Smooth R S) (q : ℤ)
    (a : (N q).val.obj (Opposite.op (Spec (CommRingCat.of S)))),
    includeDegree (W.grading (CommRingCat.of S)) q (O.orientation S q (-1) a)=
      (W.symbols (CommRingCat.of S)).g*includeDegree (W.grading (CommRingCat.of S)) q a

variable (H : Normalization J L G R site M N T O W)
variable (S : Type) [CommRing S] [Algebra R S] (hs : Algebra.Smooth R S) (q : ℤ)

include H hs in
omit [J.Additive] [L.Additive] in
theorem orientation_power (ν : ℕ)
    (a : (N q).val.obj (Opposite.op (Spec (CommRingCat.of S)))) :
    includeDegree (W.grading (CommRingCat.of S)) q ((O.orientation S q (-1)^ν) a)=
      (W.symbols (CommRingCat.of S)).g^ν*includeDegree (W.grading (CommRingCat.of S)) q a := by
  induction ν with
  | zero => simp
  | succ ν ih =>
      rw [pow_succ',Module.End.mul_apply,H.negative S hs q,ih,pow_succ',mul_assoc]

def totalOrientation (ν : ℕ) : W.Total (CommRingCat.of S) →+ W.Total (CommRingCat.of S) :=
  reindexMap (W.grading (CommRingCat.of S)) (W.grading (CommRingCat.of S)) id
    (fun q => (O.orientation S q (-1)^ν).toAddMonoidHom)

omit [J.Additive] [L.Additive] in
theorem totalOrientation_degree (ν : ℕ)
    (a : (N q).val.obj (Opposite.op (Spec (CommRingCat.of S)))) :
    totalOrientation J L G R site M N T O W S ν
      (includeDegree (W.grading (CommRingCat.of S)) q a)=
    includeDegree (W.grading (CommRingCat.of S)) q ((O.orientation S q (-1)^ν) a) :=
  reindexMap_degree (W.grading (CommRingCat.of S)) (W.grading (CommRingCat.of S)) id
    (fun q => (O.orientation S q (-1)^ν).toAddMonoidHom) q a

include H hs in
omit [J.Additive] [L.Additive] in
theorem total_formula (ν : ℕ) (a : W.Total (CommRingCat.of S)) :
    totalOrientation J L G R site M N T O W S ν a=(W.symbols (CommRingCat.of S)).g^ν*a := by
  have he : totalOrientation J L G R site M N T O W S ν=
      AddMonoidHom.mulLeft ((W.symbols (CommRingCat.of S)).g^ν) := by
    apply GradedSectionTotal.hom_ext (W.grading (CommRingCat.of S))
    intro q x
    rw [totalOrientation_degree]
    exact orientation_power J L G R site M N T O W H S hs q ν x
  exact DFunLike.congr_fun he a

#print axioms Normalization
#print axioms orientation_power
#print axioms totalOrientation
#print axioms totalOrientation_degree
#print axioms total_formula
end Verification.GradedMilnorWittThomOrientation
