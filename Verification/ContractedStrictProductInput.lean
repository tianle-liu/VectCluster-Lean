/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictNisnevichContraction
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.RingTheory.Smooth.Basic

/-!
# Contracted Strict Product Input

Uniform use of the ordinary cellular product formula (Morel--Sawant,
Lemma 2.31) when both given projective cellular complexes are contracted
to degree zero. Tensoring chain homotopies gives the displayed contraction.
This is an explicit literature input for arbitrary smooth affine algebras;
it contains no path, exchange matrix, coefficient normalization, or claim
that a supplied factor is contractible. Those contractions must be proved
before this input can be used.
-/
noncomputable section
namespace Verification.ContractedStrictProductInput
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [MonoidalCategory A] [MonoidalPreadditive A]
variable [Category C] [Abelian C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) (G : Scheme ⥤ CochainComplex C ℤ)
variable (k : Type) [Field k]

structure ContractedModel (X : D) (U : A) where
  model : StrictProjectiveModel.Model J X
  upper : model.complex.IsStrictlyLE 0
  contraction : HomotopyEquiv model.complex ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj U)

structure Standard where
  product : ∀ (S T : Type) [CommRing S] [CommRing T] [Algebra k S] [Algebra k T]
    [Algebra.Smooth k S] [Algebra.Smooth k T]
    (P : StrictProjectiveModel.Model J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of S))))))
    (Q : StrictProjectiveModel.Model J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of T))))))
    (U V : A),
    P.complex.IsStrictlyLE 0 → Q.complex.IsStrictlyLE 0 →
    HomotopyEquiv P.complex ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj U) →
    HomotopyEquiv Q.complex ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj V) →
    ContractedModel J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (TensorProduct k S T)))))) (U⊗V)

variable (MS : Standard J L G k)
variable (S T : Type) [CommRing S] [CommRing T] [Algebra k S] [Algebra k T]
variable [Algebra.Smooth k S] [Algebra.Smooth k T]

def combine {U V : A}
    (P : ContractedModel J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of S))))) U)
    (Q : ContractedModel J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of T))))) V) :
    ContractedModel J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (TensorProduct k S T)))))) (U⊗V) :=
  MS.product S T P.model Q.model U V P.upper Q.upper P.contraction Q.contraction

variable (Nis : StrictNisnevichInput.Theory A)
variable (NR : StrictNisnevichRepresentability.Standard J L G Nis k)
variable (HC : StrictCoefficientComparison.StandardHomology (A:=A))

include NR HC in
omit [MonoidalCategory A] [MonoidalPreadditive A] [CommRing T] [Algebra k T] [Algebra.Smooth k T] in
theorem vanishes {U : A}
    (P : ContractedModel J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of S))))) U)
    (F : A) (p : ℕ) (hp : 0<p) : IsZero (Nis.cohomology (Spec (CommRingCat.of S)) F p) :=
  StrictNisnevichContraction.vanishes J L G Nis k NR HC S P.model P.upper P.contraction F p hp

#print axioms ContractedModel
#print axioms Standard
#print axioms combine
#print axioms vanishes
end Verification.ContractedStrictProductInput
