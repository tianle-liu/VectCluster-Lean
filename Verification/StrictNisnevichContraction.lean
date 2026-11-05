/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCoefficientHomotopy
import Verification.StrictNisnevichRepresentability

/-!
# Strict Nisnevich Contraction

An actual strict cellular contraction to degree zero implies positive
Nisnevich vanishing for every coefficient object, using only ordinary
bounded-projective Hom computation and smooth-affine representability.
-/
noncomputable section
namespace Verification.StrictNisnevichContraction
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) (G : Scheme ⥤ CochainComplex C ℤ)
variable (Nis : StrictNisnevichInput.Theory A) (k : Type) [Field k]
variable (NR : StrictNisnevichRepresentability.Standard J L G Nis k)
variable (HC : StrictCoefficientComparison.StandardHomology (A:=A))
variable (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R]
variable (P : StrictProjectiveModel.Model J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of R))))))
variable (hp : P.complex.IsStrictlyLE 0) {Q : A}
variable (e : HomotopyEquiv P.complex ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj Q))

include NR HC hp e in
theorem vanishes (M : A) (p : ℕ) (hp' : 0<p) :
    IsZero (Nis.cohomology (Spec (CommRingCat.of R)) M p) := by
  letI := StrictCoefficientComparison.ambient_subsingleton J HC P hp M p
    (StrictCoefficientHomotopy.vanishes P.complex M e p hp')
  exact StrictNisnevichRepresentability.cohomology_zero J L G Nis k NR R M p

#print axioms vanishes
end Verification.StrictNisnevichContraction
