/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictNisnevichRepresentability

/-!
# Chow Witt Nisnevich Input

Ordinary Chow--Witt cohomology and its unit action, uniformly for all
smooth affine algebras. MW p denotes the ordinary degree-p Milnor--Witt
coefficient object. The Chow--Witt comparison and ordinary representability
are required to intertwine the usual actions of all regular units.
No exchange scheme, Euler bijectivity, or orbit classification is an input.
-/
noncomputable section
namespace Verification.ChowWittNisnevichInput
open CategoryTheory AlgebraicGeometry
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) (L : DerivedCategory C ⥤ D)
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (T : StrictNisnevichInput.Theory A) (k : Type) [Field k]
variable (NR : StrictNisnevichRepresentability.Standard J L G T k)
variable (MW : ℕ → A) (CW : Scheme → ℕ → AddCommGrp)

structure Standard where
  comparison : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R] (p : ℕ),
    CW (Spec (CommRingCat.of R)) p ≃+ T.cohomology (Spec (CommRingCat.of R)) (MW p) p
  unitAction : ∀ (R : Type) [CommRing R] [Algebra k R] (p : ℕ),
    MulAction Rˣ (CW (Spec (CommRingCat.of R)) p)
  ambientAction : ∀ (R : Type) [CommRing R] [Algebra k R] (p : ℕ),
    MulAction Rˣ (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of R)))) ⟶
      J.obj (StrictCoefficientComparison.target (MW p) p))
  unit_naturality : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    (p : ℕ) (u : Rˣ) (x : CW (Spec (CommRingCat.of R)) p),
    letI := unitAction R p
    letI := ambientAction R p
    NR.comparison R (MW p) p (comparison R p (u • x)) =
      u • NR.comparison R (MW p) p (comparison R p x)

variable (S : Standard J L G T k NR MW CW)
variable (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R] (p : ℕ)

def ambientEquiv : CW (Spec (CommRingCat.of R)) p ≃+
    (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of R)))) ⟶
      J.obj (StrictCoefficientComparison.target (MW p) p)) :=
  (S.comparison R p).trans (NR.comparison R (MW p) p)

theorem ambient_smul (u : Rˣ) (x : CW (Spec (CommRingCat.of R)) p) :
    letI := S.unitAction R p
    letI := S.ambientAction R p
    ambientEquiv J L G T k NR MW CW S R p (u • x) =
      u • ambientEquiv J L G T k NR MW CW S R p x :=
  S.unit_naturality R p u x

#print axioms Standard
#print axioms ambientEquiv
#print axioms ambient_smul
end Verification.ChowWittNisnevichInput
