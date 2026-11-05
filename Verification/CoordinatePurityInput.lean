/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GeometricCellularSource
import Verification.ConormalFrame
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Coordinate Purity Input

A uniform standard homotopy-purity input for actual smooth coordinate
pairs. Both sides are literal localization cones of schemes. The frame is
the basis of the actual conormal module I/I², with its original generators;
no exchange stratum decomposition or cellular differential is an input.
-/
noncomputable section
namespace Verification.CoordinatePurityInput
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
universe w
variable (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype ι]
variable (x : ι → A)

structure Frame where
  smooth : Algebra.Smooth R A
  closedSmooth : Algebra.Smooth R (A ⧸ ConormalFrame.ideal x)
  regular : ∀ l : List ι, l.Nodup → RingTheory.Sequence.IsRegular A (l.map x)
  basis : Basis ι (A ⧸ ConormalFrame.ideal x) (ConormalFrame.ideal x).Cotangent
  basis_generator : ∀ i,basis i = ConormalFrame.frame x i

def puncture : (Spec (CommRingCat.of A)).Opens := ⨆ i,PrimeSpectrum.basicOpen (x i)

variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)

def pairArrow : G.obj (puncture A ι x).toScheme ⟶ G.obj (Spec (CommRingCat.of A)) :=
  G.map (puncture A ι x).ι

def relative : DerivedCategory C := DerivedCategory.Q.obj (mappingCone (pairArrow A ι x G))

def normalThom : DerivedCategory C :=
  relative (MvPolynomial ι (A ⧸ ConormalFrame.ideal x)) ι MvPolynomial.X G

/-- The cited purity theorem, uniformly in actual smooth framed pairs over R.
The choice of chains theory and the hypotheses on the base for that theorem
remain explicit external mathematical inputs. -/
structure StandardPurity where
  comparison : ∀ (A ι : Type) [CommRing A] [Algebra R A] [Fintype ι] (x : ι → A),
    Frame R A ι x → (relative A ι x G ≅ normalThom A ι x G)

#print axioms Frame
#print axioms puncture
#print axioms pairArrow
#print axioms relative
#print axioms normalThom
#print axioms StandardPurity
end Verification.CoordinatePurityInput
