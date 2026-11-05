/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostSupportRowBlocks
import Verification.RostPrincipalLocalizationInput
import Verification.CoordinateFlag

/-!
# Rost Support Divisor Input

The ordinary first support differential is local principal localization.
Every chart here is formed from arbitrary coordinate rings. The comparison
uses algebra equivalences over the original ambient algebra, so arbitrary
relabelings of stratum coefficients are not silently treated as natural.
No exchange matrix, component quotient, or coordinate valuation occurs.
-/
noncomputable section
namespace Verification.RostSupportDivisorInput
open CategoryTheory AlgebraicGeometry
open Classical
variable (T : RostAffineInput.Theory) (S : RostSupportInput.Theory T)
variable (P : RostPrincipalLocalizationInput.Theory T)
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (Allowed : Finset V → Prop)

abbrev Chart (J : Finset V) := PrimeStratumPresentation.OpenRing x J
abbrev Face (J : Finset V) (v : J) :=
  CoordinateFlag.ClosedOld (Chart A V x J) J
    (fun i => algebraMap A (Chart A V x J) (x i.val)) v

def parameter (J : Finset V) (v : J) : Face A V x J v :=
  CoordinateFlag.parameter (Chart A V x J) J
    (fun i => algebraMap A (Chart A V x J) (x i.val)) v

/-- Geometric identifications required from the caller. They preserve all
ambient functions, because they are equivalences of A-algebras. -/
structure Coordinates (I J : Finset V) (v : J) where
  source : PrimeStratumPresentation.ClosedRing x I ≃ₐ[A]
    RostPrincipalLocalizationInput.OpenRing (Face A V x J v) (parameter A V x J v)
  target : RostPrincipalLocalizationInput.ClosedRing (Face A V x J v)
    (parameter A V x J v) ≃ₐ[A] PrimeStratumPresentation.ClosedRing x J

/-- The usual hypotheses for the support sequence; these are not new
mathematical inputs beyond RostSupportInput.Theory.sequence. -/
structure Filtration where
  cover : ∀ p : PrimeSpectrum A,Allowed (PrimeCoordinateFiltration.zeroSet x p)
  regular : ∀ I,Allowed I → RingTheory.Sequence.IsWeaklyRegular
    (PrimeStratumPresentation.OpenRing x I)
    ((CoordinateKoszulClass.equations A V x I).map
      (algebraMap A (PrimeStratumPresentation.OpenRing x I)))

variable (k : Type) [Field k] [Algebra k A] [Algebra.Smooth k A]
variable (F : Filtration A V x Allowed)

def row (s : ℤ) : RostSupportInput.Data T A V x Allowed s :=
  S.sequence k A V x Allowed F.cover F.regular s

/-- Transport of the ordinary principal boundary into the actual stratum
terms. Smoothness and regularity of the face must be proved geometrically. -/
def localBoundary (s : ℤ) (p : ℕ) (I : PrimeLayerCover.Index Allowed p)
    (J : PrimeLayerCover.Index Allowed (p+1)) (v : J.val)
    [Algebra k (Face A V x J.val v)] [Algebra.Smooth k (Face A V x J.val v)]
    (hreg : IsRegular (parameter A V x J.val v))
    (e : Coordinates A V x I.val J.val v) :
    RostSupportRowBlocks.Term T A V x Allowed s p I ⟶
      RostSupportRowBlocks.Term T A V x Allowed s (p+1) J :=
  (T.iso (Scheme.Spec.mapIso e.source.toRingEquiv.toCommRingCatIso.symm.op) (s-p) 0).hom ≫
    P.boundary k (Face A V x J.val v) (parameter A V x J.val v) hreg (s-p) ≫
      (T.iso (Scheme.Spec.mapIso e.target.toRingEquiv.toCommRingCatIso.symm.op)
        ((s-p)-1) 0).hom ≫
      (eqToIso (congrArg (fun w =>
        (T.cycles (Spec (CommRingCat.of (PrimeStratumPresentation.ClosedRing x J.val))) w).homology 0)
        (by push_cast; ring : (s-(p:ℤ))-1 = s-((p+1:ℕ):ℤ)))).hom

/-- B-free locality and the ordinary first-differential/localization law.
This does not specify the value of a residue. The separately cited valuation
normalization and the original geometric multiplicity calculation are still
required before this interface can yield a Chow formula. -/
structure Standard : Prop where
  nonincident : ∀ s p (I : PrimeLayerCover.Index Allowed p)
    (J : PrimeLayerCover.Index Allowed (p+1)),¬ I.val ⊆ J.val →
    RostSupportRowBlocks.block T A V x Allowed s (row T S A V x Allowed k F s) p I J = 0
  adjacent : ∀ s p (I : PrimeLayerCover.Index Allowed p)
    (J : PrimeLayerCover.Index Allowed (p+1)) (v : J.val),I.val = J.val.erase v.val →
    ∀ [Algebra k (Face A V x J.val v)] [Algebra.Smooth k (Face A V x J.val v)]
      (hreg : IsRegular (parameter A V x J.val v))
      (e : Coordinates A V x I.val J.val v),
    RostSupportRowBlocks.block T A V x Allowed s (row T S A V x Allowed k F s) p I J =
      localBoundary T P A V x Allowed k s p I J v hreg e

#print axioms Chart
#print axioms Face
#print axioms parameter
#print axioms Coordinates
#print axioms Filtration
#print axioms row
#print axioms localBoundary
#print axioms Standard
end Verification.RostSupportDivisorInput
