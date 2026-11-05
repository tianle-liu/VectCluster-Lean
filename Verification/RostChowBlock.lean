/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostSupportDivisorInput
import Verification.RostBoundaryTransportValues

/-!
# Rost Chow Block

The actual bottom Milnor differential block in weights one and zero.
All degree transports are proved from integer identities; they add no
residue or component hypothesis.
-/
noncomputable section
set_option maxHeartbeats 1000000
namespace Verification.RostChowBlock
open CategoryTheory AlgebraicGeometry
open Verification.RostCanonicalCoefficients
variable (T : RostAffineInput.Theory)
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (Allowed : Finset V → Prop) (p : ℕ)
variable (I : PrimeLayerCover.Index Allowed p) (J : PrimeLayerCover.Index Allowed (p+1))

def sourceIso : RostSupportRowBlocks.Term T A V x Allowed (p+1) p I ≅
    Sections T (PrimeStratumPresentation.ClosedRing x I.val) 1 :=
  eqToIso (congrArg (fun w => Sections T (PrimeStratumPresentation.ClosedRing x I.val) w)
    (by push_cast; ring : ((p+1:ℕ):ℤ) - (p:ℤ) = 1))

def targetIso : RostSupportRowBlocks.Term T A V x Allowed (p+1) (p+1) J ≅
    Sections T (PrimeStratumPresentation.ClosedRing x J.val) 0 :=
  eqToIso (congrArg (fun w => Sections T (PrimeStratumPresentation.ClosedRing x J.val) w)
    (sub_self ((p+1:ℕ):ℤ)))

def block (D : RostSupportInput.Data T A V x Allowed (p+1)) :
    Sections T (PrimeStratumPresentation.ClosedRing x I.val) 1 ⟶
      Sections T (PrimeStratumPresentation.ClosedRing x J.val) 0 :=
  (sourceIso T A V x Allowed p I).inv ≫
    RostSupportRowBlocks.block T A V x Allowed (p+1) D p I J ≫
      (targetIso T A V x Allowed p J).hom

variable (P : RostPrincipalLocalizationInput.Theory T)
variable (k : Type) [Field k] [Algebra k A] [Algebra.Smooth k A]
variable (v : J.val) [Algebra k (RostSupportDivisorInput.Face A V x J.val v)]
variable [Algebra.Smooth k (RostSupportDivisorInput.Face A V x J.val v)]
variable (hreg : IsRegular (RostSupportDivisorInput.parameter A V x J.val v))
variable (e : RostSupportDivisorInput.Coordinates A V x I.val J.val v)

omit [Algebra k A] [Algebra.Smooth k A] in
/-- Degree equality transports commute with the same family of boundaries. -/
theorem weight_cast (w z : ℤ) (h1 : w = 1) (hz : w-1 = z) (h0 : z = 0) :
    (eqToIso (congrArg (fun a => Sections T (PrimeStratumPresentation.ClosedRing x I.val) a) h1)).inv ≫
      (T.iso (Scheme.Spec.mapIso e.source.toRingEquiv.toCommRingCatIso.symm.op) w 0).hom ≫
      P.boundary k (RostSupportDivisorInput.Face A V x J.val v)
        (RostSupportDivisorInput.parameter A V x J.val v) hreg w ≫
      (T.iso (Scheme.Spec.mapIso e.target.toRingEquiv.toCommRingCatIso.symm.op) (w-1) 0).hom ≫
      (eqToIso (congrArg (fun a => Sections T (PrimeStratumPresentation.ClosedRing x J.val) a) hz)).hom ≫
      (eqToIso (congrArg (fun a => Sections T (PrimeStratumPresentation.ClosedRing x J.val) a) h0)).hom =
    (transport T e.source.toRingEquiv 1).toAddCommGrpIso.hom ≫
      P.boundary k (RostSupportDivisorInput.Face A V x J.val v)
        (RostSupportDivisorInput.parameter A V x J.val v) hreg 1 ≫
          (transport T e.target.toRingEquiv 0).toAddCommGrpIso.hom := by
  subst w
  subst z
  simp only [eqToIso_refl,Category.id_comp,Category.comp_id]
  rfl

omit [Algebra k A] [Algebra.Smooth k A] in
theorem localBoundary :
    (sourceIso T A V x Allowed p I).inv ≫
      RostSupportDivisorInput.localBoundary T P A V x Allowed k (p+1) p I J v hreg e ≫
        (targetIso T A V x Allowed p J).hom =
    (transport T e.source.toRingEquiv 1).toAddCommGrpIso.hom ≫
      P.boundary k (RostSupportDivisorInput.Face A V x J.val v)
        (RostSupportDivisorInput.parameter A V x J.val v) hreg 1 ≫
          (transport T e.target.toRingEquiv 0).toAddCommGrpIso.hom := by
  unfold sourceIso targetIso RostSupportDivisorInput.localBoundary
  simp only [Category.assoc]
  exact weight_cast T A V x Allowed p I J P k v hreg e
    ((p:ℤ)+1-p) ((p:ℤ)+1-((p+1:ℕ):ℤ)) (by omega) (by push_cast; ring) (by push_cast; ring)

#print axioms sourceIso
#print axioms targetIso
#print axioms block
#print axioms weight_cast
#print axioms localBoundary
end Verification.RostChowBlock
