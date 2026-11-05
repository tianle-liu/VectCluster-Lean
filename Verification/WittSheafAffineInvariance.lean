/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.WittSheafSectionsInput

/-!
# Witt Sheaf Affine Invariance

Ordinary affine-space invariance and functorial transport for the
ring presheaf of Witt sheaf sections. No cluster scheme occurs here.
-/
noncomputable section
namespace Verification.WittSheafAffineInvariance
open CategoryTheory AlgebraicGeometry Opposite
open Verification.WittSheafSectionsInput
variable (R : Type) [CommRing R] (W : Scheme.{0}ᵒᵖ ⥤ CommRingCat.{0})

omit [CommRing R] in
theorem pullback_id (S : Type) [CommRing S] : pullback W (RingHom.id S) = RingHom.id _ := by
  ext a
  simp [pullback]

omit [CommRing R] in
theorem pullback_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U]
    (f : S →+* T) (g : T →+* U) :
    pullback W (g.comp f) = (pullback W g).comp (pullback W f) := by
  simp only [pullback,← CommRingCat.hom_comp,← Functor.map_comp]
  rw [CommRingCat.ofHom_comp,Spec.map_comp,op_comp]

omit [CommRing R] in
def ringEquiv {S T : Type} [CommRing S] [CommRing T] (e : S ≃+* T) :
    RingSection W S ≃+* RingSection W T :=
  RingEquiv.ofHomInv (pullback W e.toRingHom) (pullback W e.symm.toRingHom)
    (by exact (pullback_comp W e.toRingHom e.symm.toRingHom).symm.trans
          (by rw [e.symm_toRingHom_comp_toRingHom,pullback_id]))
    (by exact (pullback_comp W e.symm.toRingHom e.toRingHom).symm.trans
          (by rw [e.toRingHom_comp_symm_toRingHom,pullback_id]))

structure Standard : Prop where
  polynomial : ∀ (S ι : Type) [CommRing S] [Algebra R S] [Fintype ι],
    Algebra.Smooth R S → Function.Bijective (pullback W (MvPolynomial.C : S →+* MvPolynomial ι S))

variable (H : Standard R W)

def polynomialEquiv (S ι : Type) [CommRing S] [Algebra R S] [Fintype ι]
    (hs : Algebra.Smooth R S) : RingSection W S ≃+* RingSection W (MvPolynomial ι S) :=
  RingEquiv.ofBijective (pullback W MvPolynomial.C) (H.polynomial S ι hs)

#print axioms pullback_id
#print axioms pullback_comp
#print axioms ringEquiv
#print axioms Standard
#print axioms polynomialEquiv
end Verification.WittSheafAffineInvariance
