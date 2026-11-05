/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AffineSheafContraction

/-!
# Actual Sheaf Contraction Restriction

The genuine coefficient-sheaf restriction preserves the u=1 kernel
because the actual torus-face ring homomorphism preserves that basepoint.
-/
noncomputable section
namespace Verification.ActualSheafContractionRestriction
open CategoryTheory AlgebraicGeometry Opposite
variable (site : GrothendieckTopology Scheme.{0})
variable (N : Sheaf site (ModuleCat.{0} ℤ))
variable {S T U : Type} [CommRing S] [CommRing T] [CommRing U]

def pullback (f : S →+* T) : N.val.obj (op (Spec (CommRingCat.of S))) →+
    N.val.obj (op (Spec (CommRingCat.of T))) where
  toFun a := N.val.map (Spec.map (CommRingCat.ofHom f)).op a
  map_zero' := map_zero _
  map_add' a b := map_add _ a b

theorem pullback_comp (f : S →+* T) (g : T →+* U) :
    pullback site N (g.comp f) = (pullback site N g).comp (pullback site N f) := by
  apply AddMonoidHom.ext
  intro a
  change N.val.map (Spec.map (CommRingCat.ofHom (g.comp f))).op a =
    N.val.map (Spec.map (CommRingCat.ofHom g)).op
      (N.val.map (Spec.map (CommRingCat.ofHom f)).op a)
  rw [CommRingCat.ofHom_comp, Spec.map_comp, op_comp, Functor.map_comp]
  rfl

variable (R ι κ τ : Type) [CommRing R] [Fintype κ]
variable (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (v : ι)
variable (Ns : ℤ → Sheaf site (ModuleCat.{0} ℤ)) (q : ℤ)
local notation "New" => ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R ι κ τ B)
local notation "Old" => ActualTorusReducedRestriction.OldBase R ι κ τ B v

theorem basepoint_square
    (a : (Ns q).val.obj (op (Spec (CommRingCat.of (LaurentBasepoint.Laurent Old))))) :
    AffineSheafContraction.sheafAtOne R New site Ns q
      (pullback site (Ns q) (ActualTorusFace.torusFace R ι κ τ B v).toRingHom a) =
    pullback site (Ns q) (ActualTorusReducedRestriction.fiberRestriction R ι κ τ B v).toRingHom
      (AffineSheafContraction.sheafAtOne R Old site Ns q a) := by
  have h := congrArg (fun f : LaurentBasepoint.Laurent Old →ₐ[R] New => pullback site (Ns q) f.toRingHom)
    (ActualTorusBasepointNaturality.atOne_square R ι κ τ B v)
  change pullback site (Ns q) ((LaurentBasepoint.atOne R New).toRingHom.comp
      (ActualTorusFace.torusFace R ι κ τ B v).toRingHom) =
    pullback site (Ns q) ((ActualTorusReducedRestriction.fiberRestriction R ι κ τ B v).toRingHom.comp
      (LaurentBasepoint.atOne R Old).toRingHom) at h
  rw [pullback_comp, pullback_comp] at h
  exact DFunLike.congr_fun h a

def restriction : (AffineSheafContraction.sheafAtOne R Old site Ns q).ker →+
    (AffineSheafContraction.sheafAtOne R New site Ns q).ker where
  toFun a := ⟨pullback site (Ns q) (ActualTorusFace.torusFace R ι κ τ B v).toRingHom a.val, by
    have h := basepoint_square site R ι κ τ B v Ns q a.val
    have ha : AffineSheafContraction.sheafAtOne R Old site Ns q a.val = 0 := a.property
    rw [ha, map_zero] at h
    exact h⟩
  map_zero' := by apply Subtype.ext; simp only [AddSubgroup.coe_zero, map_zero]
  map_add' a b := by apply Subtype.ext; simp only [AddSubgroup.coe_add, map_add]

#print axioms pullback
#print axioms pullback_comp
#print axioms basepoint_square
#print axioms restriction
end Verification.ActualSheafContractionRestriction
