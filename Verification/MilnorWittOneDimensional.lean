/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.MilnorWittSymbolRelations
import Verification.MilnorWittSymbolNaturality

/-!
# Milnor Witt One Dimensional

One-dimensional form classes are derived from the ordinary MW symbol
relations. Their multiplicativity and square-one relation are not additional
inputs; in eta-periodic Witt coefficients the orientation is minus one.
-/
namespace Verification.MilnorWittOneDimensional
open Verification.MilnorWittSymbolRelations
variable {S A : Type*} [CommRing S] [Ring A] (D : Symbols S A)

def oneDim (u : Sˣ) : A := 1 + D.eta * D.symbol u

theorem oneDim_one : oneDim D 1 = 1 := by simp [oneDim,D.one]

theorem oneDim_mul (u v : Sˣ) : oneDim D (u*v) = oneDim D u * oneDim D v := by
  have h : (D.eta*D.symbol u)*(D.eta*D.symbol v) =
      D.eta*D.eta*D.symbol u*D.symbol v := by
    rw [mul_assoc,D.toCoefficients.push_eta]
    simp only [mul_assoc]
  calc
    oneDim D (u*v) = 1 + D.eta*D.symbol u + D.eta*D.symbol v +
        (D.eta*D.symbol u)*(D.eta*D.symbol v) := by
      rw [oneDim,D.product,h]
      noncomm_ring
    _ = oneDim D u * oneDim D v := by unfold oneDim; noncomm_ring

def oneDimHom : Sˣ →* A where
  toFun := oneDim D
  map_one' := oneDim_one D
  map_mul' := oneDim_mul D

theorem oneDim_neg_one : oneDim D (-1) = D.g := by
  have hr : D.symbol (-1) = D.rho := by simpa [D.one] using D.negative 1
  rw [oneDim,hr,D.eta_rho]
  noncomm_ring

theorem oneDim_inverse (u : Sˣ) : oneDim D u⁻¹ = oneDim D u := by
  have h : D.eta*D.g = -D.eta := (D.central_eta D.g).eq.trans D.g_eta
  rw [oneDim,oneDim,D.inverse,neg_mul,mul_neg,← mul_assoc,h,neg_mul,neg_neg]

theorem oneDim_square (u : Sˣ) : oneDim D u * oneDim D u = 1 := by
  have h := oneDim_mul D u u⁻¹
  rw [mul_inv_cancel,oneDim_one,oneDim_inverse] at h
  exact h.symm

theorem orientation_eq_neg_one (hη : IsUnit D.eta) : D.g = -1 := by
  apply hη.mul_right_cancel
  simp [D.g_eta]

theorem witt_negative (hη : IsUnit D.eta) : oneDim D (-1) = -1 := by
  rw [oneDim_neg_one,orientation_eq_neg_one D hη]

theorem map_oneDim {T B : Type*} [CommRing T] [Ring B]
    (D' : Symbols T B) (f : S →+* T) (F : A →+* B)
    (h : MilnorWittSymbolNaturality.Compatible D D' f F) (u : Sˣ) :
    F (oneDim D u) = oneDim D' (Units.map f.toMonoidHom u) := by
  simp [oneDim,h.eta,h.symbol]

#print axioms map_oneDim
#print axioms oneDim
#print axioms oneDim_one
#print axioms oneDim_mul
#print axioms oneDimHom
#print axioms oneDim_neg_one
#print axioms oneDim_inverse
#print axioms oneDim_square
#print axioms orientation_eq_neg_one
#print axioms witt_negative
end Verification.MilnorWittOneDimensional
