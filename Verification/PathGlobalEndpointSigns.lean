/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathGlobalAffineSigns
import Verification.PathAffineRightEndpoint
import Verification.PathEndpointTotal

/-!
# Path Global Endpoint Signs

Global affine signs respect the actual constant endpoint projectors,
with the original right endpoint parity recovered from each stratum.
-/

namespace Verification.PathGlobalEndpointSigns

open Classical Verification.PathCompression Verification.PathCochains
  Verification.PathRhoFinite Verification.PathEndpointTotal
  Verification.PathAffineLeftEndpoint Verification.PathAffineRightEndpoint
  Verification.PathGlobalAffineSigns

variable {R : Type*} [CommRing R] (g ρ : R)

theorem last_sign_original (a b : Bool) (n : ℕ) (I : Config n) :
    signAt a b ((available I.val (n+2)).card-1)=signAt a b (n+1) := by
  have hp : 0 < (available I.val (n+2)).card :=
    Finset.card_pos.mpr ⟨0,zero_available I.property (by omega)⟩
  have hc := available_card I.property
  rw [signAt_parity,signAt_parity]
  have he : ((available I.val (n+2)).card-1)%2=(n+1)%2 := by omega
  rw [he]

/-- The left projector changes by its actual first-coordinate sign. -/
theorem left_quotient (a b : Bool) (k : R) (n : ℕ) :
    (left k n).comp ((totalSign g ρ a b n).comp (left (flipConstant g ρ a k) n))=
      (left k n).comp (totalSign g ρ a b n) := by
  apply LinearMap.ext
  intro x
  funext I
  apply Subtype.ext
  change Verification.PathLeftEndpoint.projection k
    (stratumFactor g a b I.val • Verification.PathAffineSigns.signMap g ρ a b
      (Verification.PathLeftEndpoint.projection (flipConstant g ρ a k) (x I).val))=
    Verification.PathLeftEndpoint.projection k
      (stratumFactor g a b I.val • Verification.PathAffineSigns.signMap g ρ a b (x I).val)
  rw [map_smul,map_smul]
  congr 1
  exact LinearMap.congr_fun (left_sign_quotient g ρ a b k) (x I).val

/-- The right endpoint uses original coordinate n+1 in every independent stratum. -/
theorem right_quotient (a b : Bool) (k : R) (n : ℕ) :
    (right k n).comp ((totalSign g ρ a b n).comp
      (right (flipConstant g ρ (signAt a b (n+1)) k) n))=
        (right k n).comp (totalSign g ρ a b n) := by
  apply LinearMap.ext
  intro x
  funext I
  apply Subtype.ext
  change Verification.PathRightEndpoint.projection k
    (stratumFactor g a b I.val • Verification.PathAffineSigns.signMap g ρ a b
      (Verification.PathRightEndpoint.projection (flipConstant g ρ (signAt a b (n+1)) k) (x I).val))=
    Verification.PathRightEndpoint.projection k
      (stratumFactor g a b I.val • Verification.PathAffineSigns.signMap g ρ a b (x I).val)
  rw [map_smul,map_smul]
  congr 1
  have hp : 0 < (available I.val (n+2)).card :=
    Finset.card_pos.mpr ⟨0,zero_available I.property (by omega)⟩
  have he : (available I.val (n+2)).card-1+1=(available I.val (n+2)).card := by omega
  have hh := layer_quotient g ρ a b k ((available I.val (n+2)).card-1) (x I).val
    (by simpa only [he] using (x I).property)
  rw [last_sign_original a b n I] at hh
  exact hh

/-- Both independent endpoint relations descend simultaneously on an even path. -/
theorem both_quotient (a b : Bool) (l r : R) (m : ℕ) :
    ((left l (2*m)).comp (right r (2*m))).comp ((totalSign g ρ a b (2*m)).comp
      ((left (flipConstant g ρ a l) (2*m)).comp
        (right (flipConstant g ρ (signAt a b (2*m+1)) r) (2*m))))=
      ((left l (2*m)).comp (right r (2*m))).comp (totalSign g ρ a b (2*m)) := by
  apply LinearMap.ext
  intro x
  have hc (y : Total (R := R) (2*m)) :
      left l (2*m) (right r (2*m) y)=right r (2*m) (left l (2*m) y) :=
    LinearMap.congr_fun (endpoints_commute l r m) y
  have hl (y : Total (R := R) (2*m)) := LinearMap.congr_fun (left_quotient g ρ a b l (2*m)) y
  have hr (y : Total (R := R) (2*m)) := LinearMap.congr_fun (right_quotient g ρ a b r (2*m)) y
  simp only [LinearMap.comp_apply] at hl hr ⊢
  rw [hc,hl,← hc,hr]

#print axioms last_sign_original
#print axioms left_quotient
#print axioms right_quotient
#print axioms both_quotient

end Verification.PathGlobalEndpointSigns
