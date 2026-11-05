/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathWeightBasis

/-!
# Path Positive Weight Index

Exact positive MW indices in the path survivor formulas. These are
bijections with the already proved allowed weights, including all lengths
and the empty Y_0 case.
-/

namespace Verification.PathPositiveWeightIndex

open Verification.PathCokernel

abbrev ZIndex (n : ℕ) := {k : Weight false (n+1) // 0<k.val.val}
abbrev YIndex (a : ℕ) := {k : Weight true (2*a) // 0<k.val.val}

def zEquiv (n : ℕ) : ZIndex n ≃ Fin (n+1) where
  toFun k := ⟨k.val.val.val-1,by have h:=k.val.val.isLt;have hp:=k.property;omega⟩
  invFun k := ⟨⟨⟨k.val+1,by have h:=k.isLt;omega⟩,by intro h;cases h⟩,by change 0<k.val+1;omega⟩
  left_inv k := by
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    have h:=k.property
    dsimp only
    omega
  right_inv k := by apply Fin.ext;dsimp only;omega

def yEquiv (a : ℕ) : YIndex a ≃ Fin a where
  toFun k := ⟨k.val.val.val/2-1,by
    have h:=k.val.val.isLt
    have hp:=k.property
    have he:=k.val.property rfl
    omega⟩
  invFun k := ⟨⟨⟨2*(k.val+1),by have h:=k.isLt;omega⟩,by intro _;dsimp only;omega⟩,by change 0<2*(k.val+1);omega⟩
  left_inv k := by
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    have h:=k.property
    have he:=k.val.property rfl
    dsimp only
    omega
  right_inv k := by apply Fin.ext;dsimp only;omega

theorem z_value (n : ℕ) (k : ZIndex n) : (zEquiv n k).val+1=k.val.val.val := by
  change (k.val.val.val-1)+1=k.val.val.val
  have h:=k.property
  omega

theorem y_value (a : ℕ) (k : YIndex a) : 2*((yEquiv a k).val+1)=k.val.val.val := by
  change 2*(k.val.val.val/2-1+1)=k.val.val.val
  have h:=k.property
  have he:=k.val.property rfl
  omega

#print axioms ZIndex
#print axioms YIndex
#print axioms zEquiv
#print axioms yEquiv
#print axioms z_value
#print axioms y_value

end Verification.PathPositiveWeightIndex
