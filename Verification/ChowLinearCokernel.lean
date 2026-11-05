/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalChowIncoming
import Verification.AllowedComponentRow

/-!
# Chow Linear Cokernel

The ordinary categorical cokernel is the quotient by the integral
linear image. This supplies the final categorical assembly of the actual
Chow comparison after its image has been computed.
-/
noncomputable section
namespace Verification.ChowLinearCokernel
open CategoryTheory CategoryTheory.Limits
variable {A B : AddCommGrp} (f : A ⟶ B)

def quotientIso : cokernel f ≅ AddCommGrp.of (B ⧸ LinearMap.range f.hom.toIntLinearMap) :=
  AddCommGrp.cokernelIsoQuotient f

def quotientIsoOfRange (S : Submodule ℤ B) (h : LinearMap.range f.hom.toIntLinearMap = S) :
    cokernel f ≅ AddCommGrp.of (B ⧸ S) :=
  quotientIso f ≪≫ (Submodule.quotEquivOfEq _ _ h).toAddEquiv.toAddCommGrpIso

#print axioms quotientIso
#print axioms quotientIsoOfRange
end Verification.ChowLinearCokernel
