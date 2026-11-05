/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathSplitRecursion

/-!
# Path Split Cone Data

Package the actual split-cone equality before specializing large path modules.
-/

namespace Verification.PathSplitConeData

variable {R C M O : Type*} [CommRing R]
variable [AddCommGroup C] [Module R C] [AddCommGroup M] [Module R M]
variable [AddCommGroup O] [Module R O]

def block (DC : C →ₗ[R] C) (DO : O →ₗ[R] O) (F : O →ₗ[R] C) :
    (C × O) →ₗ[R] (C × O) :=
  ((DC.comp (LinearMap.fst R C O))+F.comp (LinearMap.snd R C O)).prod
    (DO.comp (LinearMap.snd R C O))

structure ConeData (D : M →ₗ[R] M) (DC : C →ₗ[R] C) (DO : O →ₗ[R] O) where
  coordinates : M ≃ₗ[R] C × O
  connecting : O →ₗ[R] C
  conjugacy : coordinates.toLinearMap.comp D=(block DC DO connecting).comp coordinates.toLinearMap

noncomputable def ofSplit (E : C →ₗ[R] M) (Q : M →ₗ[R] O) (S : O →ₗ[R] M)
    (hE : Function.Injective E) (hEQ : LinearMap.range E=LinearMap.ker Q)
    (hQS : Q.comp S=LinearMap.id) (D : M →ₗ[R] M) (DC : C →ₗ[R] C) (DO : O →ₗ[R] O)
    (hDE : D.comp E=E.comp DC) (hQD : Q.comp D=DO.comp Q) : ConeData D DC DO where
  coordinates := Verification.PathSplitRecursion.coordinates E Q S hE hEQ hQS
  connecting := Verification.PathSplitRecursion.connecting E Q S hE hEQ hQS D
  conjugacy := Verification.PathSplitRecursion.coordinates_differential E Q S hE hEQ hQS D DC DO hDE hQD

#print axioms block
#print axioms ConeData
#print axioms ofSplit

end Verification.PathSplitConeData
