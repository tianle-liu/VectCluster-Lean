/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathConeCoefficients

/-!
# Path Cone Matrix Data

Bundling the finite cone computation before specializing actual endpoint
image modules avoids expanding their proof-dependent module structures.
-/

namespace Verification.PathConeMatrixData

open Verification.PathEndpointCoordinates Verification.PathSplitConeData Verification.PathConeCoefficients

variable {R M C O : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup C] [Module R C] [AddCommGroup O] [Module R O]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

structure MatrixData (D : M →ₗ[R] M) (A : Matrix ι ι R) (B : Matrix κ κ R) where
  coordinates : M ≃ₗ[R] (ι ⊕ κ → R)
  connecting : Matrix ι κ R
  block_equality : matrixOf coordinates D=Matrix.fromBlocks A connecting 0 B
  squared : matrixOf coordinates D*matrixOf coordinates D=0

noncomputable def ofConeData (D : M →ₗ[R] M) (DC : C →ₗ[R] C) (DO : O →ₗ[R] O)
    (K : ConeData D DC DO) (E : C ≃ₗ[R] (ι → R)) (F : O ≃ₗ[R] (κ → R)) (hD : D.comp D=0) :
    MatrixData D (matrixOf E DC) (matrixOf F DO) where
  coordinates := K.coordinates.trans (pairCoordinates E F)
  connecting := rectangularMatrix E F K.connecting
  block_equality := (matrixOf_equivalence K.coordinates (pairCoordinates E F) D
    (block DC DO K.connecting) K.conjugacy).trans (block_matrix E F DC DO K.connecting)
  squared := matrixOf_squared _ D hD

#print axioms MatrixData
#print axioms ofConeData

end Verification.PathConeMatrixData
