/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SingleModifiedPath
import Verification.BranchedPathMatrix

/-!
# Dynkin Matrix Normal Form

Literal signed exchange matrices for the irreducible finite Dynkin
list. The index of A starts at rank one, B/C at rank two, and D at rank four.
These are matrix definitions, with no vanishing or deletion property.
-/
noncomputable section
namespace Verification.DynkinMatrixNormalForm
open Classical

inductive Kind where
  | A (r : ℕ)
  | B (r : ℕ)
  | C (r : ℕ)
  | D (r : ℕ)
  | E6 | E7 | E8 | F4 | G2
  deriving DecidableEq

def dArms (r : ℕ) (i : Fin 3) : ℕ := if i.val=0 then 1 else if i.val=1 then 1 else r+1

def eArms (r : ℕ) (i : Fin 3) : ℕ := if i.val=0 then 1 else if i.val=1 then 2 else r+2

def Vertices : Kind→Type
  | .A r=>Fin (r+1)
  | .B r=>Fin (r+2)
  | .C r=>Fin (r+2)
  | .D r=>BranchedPathMatrix.Vertices (dArms r)
  | .E6=>BranchedPathMatrix.Vertices (eArms 0)
  | .E7=>BranchedPathMatrix.Vertices (eArms 1)
  | .E8=>BranchedPathMatrix.Vertices (eArms 2)
  | .F4=>Fin 4
  | .G2=>Fin 2

instance verticesFintype (t : Kind) : Fintype (Vertices t) := by cases t <;> dsimp [Vertices] <;> infer_instance

def matrix (a : ℕ→ℤˣ) (b : Fin 3→ℕ→ℤˣ) (u : Fin 3→ℤˣ) :
    (t : Kind)→Matrix (Vertices t) (Vertices t) ℤ
  | .A r=>PathOrientationSigns.matrix a (r+1)
  | .B r=>SingleModifiedPath.matrix (r+2) a ⟨0,by omega⟩ (2*(a 0:ℤ)) (-(a 0:ℤ))
  | .C r=>SingleModifiedPath.matrix (r+2) a ⟨0,by omega⟩ (a 0:ℤ) (-2*(a 0:ℤ))
  | .D r=>BranchedPathMatrix.matrix (dArms r) b (fun i=>(u i:ℤ)) (fun i=>-(u i:ℤ))
  | .E6=>BranchedPathMatrix.matrix (eArms 0) b (fun i=>(u i:ℤ)) (fun i=>-(u i:ℤ))
  | .E7=>BranchedPathMatrix.matrix (eArms 1) b (fun i=>(u i:ℤ)) (fun i=>-(u i:ℤ))
  | .E8=>BranchedPathMatrix.matrix (eArms 2) b (fun i=>(u i:ℤ)) (fun i=>-(u i:ℤ))
  | .F4=>SingleModifiedPath.matrix 4 a ⟨1,by omega⟩ (2*(a 1:ℤ)) (-(a 1:ℤ))
  | .G2=>SingleModifiedPath.matrix 2 a ⟨0,by omega⟩ (3*(a 0:ℤ)) (-(a 0:ℤ))

structure NormalForm (n : ℕ) (B : Matrix (Fin n) (Fin n) ℤ) where
  kind : Kind
  pathSigns : ℕ→ℤˣ
  armSigns : Fin 3→ℕ→ℤˣ
  centralSigns : Fin 3→ℤˣ
  indexing : Vertices kind≃Fin n
  entries : ∀i j,B (indexing i) (indexing j)=matrix pathSigns armSigns centralSigns kind i j

#print axioms Kind
#print axioms dArms
#print axioms eArms
#print axioms Vertices
#print axioms verticesFintype
#print axioms matrix
#print axioms NormalForm
end Verification.DynkinMatrixNormalForm
