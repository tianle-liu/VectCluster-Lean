/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRecursion

/-!
# Path Open Insertion

Inserting or removing the first partner when the first original
coordinate is a unit, with all endpoint coefficients retained.
-/
namespace Verification.PathOpenInsertion
open Verification.PathPresentation Verification.PathRecursion
variable {R : Type*} [CommRing R] {n : ℕ}

def insertX (u : Rˣ) (xx : Fin n → R) : Fin (n+1) → R := Fin.cons (u:R) xx

def insertY (a b : R) (u : Rˣ) (xx yy : Fin n → R) : Fin (n+1) → R :=
  Fin.cons ((u⁻¹:Rˣ)*(a+boundary (u:R) b xx 1)) yy

theorem inserted_equations (a b : R) (u : Rˣ) (xx yy : Fin n → R)
    (h : Equations (u:R) b xx yy) :
    Equations a b (insertX u xx) (insertY a b u xx yy) := by
  rw [insertX, insertY, equations_cons]
  constructor
  · rw [← mul_assoc, Units.mul_inv, one_mul]
  · exact h

theorem removed_partner (a b : R) (u : Rˣ) (xx yy : Fin (n+1) → R)
    (h : Equations a b xx yy) (hu : xx 0 = (u:R)) :
    yy 0 = (u⁻¹:Rˣ)*(a+boundary (u:R) b (Fin.tail xx) 1) := by
  have hh := equation_first a b xx yy h
  rw [hu] at hh
  calc
    yy 0 = ((u⁻¹:Rˣ):R)*((u:R)*yy 0) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [hh]

#print axioms insertX
#print axioms insertY
#print axioms inserted_equations
#print axioms removed_partner
end Verification.PathOpenInsertion
