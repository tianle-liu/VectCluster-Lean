/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathPresentation

/-!
# Path Recursion

Finite-index identities for deleting the first path vertex.
-/
namespace Verification.PathRecursion
open Verification.PathPresentation
variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

omit [CommRing R] in
theorem boundary_cons (a b c : R) (xx : Fin n → R) (i : Fin (n+2)) :
    boundary a b (Fin.cons c xx) i.succ = boundary c b xx i := by
  simp only [boundary, ← Fin.cons_snoc_eq_snoc_cons, Fin.cons_succ]

theorem equations_cons (a b c d : R) (xx yy : Fin n → R) :
    Equations a b (Fin.cons c xx) (Fin.cons d yy) ↔
      c*d = a + boundary c b xx 1 ∧ Equations c b xx yy := by
  constructor
  · intro h
    constructor
    · have hh := h 0
      simpa only [Fin.cons_zero, Fin.castSucc_zero, boundary_zero, Fin.succ_zero_eq_one,
        boundary_cons] using hh
    · intro i
      have hh := h i.succ
      simpa only [Fin.cons_succ, Fin.castSucc_fin_succ, boundary_cons] using hh
  · rintro ⟨h₀,h⟩ i
    induction i using Fin.cases with
    | zero =>
      simpa only [Fin.cons_zero, Fin.castSucc_zero, boundary_zero, Fin.succ_zero_eq_one,
        boundary_cons] using h₀
    | succ i =>
      simpa only [Fin.cons_succ, Fin.castSucc_fin_succ, boundary_cons] using h i

theorem equations_map (f : R →+* S) (a b : R) (xx yy : Fin n → R)
    (h : Equations a b xx yy) :
    Equations (f a) (f b) (fun i => f (xx i)) (fun i => f (yy i)) := by
  intro i
  have hh := congrArg f (h i)
  simpa only [map_mul, map_add, boundary_map f] using hh

theorem equations_tail (a b : R) (xx yy : Fin (n+1) → R)
    (h : Equations a b xx yy) :
    Equations (xx 0) b (Fin.tail xx) (Fin.tail yy) := by
  have hh := h
  rw [← Fin.cons_self_tail xx, ← Fin.cons_self_tail yy] at hh
  exact ((equations_cons _ _ _ _ _ _).mp hh).2

theorem equation_first (a b : R) (xx yy : Fin (n+1) → R)
    (h : Equations a b xx yy) :
    xx 0*yy 0 = a+boundary (xx 0) b (Fin.tail xx) 1 := by
  have hh := h
  rw [← Fin.cons_self_tail xx, ← Fin.cons_self_tail yy] at hh
  exact ((equations_cons _ _ _ _ _ _).mp hh).1

#print axioms boundary_cons
#print axioms equations_cons
#print axioms equations_map
#print axioms equations_tail
#print axioms equation_first
end Verification.PathRecursion
