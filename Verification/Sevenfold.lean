/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Std

/-!
# Sevenfold

Finite, kernel-checked certificates for the combinatorics in manuscript.tex,
the section "A seven-dimensional example" and its further examples.
Vertices 1,...,5 are represented by bits 0,...,4.
All finite claims below are proved with `decide`, not `native_decide`.

The integer cycle calculation uses the four edges of the independence square,
oriented cyclically as 1 -> 3 -> 2 -> 4 -> 1. It proves a complete description
of supported integral 1-cycles. The identification of this explicit complex
with geometric Chow--Witt groups, and the vector-bundle classification, are
NOT axiomatized or claimed to be formalized here.
-/

namespace Verification.Sevenfold

def contains (mask vertex : Nat) : Bool := (mask / 2 ^ vertex) % 2 == 1

def subset (a b : Nat) : Bool :=
  (List.range 5).all fun i => !contains a i || contains b i

def graphEdges : List (Nat × Nat) :=
  [(0, 1), (2, 3), (0, 4), (1, 4), (2, 4), (3, 4)]

def independent (mask : Nat) : Bool :=
  graphEdges.all fun e => !(contains mask e.1 && contains mask e.2)

def faces (ambient : Nat) : List Nat :=
  (List.range 32).filter fun mask => subset mask ambient && independent mask

theorem all_independent_faces :
    faces 31 = [0, 1, 2, 4, 5, 6, 8, 9, 10, 16] := by decide

theorem four_vertex_square_faces :
    faces 15 = [0, 1, 2, 4, 5, 6, 8, 9, 10] := by decide

def size (mask : Nat) : Nat := ((List.range 5).filter (contains mask)).length

theorem no_independent_triples :
    ∀ mask : Fin 32, independent mask.val = true → size mask.val ≤ 2 := by decide

theorem independence_number_two : independent 5 = true ∧ size 5 = 2 := by decide

/-- The coefficient cliques are {1,2,5} and {3,4}. -/
def color (vertex : Nat) : Nat := if vertex == 2 || vertex == 3 then 1 else 0

theorem colors_injective_on_independent_sets :
    ∀ mask : Fin 32, ∀ i j : Fin 5,
      independent mask.val = true →
      contains mask.val i.val = true → contains mask.val j.val = true →
      color i.val = color j.val → i = j := by decide

/-- Edge support in the cyclic order 1->3->2->4->1. -/
def edge13 (t : Nat) : Bool := contains t 0 && contains t 2
def edge32 (t : Nat) : Bool := contains t 2 && contains t 1
def edge24 (t : Nat) : Bool := contains t 1 && contains t 3
def edge41 (t : Nat) : Bool := contains t 3 && contains t 0

def hasWholeSquare (t : Nat) : Prop :=
  edge13 t = true ∧ edge32 t = true ∧ edge24 t = true ∧ edge41 t = true

instance (t : Nat) : Decidable (hasWholeSquare t) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem only_two_whole_squares :
    ∀ t : Fin 32, hasWholeSquare t.val ↔ t.val = 15 ∨ t.val = 31 := by decide

/-- Integral boundary zero at vertices 1,3,2,4; vertex 5 has no incident edge. -/
def boundaryZero (a b c d : Int) : Prop :=
  d - a = 0 ∧ a - b = 0 ∧ b - c = 0 ∧ c - d = 0

def supported (t : Nat) (a b c d : Int) : Prop :=
  (edge13 t = true ∨ a = 0) ∧ (edge32 t = true ∨ b = 0) ∧
  (edge24 t = true ∨ c = 0) ∧ (edge41 t = true ∨ d = 0)

def isCycle (t : Nat) (a b c d : Int) : Prop :=
  boundaryZero a b c d ∧ supported t a b c d

theorem integer_boundary_kernel (a b c d : Int) :
    boundaryZero a b c d ↔ a = b ∧ b = c ∧ c = d := by
  unfold boundaryZero
  omega

theorem equal_coefficients_support (t : Nat) (a : Int) :
    supported t a a a a ↔ hasWholeSquare t ∨ a = 0 := by
  unfold supported hasWholeSquare
  constructor
  · intro h
    by_cases ha : a = 0
    · exact Or.inr ha
    · exact Or.inl ⟨h.1.resolve_right ha, h.2.1.resolve_right ha,
        h.2.2.1.resolve_right ha, h.2.2.2.resolve_right ha⟩
  · intro h
    rcases h with h | h
    · exact ⟨Or.inl h.1, Or.inl h.2.1, Or.inl h.2.2.1, Or.inl h.2.2.2⟩
    · exact ⟨Or.inr h, Or.inr h, Or.inr h, Or.inr h⟩

/-- Every induced square cycle has one integer coefficient, and is zero
unless the ambient set is {1,2,3,4} or {1,2,3,4,5}. -/
theorem all_induced_integer_cycles (t : Fin 32) (a b c d : Int) :
    isCycle t.val a b c d ↔
      a = b ∧ b = c ∧ c = d ∧ ((t.val = 15 ∨ t.val = 31) ∨ a = 0) := by
  constructor
  · rintro ⟨hb, hs⟩
    have he := (integer_boundary_kernel a b c d).mp hb
    rcases he with ⟨hab, hbc, hcd⟩
    have hba : b = a := hab.symm
    have hca : c = a := hbc.symm.trans hba
    have hda : d = a := hcd.symm.trans hca
    have hs' : supported t.val a a a a := by simpa [hba, hca, hda] using hs
    have hw := (equal_coefficients_support t.val a).mp hs'
    exact ⟨hab, hbc, hcd, hw.imp ((only_two_whole_squares t).mp) id⟩
  · rintro ⟨hab, hbc, hcd, hw⟩
    have hba : b = a := hab.symm
    have hca : c = a := hbc.symm.trans hba
    have hda : d = a := hcd.symm.trans hca
    constructor
    · exact (integer_boundary_kernel a b c d).mpr ⟨hab, hbc, hcd⟩
    · have hs : supported t.val a a a a :=
        (equal_coefficients_support t.val a).mpr
          (hw.imp ((only_two_whole_squares t).mpr) id)
      simpa [hba, hca, hda] using hs

theorem full_square_cycles (t : Fin 32) (h : t.val = 15 ∨ t.val = 31)
    (a b c d : Int) :
    isCycle t.val a b c d ↔ a = b ∧ b = c ∧ c = d := by
  rw [all_induced_integer_cycles]
  constructor
  · intro hc
    exact ⟨hc.1, hc.2.1, hc.2.2.1⟩
  · rintro ⟨hab, hbc, hcd⟩
    exact ⟨hab, hbc, hcd, Or.inl h⟩

theorem other_induced_cycles_vanish (t : Fin 32)
    (h : ¬(t.val = 15 ∨ t.val = 31)) (a b c d : Int)
    (hc : isCycle t.val a b c d) : a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have he := (all_induced_integer_cycles t a b c d).mp hc
  have ha : a = 0 := he.2.2.2.resolve_left h
  omega

def weight (t : Nat) : Nat :=
  (if contains t 0 || contains t 1 || contains t 4 then 1 else 1 + 2 ^ 3) *
  (if contains t 2 || contains t 3 then 1 else 1 + 2 ^ 2)

theorem sevenfold_contribution_weights : weight 15 = 1 ∧ weight 31 = 1 := by decide
theorem sevenfold_total_multiplicity : weight 15 + weight 31 = 2 := by decide

/-- Removing either coefficient clique from either contributing set removes
the square, the combinatorial input for the claimed unit action. -/
theorem removing_coefficient_clique_kills_square :
    ¬hasWholeSquare 12 ∧ ¬hasWholeSquare 3 ∧ ¬hasWholeSquare 19 := by decide

def removeClique (t clique : Nat) : Nat :=
  ((List.range 5).filter fun i => contains t i && !contains clique i).foldl
    (fun mask i => mask + 2 ^ i) 0

theorem actual_clique_removals :
    removeClique 15 19 = 12 ∧ removeClique 31 19 = 12 ∧
    removeClique 15 12 = 3 ∧ removeClique 31 12 = 19 := by decide

end Verification.Sevenfold

namespace Verification.PathFive

open Verification.Sevenfold (contains subset size)

def graphEdges : List (Nat × Nat) := [(0, 1), (1, 2), (2, 3), (3, 4)]
def independent (mask : Nat) : Bool :=
  graphEdges.all fun e => !(contains mask e.1 && contains mask e.2)
def faces (t : Nat) : List Nat :=
  (List.range 32).filter fun i => subset i t && independent i

/-- Exactly six edges and the single triangle {1,3,5}. -/
theorem all_path_faces :
    faces 31 = [0, 1, 2, 4, 5, 8, 9, 10, 16, 17, 18, 20, 21] := by decide

theorem no_path_faces_above_dimension_two :
    ∀ mask : Fin 32, independent mask.val = true → size mask.val ≤ 3 := by decide

def edge (t i j : Nat) : Bool := contains t i && contains t j
def trianglePresent (t : Nat) : Prop := subset 21 t = true
def squarePresent (t : Nat) : Prop := subset 27 t = true

instance (t : Nat) : Decidable (trianglePresent t) :=
  inferInstanceAs (Decidable (subset 21 t = true))
instance (t : Nat) : Decidable (squarePresent t) :=
  inferInstanceAs (Decidable (subset 27 t = true))

theorem triangle_from_two_edges : ∀ t : Fin 32,
    edge t.val 0 2 = true → edge t.val 2 4 = true → trianglePresent t.val := by decide
theorem square_from_three_edges : ∀ t : Fin 32,
    edge t.val 0 3 = true → edge t.val 1 3 = true → edge t.val 1 4 = true →
      squarePresent t.val := by decide
theorem only_two_square_sets : ∀ t : Fin 32,
    squarePresent t.val ↔ t.val = 27 ∨ t.val = 31 := by decide

/-- Coordinates use sorted orientations 13,14,15,24,25,35. -/
structure Chain where
  a : Int
  b : Int
  c : Int
  d : Int
  e : Int
  f : Int
  deriving DecidableEq

def boundaryZero (v : Chain) : Prop :=
  -v.a - v.b - v.c = 0 ∧ -v.d - v.e = 0 ∧ v.a - v.f = 0 ∧
  v.b + v.d = 0 ∧ v.c + v.e + v.f = 0

def supported (t : Nat) (v : Chain) : Prop :=
  (edge t 0 2 = true ∨ v.a = 0) ∧ (edge t 0 3 = true ∨ v.b = 0) ∧
  (edge t 0 4 = true ∨ v.c = 0) ∧ (edge t 1 3 = true ∨ v.d = 0) ∧
  (edge t 1 4 = true ∨ v.e = 0) ∧ (edge t 2 4 = true ∨ v.f = 0)

def isCycle (t : Nat) (v : Chain) : Prop := boundaryZero v ∧ supported t v

theorem integer_kernel (v : Chain) : boundaryZero v ↔
    v.c = -v.a - v.b ∧ v.d = -v.b ∧ v.e = v.b ∧ v.f = v.a := by
  unfold boundaryZero
  omega

theorem supported_cycle_parameters (t : Fin 32) (v : Chain)
    (h : isCycle t.val v) :
    (trianglePresent t.val ∨ v.a = 0) ∧ (squarePresent t.val ∨ v.b = 0) := by
  have hk := (integer_kernel v).mp h.1
  constructor
  · by_cases ha : v.a = 0
    · exact Or.inr ha
    · apply Or.inl
      apply triangle_from_two_edges t
      · exact h.2.1.resolve_right ha
      · have hf : v.f ≠ 0 := by omega
        exact h.2.2.2.2.2.2.resolve_right hf
  · by_cases hb : v.b = 0
    · exact Or.inr hb
    · apply Or.inl
      apply square_from_three_edges t
      · exact h.2.2.1.resolve_right hb
      · have hd : v.d ≠ 0 := by omega
        exact h.2.2.2.2.1.resolve_right hd
      · have he : v.e ≠ 0 := by omega
        exact h.2.2.2.2.2.1.resolve_right he

/-- Boundary of k times the unique oriented 2-simplex [1,3,5]. -/
def triangleBoundary (k : Int) : Chain := ⟨k, 0, -k, 0, 0, k⟩

theorem triangle_boundary_injective (k l : Int) :
    triangleBoundary k = triangleBoundary l ↔ k = l := by
  constructor
  · intro h
    exact congrArg Chain.a h
  · intro h
    exact congrArg triangleBoundary h

/-- A representative for k times the square 1->4->2->5->1. -/
def squareCycle (k : Int) : Chain := ⟨0, k, -k, -k, k, 0⟩

def add (v w : Chain) : Chain :=
  ⟨v.a + w.a, v.b + w.b, v.c + w.c, v.d + w.d, v.e + w.e, v.f + w.f⟩

theorem cycle_decomposition (v : Chain) (h : boundaryZero v) :
    v = add (triangleBoundary v.a) (squareCycle v.b) := by
  have hk := (integer_kernel v).mp h
  cases v
  unfold add triangleBoundary squareCycle
  simp_all
  omega

/-- Explicit equality modulo supported integral 2-boundaries. -/
def sameHomology (t : Nat) (v w : Chain) : Prop :=
  ∃ k : Int, (trianglePresent t ∨ k = 0) ∧
    v.a - w.a = k ∧ v.b - w.b = 0 ∧ v.c - w.c = -k ∧
    v.d - w.d = 0 ∧ v.e - w.e = 0 ∧ v.f - w.f = k

/-- The square coefficient is a complete invariant modulo 2-boundaries. -/
theorem homology_parameter_complete (t : Fin 32) (v w : Chain)
    (hv : isCycle t.val v) (hw : isCycle t.val w) :
    sameHomology t.val v w ↔ v.b = w.b := by
  constructor
  · rintro ⟨k, _, _, hb, _⟩
    omega
  · intro hb
    have hkv := (integer_kernel v).mp hv.1
    have hkw := (integer_kernel w).mp hw.1
    have hpv := (supported_cycle_parameters t v hv).1
    have hpw := (supported_cycle_parameters t w hw).1
    refine ⟨v.a - w.a, ?_, ?_⟩
    · by_cases ht : trianglePresent t.val
      · exact Or.inl ht
      · have ha := hpv.resolve_left ht
        have ha' := hpw.resolve_left ht
        exact Or.inr (by omega)
    · omega

theorem no_homology_outside_two_sets (t : Fin 32)
    (ht : ¬(t.val = 27 ∨ t.val = 31)) (v : Chain) (hv : isCycle t.val v) :
    v.b = 0 := by
  have h := (supported_cycle_parameters t v hv).2
  exact h.resolve_left (fun hs => ht ((only_two_square_sets t).mp hs))

theorem square_representatives_supported : ∀ t : Fin 32,
    squarePresent t.val →
      edge t.val 0 3 = true ∧ edge t.val 0 4 = true ∧
      edge t.val 1 3 = true ∧ edge t.val 1 4 = true := by decide

theorem every_integer_represented (t : Fin 32) (ht : squarePresent t.val) (k : Int) :
    isCycle t.val (squareCycle k) := by
  have he := square_representatives_supported t ht
  constructor
  · simp only [boundaryZero, squareCycle]
    omega
  · unfold supported squareCycle
    exact ⟨Or.inr rfl, Or.inl he.1, Or.inl he.2.1, Or.inl he.2.2.1,
      Or.inl he.2.2.2, Or.inr rfl⟩

theorem principal_coefficient_multiplicity :
    3 ^ (5 - size 27) = 3 ∧ 3 ^ (5 - size 31) = 1 ∧
    3 ^ (5 - size 27) + 3 ^ (5 - size 31) = 4 := by decide

end Verification.PathFive

-- Trusted-kernel dependency audit for every theorem above.
#print axioms Verification.Sevenfold.all_independent_faces
#print axioms Verification.Sevenfold.four_vertex_square_faces
#print axioms Verification.Sevenfold.no_independent_triples
#print axioms Verification.Sevenfold.independence_number_two
#print axioms Verification.Sevenfold.colors_injective_on_independent_sets
#print axioms Verification.Sevenfold.only_two_whole_squares
#print axioms Verification.Sevenfold.integer_boundary_kernel
#print axioms Verification.Sevenfold.equal_coefficients_support
#print axioms Verification.Sevenfold.all_induced_integer_cycles
#print axioms Verification.Sevenfold.full_square_cycles
#print axioms Verification.Sevenfold.other_induced_cycles_vanish
#print axioms Verification.Sevenfold.sevenfold_contribution_weights
#print axioms Verification.Sevenfold.sevenfold_total_multiplicity
#print axioms Verification.Sevenfold.removing_coefficient_clique_kills_square
#print axioms Verification.Sevenfold.actual_clique_removals
#print axioms Verification.PathFive.all_path_faces
#print axioms Verification.PathFive.no_path_faces_above_dimension_two
#print axioms Verification.PathFive.triangle_from_two_edges
#print axioms Verification.PathFive.square_from_three_edges
#print axioms Verification.PathFive.only_two_square_sets
#print axioms Verification.PathFive.integer_kernel
#print axioms Verification.PathFive.supported_cycle_parameters
#print axioms Verification.PathFive.triangle_boundary_injective
#print axioms Verification.PathFive.cycle_decomposition
#print axioms Verification.PathFive.homology_parameter_complete
#print axioms Verification.PathFive.no_homology_outside_two_sets
#print axioms Verification.PathFive.square_representatives_supported
#print axioms Verification.PathFive.every_integer_represented
#print axioms Verification.PathFive.principal_coefficient_multiplicity

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.PathFive.Chain
#print axioms Verification.PathFive.add
#print axioms Verification.PathFive.boundaryZero
#print axioms Verification.PathFive.edge
#print axioms Verification.PathFive.faces
#print axioms Verification.PathFive.graphEdges
#print axioms Verification.PathFive.independent
#print axioms Verification.PathFive.isCycle
#print axioms Verification.PathFive.sameHomology
#print axioms Verification.PathFive.squareCycle
#print axioms Verification.PathFive.squarePresent
#print axioms Verification.PathFive.supported
#print axioms Verification.PathFive.triangleBoundary
#print axioms Verification.PathFive.trianglePresent
#print axioms Verification.Sevenfold.boundaryZero
#print axioms Verification.Sevenfold.color
#print axioms Verification.Sevenfold.contains
#print axioms Verification.Sevenfold.edge13
#print axioms Verification.Sevenfold.edge24
#print axioms Verification.Sevenfold.edge32
#print axioms Verification.Sevenfold.edge41
#print axioms Verification.Sevenfold.faces
#print axioms Verification.Sevenfold.graphEdges
#print axioms Verification.Sevenfold.hasWholeSquare
#print axioms Verification.Sevenfold.independent
#print axioms Verification.Sevenfold.isCycle
#print axioms Verification.Sevenfold.removeClique
#print axioms Verification.Sevenfold.size
#print axioms Verification.Sevenfold.subset
#print axioms Verification.Sevenfold.supported
#print axioms Verification.Sevenfold.weight
