/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ModuleGrothendieck
import Verification.GlobalExchangeSmooth

/-!
# Smooth Cartan Input

The ordinary Cartan comparison for a smooth affine algebra over a
field. Both sides and the forgetful map are actual module Grothendieck
groups defined by their universal presentations. No rank or cluster
conclusion is included in this uniform reference theorem.
-/
namespace Verification.SmoothCartanInput

structure Standard where
  bijective : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A], Function.Bijective (ModuleGrothendieck.cartan A)

#print axioms Standard
end Verification.SmoothCartanInput
