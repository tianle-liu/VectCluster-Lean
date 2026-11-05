/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ModuleGrothendieck

/-!
# Coherent Unit

The actual free rank-one coherent class, with its finite-module
instance resolved uniformly before specializing to a large coordinate ring.
-/
namespace Verification.CoherentUnit
noncomputable def classOf (A : Type*) [CommRing A] : ModuleGrothendieck.Group A :=
  ModuleGrothendieck.classOf A (ModuleGrothendieck.of A A)
#print axioms classOf
end Verification.CoherentUnit
