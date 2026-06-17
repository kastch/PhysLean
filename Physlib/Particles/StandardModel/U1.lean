/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolai Kashcheev
-/
module

public import Physlib.Mathematics.Geometry.Unitary
public import Physlib.Particles.StandardModel.Basic

/-!
# The `U(1)` factor of the Standard Model gauge group

This file exposes the `U(1)` factor of `GaugeGroupI` as `Circle`, so later manifold and Lie group
constructions can use the existing `Circle` API from Mathlib.
-/

@[expose] public section

noncomputable section

namespace StandardModel

namespace GaugeGroupI

/-- The underlying `U(1)` factor of an element in `GaugeGroupI`, viewed as `Circle`. -/
def toU1Circle : GaugeGroupI →* Circle :=
  Unitary.toCircle.comp toU1

@[simp]
lemma toU1Circle_apply (g : GaugeGroupI) :
    toU1Circle g = Unitary.toCircle (toU1 g) := rfl

@[simp]
lemma coe_toU1Circle (g : GaugeGroupI) : (toU1Circle g : ℂ) = toU1 g := rfl

lemma toUnitary_toU1Circle (g : GaugeGroupI) : Circle.toUnitary (toU1Circle g) = toU1 g := by
  simp [toU1Circle]

@[simp]
lemma ofU1Subgroup_toU1Circle (u1 : unitary ℂ) :
    toU1Circle (ofU1Subgroup u1) = Unitary.toCircle u1 := rfl

end GaugeGroupI

end StandardModel
