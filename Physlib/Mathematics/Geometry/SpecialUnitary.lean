/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolai Kashcheev
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Instances.Matrix

/-!
# Topological structure on special unitary groups

This file supplies the topological group instance for `Matrix.specialUnitaryGroup`.
It uses the inclusion `SU(n) → U(n)` and the existing topological group structure on
`Matrix.unitaryGroup`, rather than proving the topological group laws directly.

## Main definitions

- `Matrix.SpecialUnitaryGroup.toUnitaryGroup`: the inclusion `SU(n) → U(n)`.
- `Matrix.SpecialUnitaryGroup.toUnitaryGroup_isInducing`: the inclusion induces the subtype
  topology on `SU(n)`.
- `Matrix.SpecialUnitaryGroup.instIsTopologicalGroup`: the topological group structure on `SU(n)`.
-/

@[expose] public section

open Topology

namespace Matrix
namespace SpecialUnitaryGroup

variable {n α : Type*} [Fintype n] [DecidableEq n] [CommRing α] [StarRing α]

/-- The inclusion of the special unitary group into the unitary group. -/
def toUnitaryGroup : specialUnitaryGroup n α →* unitaryGroup n α where
  toFun U := ⟨U.1, U.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
lemma coe_toUnitaryGroup (U : specialUnitaryGroup n α) :
    ((toUnitaryGroup U : unitaryGroup n α) : Matrix n n α) = U :=
  rfl

/-- The inclusion of `SU(n)` into `U(n)` is injective. -/
lemma toUnitaryGroup_injective :
    Function.Injective (toUnitaryGroup : specialUnitaryGroup n α → unitaryGroup n α) := by
  intro U V h
  exact Subtype.ext (congr_arg (fun W : unitaryGroup n α => (W : Matrix n n α)) h)

variable [TopologicalSpace α]

/-- The inclusion of `SU(n)` into `U(n)` induces the subtype topology on `SU(n)`. -/
lemma toUnitaryGroup_isInducing :
    IsInducing (toUnitaryGroup : specialUnitaryGroup n α → unitaryGroup n α) := by
  change IsInducing (Set.codRestrict
    (fun U : specialUnitaryGroup n α => (U : Matrix n n α))
    (unitaryGroup n α : Set (Matrix n n α)) (fun U => U.2.1))
  exact Topology.IsInducing.subtypeVal.codRestrict
    (fun U : specialUnitaryGroup n α => U.2.1)

variable [ContinuousStar α] [ContinuousAdd α] [ContinuousMul α]

/-- The special unitary group is a topological group. -/
instance instIsTopologicalGroup : IsTopologicalGroup (specialUnitaryGroup n α) :=
  IsInducing.topologicalGroup toUnitaryGroup toUnitaryGroup_isInducing

end SpecialUnitaryGroup
end Matrix
