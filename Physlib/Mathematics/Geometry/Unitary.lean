/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolai Kashcheev
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Unitary complex numbers and the circle

This file relates `unitary ℂ` to the existing `Circle` API in Mathlib. This lets later files use
the manifold and Lie group structure already available for `Circle` when working with the `U(1)`
factor written as unitary complex numbers.

## Main definitions

- `Circle.toUnitary`: the map from `Circle` to `unitary ℂ`.
- `Unitary.toCircle`: the map from `unitary ℂ` to `Circle`.
- `Circle.unitaryMulEquiv`: the multiplicative equivalence between `Circle` and `unitary ℂ`.
- `Circle.unitaryHomeomorph`: the homeomorphism between `Circle` and `unitary ℂ`.
- `Circle.unitaryContinuousMulEquiv`: the continuous multiplicative equivalence between `Circle`
  and `unitary ℂ`.
- `Unitary.instChartedSpaceComplex`: the charted space structure on `unitary ℂ` transported from
  `Circle`.
- `Unitary.instIsManifoldComplex`: the analytic manifold structure on `unitary ℂ` transported from
  `Circle`.
- `Circle.contMDiff_toUnitary`: `Circle.toUnitary` is analytic.
- `Unitary.contMDiff_toCircle`: `Unitary.toCircle` is analytic.
- `Unitary.instLieGroupComplex`: the analytic Lie group structure on `unitary ℂ` transported from
  `Circle`.
-/

@[expose] public section

noncomputable section

namespace Circle

open Complex

/-- The inclusion of `Circle` into the unitary complex numbers. -/
def toUnitary : Circle →* unitary ℂ where
  toFun z := ⟨z, by
    rw [Unitary.mem_iff]
    constructor <;> simp [Complex.conj_mul', Complex.mul_conj']⟩
  map_one' := by
    ext
    simp
  map_mul' z w := by
    ext
    simp

@[simp]
lemma coe_toUnitary (z : Circle) : (toUnitary z : ℂ) = z := rfl

/-- The map from `Circle` to unitary complex numbers is continuous. -/
lemma continuous_toUnitary : Continuous toUnitary :=
  Continuous.subtype_mk continuous_subtype_val fun z => by
    rw [Unitary.mem_iff]
    constructor <;> simp [Complex.conj_mul', Complex.mul_conj']

end Circle

namespace Unitary

/-- The map from unitary complex numbers to `Circle`. -/
def toCircle : unitary ℂ →* Circle where
  toFun u := ⟨u, mem_sphere_zero_iff_norm.2 (CStarRing.norm_coe_unitary u)⟩
  map_one' := by
    ext
    simp
  map_mul' u v := by
    ext
    simp

@[simp]
lemma coe_toCircle (u : unitary ℂ) : (toCircle u : ℂ) = u := rfl

/-- The map from unitary complex numbers to `Circle` is continuous. -/
lemma continuous_toCircle : Continuous toCircle :=
  Continuous.subtype_mk continuous_subtype_val fun u =>
    mem_sphere_zero_iff_norm.2 (CStarRing.norm_coe_unitary u)

@[simp]
lemma toCircle_toUnitary (z : Circle) : toCircle (Circle.toUnitary z) = z := by
  ext
  rfl

end Unitary

namespace Circle

@[simp]
lemma toUnitary_toCircle (u : unitary ℂ) : toUnitary (Unitary.toCircle u) = u := by
  ext
  rfl

/-- The multiplicative equivalence between `Circle` and unitary complex numbers. -/
def unitaryMulEquiv : Circle ≃* unitary ℂ where
  toFun := toUnitary
  invFun := Unitary.toCircle
  left_inv := Unitary.toCircle_toUnitary
  right_inv := toUnitary_toCircle
  map_mul' z w := map_mul toUnitary z w

@[simp]
lemma unitaryMulEquiv_apply (z : Circle) : unitaryMulEquiv z = toUnitary z := rfl

@[simp]
lemma unitaryMulEquiv_symm_apply (u : unitary ℂ) :
    unitaryMulEquiv.symm u = Unitary.toCircle u := rfl

/-- The homeomorphism between `Circle` and unitary complex numbers. -/
def unitaryHomeomorph : Circle ≃ₜ unitary ℂ where
  toEquiv := unitaryMulEquiv.toEquiv
  continuous_toFun := continuous_toUnitary
  continuous_invFun := Unitary.continuous_toCircle

@[simp]
lemma unitaryHomeomorph_apply (z : Circle) : unitaryHomeomorph z = toUnitary z := rfl

@[simp]
lemma unitaryHomeomorph_symm_apply (u : unitary ℂ) :
    unitaryHomeomorph.symm u = Unitary.toCircle u := rfl

/-- The continuous multiplicative equivalence between `Circle` and unitary complex numbers. -/
def unitaryContinuousMulEquiv : Circle ≃ₜ* unitary ℂ :=
  ContinuousMulEquiv.mk unitaryMulEquiv continuous_toUnitary Unitary.continuous_toCircle

@[simp]
lemma unitaryContinuousMulEquiv_apply (z : Circle) :
    unitaryContinuousMulEquiv z = toUnitary z := rfl

@[simp]
lemma unitaryContinuousMulEquiv_symm_apply (u : unitary ℂ) :
    unitaryContinuousMulEquiv.symm u = Unitary.toCircle u := rfl

end Circle

namespace Unitary

open scoped Manifold ContDiff

/-- The charted space structure on unitary complex numbers transported from `Circle`. -/
noncomputable instance instChartedSpaceComplex :
    ChartedSpace (EuclideanSpace ℝ (Fin 1)) (unitary ℂ) where
  atlas := fun c => ∃ e, Set.Mem (atlas (EuclideanSpace ℝ (Fin 1)) Circle) e ∧
    c = Circle.unitaryHomeomorph.symm.toOpenPartialHomeomorph.trans e
  chartAt u := Circle.unitaryHomeomorph.symm.toOpenPartialHomeomorph.trans
    (chartAt (EuclideanSpace ℝ (Fin 1)) (Circle.unitaryHomeomorph.symm u))
  mem_chart_source u := by
    simp
  chart_mem_atlas u := by
    refine ⟨chartAt (EuclideanSpace ℝ (Fin 1)) (Circle.unitaryHomeomorph.symm u), ?_⟩
    exact ⟨chart_mem_atlas _ _, rfl⟩

@[simp]
lemma chartedSpaceComplex_chartAt (u : unitary ℂ) :
    chartAt (EuclideanSpace ℝ (Fin 1)) u =
      Circle.unitaryHomeomorph.symm.toOpenPartialHomeomorph.trans
        (chartAt (EuclideanSpace ℝ (Fin 1)) (Circle.unitaryHomeomorph.symm u)) := rfl

/-- The analytic manifold structure on unitary complex numbers transported from `Circle`. -/
noncomputable instance instIsManifoldComplex : IsManifold (𝓡 1) ω (unitary ℂ) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  rcases he with ⟨c, hc, hce⟩
  rcases he' with ⟨c', hc', hce'⟩
  rw [hce, hce']
  have hmem := (contDiffGroupoid ω (𝓡 1)).compatible hc hc'
  refine hmem.1.congr_mono ?_ ?_
  · intro x hx
    simp [Homeomorph.symm_toOpenPartialHomeomorph, Function.comp_def]
  · intro x hx
    simpa [Homeomorph.symm_toOpenPartialHomeomorph, Function.comp_def] using hx

end Unitary

namespace Circle

open scoped Manifold ContDiff

/-- The map from `Circle` to unitary complex numbers is analytic. -/
lemma contMDiff_toUnitary : ContMDiff (𝓡 1) (𝓡 1) ω toUnitary := by
  rw [contMDiff_iff]
  constructor
  · exact continuous_toUnitary
  · intro x y
    have hmem := (contDiffGroupoid ω (𝓡 1)).compatible
      (chart_mem_atlas (EuclideanSpace ℝ (Fin 1)) x)
      (chart_mem_atlas (EuclideanSpace ℝ (Fin 1)) (Circle.unitaryHomeomorph.symm y))
    refine hmem.1.congr_mono ?_ ?_
    · intro z hz
      simp [extChartAt, Unitary.chartedSpaceComplex_chartAt,
        Homeomorph.symm_toOpenPartialHomeomorph, Function.comp_def]
    · intro z hz
      simpa [extChartAt, Unitary.chartedSpaceComplex_chartAt,
        Homeomorph.symm_toOpenPartialHomeomorph, Function.comp_def] using hz

end Circle

namespace Unitary

open scoped Manifold ContDiff

/-- The map from unitary complex numbers to `Circle` is analytic. -/
lemma contMDiff_toCircle : ContMDiff (𝓡 1) (𝓡 1) ω toCircle := by
  rw [contMDiff_iff]
  constructor
  · exact continuous_toCircle
  · intro x y
    have hmem := (contDiffGroupoid ω (𝓡 1)).compatible
      (chart_mem_atlas (EuclideanSpace ℝ (Fin 1)) (Circle.unitaryHomeomorph.symm x))
      (chart_mem_atlas (EuclideanSpace ℝ (Fin 1)) y)
    refine hmem.1.congr_mono ?_ ?_
    · intro z hz
      simp [extChartAt, chartedSpaceComplex_chartAt, Homeomorph.symm_toOpenPartialHomeomorph,
        Function.comp_def]
    · intro z hz
      simpa [extChartAt, chartedSpaceComplex_chartAt, Homeomorph.symm_toOpenPartialHomeomorph,
        Function.comp_def] using hz

/-- The analytic Lie group structure on unitary complex numbers transported from `Circle`. -/
noncomputable instance instLieGroupComplex : LieGroup (𝓡 1) ω (unitary ℂ) where
  compatible := (inferInstance : IsManifold (𝓡 1) ω (unitary ℂ)).compatible
  contMDiff_mul := by
    let model := 𝓡 1
    have h_toCircle : ContMDiff (model.prod model) (model.prod model) ω
        (Prod.map toCircle toCircle) :=
      ContMDiff.prodMap contMDiff_toCircle contMDiff_toCircle
    have h_mul : ContMDiff (model.prod model) model ω
        (fun p : Prod Circle Circle => p.1 * p.2) :=
      _root_.contMDiff_mul (G := Circle) model ω
    have h_toUnitary : ContMDiff (model.prod model) model ω
        (fun p : Prod (unitary ℂ) (unitary ℂ) =>
          Circle.toUnitary (toCircle p.1 * toCircle p.2)) :=
      Circle.contMDiff_toUnitary.comp (h_mul.comp h_toCircle)
    refine h_toUnitary.congr ?_
    intro p
    simp
  contMDiff_inv := by
    let model := 𝓡 1
    have h_inv : ContMDiff model model ω (fun z : Circle => z⁻¹) :=
      _root_.contMDiff_inv (G := Circle) model ω
    have h_toUnitary : ContMDiff model model ω
        (fun u : unitary ℂ => Circle.toUnitary ((toCircle u)⁻¹)) :=
      Circle.contMDiff_toUnitary.comp (h_inv.comp contMDiff_toCircle)
    refine h_toUnitary.congr ?_
    intro u
    simp

end Unitary
