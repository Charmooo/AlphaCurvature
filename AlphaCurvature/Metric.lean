/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import AlphaCurvature.Curvature.Hessian
import AlphaCurvature.Curvature.Pullback

/-!
# The α-geometry of the simplex and its scalar curvature

The α-geometry of the open probability simplex, and its scalar curvature in closed form.

The α-geometry is the pullback of the Euclidean metric by the Amari embedding
`A_p(ρ) = p ρ^(1/p)`, coordinatewise, with `p = 2/(1 - α)`, and `A_∞(ρ) = log ρ` at `α = 1`.
Its metric is `g = ∑ᵢ ρᵢ^(-1-α) dρᵢ²` (`alphaForm`, `pullback_amariEmbed`). In the affine chart
`z ↦ x + z` of the simplex `x + {∑ zᵢ = 0}` (`alphaChart`, `simplexTangent`) it is a Hessian
metric: its derivative `-(1 + α) ∑ᵢ xᵢ^(-2-α) dxᵢ³` is totally symmetric. So
`S = ¼ (|T|² - |τ|²)` in an orthonormal basis (`scalarCurvature_of_fderiv_comm_of_orthonormal`),
and both contractions only involve the completeness kernel `∑ₐ eₐ(i) eₐ(j)`.

## Main definitions

* `AlphaCurvature.simplexTangent d`: the vectors of `d → ℝ` with coordinate sum `0`.
* `AlphaCurvature.alphaForm α x`: the bilinear form `∑ᵢ xᵢ^(-1-α) uᵢ vᵢ`.
* `AlphaCurvature.amariEmbed α`: the Amari embedding, coordinatewise
  `t ↦ (2/(1 - α)) t^((1-α)/2)`, and `log` at `α = 1`.
* `AlphaCurvature.alphaChart α V x₀`: `alphaForm α` in the chart `z ↦ x₀ + z` of `x₀ + V`.
* `AlphaCurvature.alphaKernel α x`: `Kᵢⱼ = wᵢ δᵢⱼ - wᵢ wⱼ / W`, with `w = x^(1+α)` and
  `W = ∑ₖ wₖ`.

## Main statements

* `AlphaCurvature.pullback_amariEmbed`: `alphaForm α` is the Amari pullback of the Euclidean
  metric, for every `α`, so it is the metric of Gibilisco–Isola's α-geometry.
* `AlphaCurvature.sum_mul_eq_alphaKernel`: **the completeness kernel**. For every
  `G_x`-orthonormal basis `e` of `simplexTangent d`, `∑ₐ eₐ(i) eₐ(j) = Kᵢⱼ`.
* `AlphaCurvature.scalarCurvature_alphaChart`: **the closed form**, in power sums
  `P(s) = ∑ᵢ xᵢˢ`,
  `S = (1 + α)²/4 · ((P(α)² - P(2α)) P(1+α) - 2 P(α) P(1+2α) + 2 P(1+3α)) / P(1+α)²`.
* `AlphaCurvature.scalarCurvature_alphaChart_zero`: at `α = 0`, the Fisher metric,
  `S = (n - 1)(n - 2)/4` on probability vectors. This is the sphere of radius `2`, which fixes
  the sign and normalization against Gibilisco–Isola.

## Implementation notes

The kernel is found without a basis. The column `k = K·ⱼ` lies in `simplexTangent d` and satisfies
`G_x(v, k) = vⱼ` for every `v` there (`alphaForm_alphaKernel`), so expanding `k` in an orthonormal
basis gives `kᵢ = ∑ₐ G_x(eₐ, k) eₐ(i) = ∑ₐ eₐ(j) eₐ(i)`.

The statements hold at every positive `x`, normalized or not, and for every real `α`. At
`α = -1` (`p = 1`) the metric is flat.

## References

* [P. Gibilisco, T. Isola, *On the monotonicity of scalar curvature in classical and quantum
  information geometry*][gibilisco2004], J. Math. Phys. 46 (2005), arXiv math-ph/0407007.
* [P. Gibilisco, *Lp unit spheres and the α-geometries: questions and perspectives*][gibilisco2020],
  Entropy 22 (2020) 1409.
* [S. Amari, H. Nagaoka, *Methods of Information Geometry*][amari2000]
-/

open scoped Topology
open ContinuousLinearMap Filter Set
open AlphaCurvature.Curvature

namespace AlphaCurvature

variable {d : Type*} [Fintype d]

/-! ### The metric -/

/-- The tangent space of the probability simplex: the vectors with coordinate sum `0`. -/
def simplexTangent (d : Type*) [Fintype d] : Submodule ℝ (d → ℝ) where
  carrier := {v | ∑ i, v i = 0}
  add_mem' {u v} hu hv := by
    change ∑ i, (u i + v i) = 0
    rw [Finset.sum_add_distrib, show ∑ i, u i = 0 from hu, show ∑ i, v i = 0 from hv, add_zero]
  zero_mem' := by simp
  smul_mem' c v hv := by
    change ∑ i, c * v i = 0
    rw [← Finset.mul_sum, show ∑ i, v i = 0 from hv, mul_zero]

theorem mem_simplexTangent {v : d → ℝ} : v ∈ simplexTangent d ↔ ∑ i, v i = 0 :=
  Iff.rfl

/-- The coordinate square `(u, v) ↦ uᵢ vᵢ`. -/
noncomputable def coordForm (i : d) : (d → ℝ) →L[ℝ] (d → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.proj i)
    (ContinuousLinearMap.proj i)

@[simp]
theorem coordForm_apply (i : d) (u v : d → ℝ) : coordForm i u v = u i * v i :=
  rfl

/-- **The α-metric** `∑ᵢ xᵢ^(-1-α) dxᵢ²` on the positive orthant. On the simplex it is the
metric of the α-geometry (`pullback_amariEmbed`); at `α = 0` it is the Fisher metric. -/
noncomputable def alphaForm (α : ℝ) (x : d → ℝ) : (d → ℝ) →L[ℝ] (d → ℝ) →L[ℝ] ℝ :=
  ∑ i, x i ^ (-1 - α) • coordForm i

variable {α : ℝ} {x : d → ℝ}

theorem alphaForm_apply (α : ℝ) (x u v : d → ℝ) :
    alphaForm α x u v = ∑ i, x i ^ (-1 - α) * (u i * v i) := by
  simp [alphaForm]

theorem alphaForm_comm (α : ℝ) (x u v : d → ℝ) : alphaForm α x u v = alphaForm α x v u := by
  simp only [alphaForm_apply, mul_comm (u _)]

/-- The derivative of the α-metric, `DG_x(z)(u, v) = -(1 + α) ∑ᵢ xᵢ^(-2-α) zᵢ uᵢ vᵢ`. -/
theorem hasFDerivAt_alphaForm (hx : ∀ i, x i ≠ 0) :
    HasFDerivAt (alphaForm α)
      (∑ i, (((-1 - α) * x i ^ (-1 - α - 1)) •
        (ContinuousLinearMap.proj i : (d → ℝ) →L[ℝ] ℝ)).smulRight
        (coordForm i)) x := by
  unfold alphaForm
  refine HasFDerivAt.fun_sum fun i _ ↦ ?_
  exact ((Real.hasDerivAt_rpow_const (Or.inl (hx i))).comp_hasFDerivAt x
    (ContinuousLinearMap.proj i : (d → ℝ) →L[ℝ] ℝ).hasFDerivAt).smul_const (coordForm i)

theorem fderiv_alphaForm_apply (hx : ∀ i, x i ≠ 0) (z u v : d → ℝ) :
    fderiv ℝ (alphaForm α) x z u v = -(1 + α) * ∑ i, x i ^ (-2 - α) * (z i * u i * v i) := by
  rw [(hasFDerivAt_alphaForm hx).fderiv, Finset.mul_sum]
  simp only [sum_apply, smulRight_apply, smul_apply, proj_apply, smul_eq_mul, coordForm_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show -1 - α - 1 = -2 - α by ring]
  ring

theorem contDiffAt_alphaForm (hx : ∀ i, x i ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (alphaForm α) x := by
  unfold alphaForm
  refine ContDiffAt.sum fun i _ ↦ ?_
  exact ((contDiff_apply ℝ (fun _ ↦ ℝ) i).contDiffAt.rpow_const_of_ne (hx i)).smul contDiffAt_const

/-! ### The Amari embedding -/

/-- A coordinate of the Amari embedding: `t ↦ p t^(1/p)` with `p = 2/(1 - α)`, and `log` at
`α = 1` (`p = ∞`). -/
noncomputable def amariCoord (α t : ℝ) : ℝ :=
  if α = 1 then Real.log t else 2 / (1 - α) * t ^ ((1 - α) / 2)

/-- **The Amari embedding** `ρ ↦ p ρ^(1/p)` of the positive orthant, coordinatewise, with
`p = 2/(1 - α)`; `ρ ↦ log ρ` at `α = 1`. -/
noncomputable def amariEmbed (α : ℝ) (x : d → ℝ) : d → ℝ :=
  fun i ↦ amariCoord α (x i)

theorem hasDerivAt_amariCoord {t : ℝ} (ht : 0 < t) :
    HasDerivAt (amariCoord α) (t ^ ((-1 - α) / 2)) t := by
  by_cases hα : α = 1
  · have h : amariCoord α = Real.log := funext fun s ↦ by simp [amariCoord, hα]
    rw [h, hα, show ((-1 - 1) / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    exact Real.hasDerivAt_log ht.ne'
  · have h : amariCoord α = fun s ↦ 2 / (1 - α) * s ^ ((1 - α) / 2) :=
      funext fun s ↦ by simp [amariCoord, hα]
    have h1 : 1 - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
    rw [h]
    convert ((Real.hasDerivAt_rpow_const (p := (1 - α) / 2) (Or.inl ht.ne')).const_mul
      (2 / (1 - α))) using 1
    rw [show (1 - α) / 2 - 1 = (-1 - α) / 2 by ring]
    field_simp

omit [Fintype d] in
theorem hasFDerivAt_amariEmbed [Finite d] (hx : ∀ i, 0 < x i) :
    HasFDerivAt (amariEmbed α) (ContinuousLinearMap.pi fun i ↦
      x i ^ ((-1 - α) / 2) • (ContinuousLinearMap.proj i : (d → ℝ) →L[ℝ] ℝ)) x :=
  have := Fintype.ofFinite d
  hasFDerivAt_pi.2 fun i ↦ (hasDerivAt_amariCoord (hx i)).comp_hasFDerivAt x
    (ContinuousLinearMap.proj i : (d → ℝ) →L[ℝ] ℝ).hasFDerivAt

/-- **The α-metric is the Amari pullback of the Euclidean metric**: on the positive orthant,
`A^*(∑ᵢ dyᵢ²) = ∑ᵢ xᵢ^(-1-α) dxᵢ²`. This is the definition of the α-geometry in
Gibilisco–Isola (`A_p` with `p = 2/(1 - α)`, `log` for `p = ∞`). -/
theorem pullback_amariEmbed (hx : ∀ i, 0 < x i) :
    pullback (amariEmbed α) (fun _ ↦ ∑ i, coordForm i) x = alphaForm α x := by
  ext u v
  rw [pullback_apply, (hasFDerivAt_amariEmbed hx).fderiv, alphaForm_apply]
  simp only [sum_apply, coordForm_apply, pi_apply, smul_apply, proj_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h : x i ^ (-1 - α) = x i ^ ((-1 - α) / 2) * x i ^ ((-1 - α) / 2) := by
    rw [← Real.rpow_add (hx i)]
    ring_nf
  rw [h]
  ring

/-! ### The chart -/

variable (α) (V : Submodule ℝ (d → ℝ))

/-- The α-metric in the affine chart `z ↦ x₀ + z` of `x₀ + V`. For `V = simplexTangent d` and
`x₀` a positive probability vector it is the α-geometry of the simplex near `x₀`. -/
noncomputable def alphaChart (x₀ : d → ℝ) : V → V →L[ℝ] V →L[ℝ] ℝ :=
  pullback (fun z : V ↦ V.subtypeL z + x₀) (alphaForm α)

@[simp]
theorem alphaChart_apply (x₀ : d → ℝ) (z u w : V) :
    alphaChart α V x₀ z u w = alphaForm α ((z : d → ℝ) + x₀) u w := by
  rw [alphaChart, pullback_affine]
  rfl

variable {α V} {x₀ : d → ℝ}

theorem contDiff_simplexChartMap {n : WithTop ℕ∞} : ContDiff ℝ n fun z : V ↦ V.subtypeL z + x₀ :=
  V.subtypeL.contDiff.add contDiff_const

theorem contDiffAt_alphaChart (hx : ∀ i, 0 < x₀ i) (n : ℕ) :
    ContDiffAt ℝ n (alphaChart α V x₀) 0 :=
  contDiffAt_pullback (by rw [map_zero, zero_add]; exact contDiffAt_alphaForm fun i ↦ (hx i).ne')
    contDiff_simplexChartMap.contDiffAt

omit [Fintype d] in
/-- Near the centre the chart stays in the positive orthant. -/
theorem eventually_pos_chart [Finite d] (hx : ∀ i, 0 < x₀ i) :
    ∀ᶠ z in 𝓝 (0 : V), ∀ i, 0 < (V.subtypeL z + x₀) i := by
  refine eventually_all.2 fun i ↦ ?_
  have h := ((continuous_apply i).comp (V.subtypeL.continuous.add continuous_const :
    Continuous fun z : V ↦ V.subtypeL z + x₀)).continuousAt (x := 0)
  refine h.eventually (lt_mem_nhds ?_)
  simpa using hx i

theorem fderiv_alphaChart_apply {z : V} (hz : ∀ i, (V.subtypeL z + x₀) i ≠ 0) (X u w : V) :
    fderiv ℝ (alphaChart α V x₀) z X u w =
      fderiv ℝ (alphaForm α) ((z : d → ℝ) + x₀) X u w := by
  have hφ : ∀ y : V, HasFDerivAt (fun z : V ↦ V.subtypeL z + x₀) V.subtypeL y :=
    fun _ ↦ V.subtypeL.hasFDerivAt.add_const x₀
  have hD : fderiv ℝ (fun z : V ↦ V.subtypeL z + x₀) = fun _ ↦ V.subtypeL :=
    funext fun y ↦ (hφ y).fderiv
  have hG : DifferentiableAt ℝ (alphaForm α) (V.subtypeL z + x₀) :=
    (hasFDerivAt_alphaForm hz).differentiableAt
  rw [alphaChart, fderiv_pullback_apply (φ := fun z : V ↦ V.subtypeL z + x₀) hG
    (hφ z).differentiableAt (by rw [hD]; exact differentiableAt_const _), hD]
  simp

theorem eventually_fderiv_alphaChart_comm (hx : ∀ i, 0 < x₀ i) :
    ∀ᶠ z in 𝓝 (0 : V), ∀ X u w,
      fderiv ℝ (alphaChart α V x₀) z X u w = fderiv ℝ (alphaChart α V x₀) z u X w := by
  filter_upwards [eventually_pos_chart hx] with z hz X u w
  have hz' : ∀ i, ((z : d → ℝ) + x₀) i ≠ 0 := fun i ↦ (hz i).ne'
  rw [fderiv_alphaChart_apply hz', fderiv_alphaChart_apply hz',
    fderiv_alphaForm_apply hz', fderiv_alphaForm_apply hz']
  simp only [mul_comm ((X : d → ℝ) _) ((u : d → ℝ) _)]

theorem alphaChart_self_pos (hx : ∀ i, 0 < x₀ i) {u : V} (hu : u ≠ 0) :
    0 < alphaChart α V x₀ 0 u u := by
  rw [alphaChart_apply, ZeroMemClass.coe_zero, zero_add, alphaForm_apply]
  obtain ⟨i, hi⟩ : ∃ i, (u : d → ℝ) i ≠ 0 := by
    by_contra! h
    exact hu (Subtype.ext (funext h))
  refine Finset.sum_pos' (fun j _ ↦ mul_nonneg (Real.rpow_nonneg (hx j).le _)
    (mul_self_nonneg _)) ⟨i, Finset.mem_univ _, ?_⟩
  exact mul_pos (Real.rpow_pos_of_pos (hx i) _) (mul_self_pos.2 hi)

theorem isInvertible_alphaChart (hx : ∀ i, 0 < x₀ i) : (alphaChart α V x₀ 0).IsInvertible :=
  LinearMap.BilinForm.isInvertible_of_pos fun _ hu ↦ alphaChart_self_pos hx hu

/-! ### Contractions against a completeness kernel -/

section Contraction

variable {ι : Type*} [Fintype ι] (e : ι → d → ℝ) (K : d → d → ℝ)
  (hK : ∀ i j, ∑ a, e a i * e a j = K i j)
include hK

/-- Summing `eₐ(i) eₐ(j)` over a family with kernel `K`. -/
theorem sum_mul_mul_eq (H : d → d → ℝ) :
    ∑ a, ∑ i, ∑ j, e a i * e a j * H i j = ∑ i, ∑ j, K i j * H i j := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← hK, Finset.sum_mul]

/-- `|T|²` of the diagonal cubic form `T(u, v, w) = ∑ᵢ tᵢ uᵢ vᵢ wᵢ` in a family with kernel `K`:
`∑ᵢⱼ tᵢ tⱼ Kᵢⱼ³`. -/
theorem sum_sq_sum_cube (t : d → ℝ) :
    ∑ a, ∑ b, ∑ c, (∑ i, t i * (e a i * e b i * e c i)) ^ 2 =
      ∑ i, ∑ j, t i * t j * K i j ^ 3 := by
  calc ∑ a, ∑ b, ∑ c, (∑ i, t i * (e a i * e b i * e c i)) ^ 2
      = ∑ a, ∑ b, ∑ c, ∑ i, ∑ j,
          e c i * e c j * (t i * e a i * e b i * (t j * e a j * e b j)) := by
        simp only [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦
          Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun i _ ↦
          Finset.sum_congr rfl fun j _ ↦ ?_
        ring
    _ = ∑ a, ∑ b, ∑ i, ∑ j, K i j * (t i * e a i * e b i * (t j * e a j * e b j)) := by
        simp only [sum_mul_mul_eq e K hK]
    _ = ∑ a, ∑ b, ∑ i, ∑ j, e b i * e b j * (K i j * (t i * e a i * (t j * e a j))) := by
        refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        ring
    _ = ∑ a, ∑ i, ∑ j, K i j * (K i j * (t i * e a i * (t j * e a j))) := by
        simp only [sum_mul_mul_eq e K hK]
    _ = ∑ a, ∑ i, ∑ j, e a i * e a j * (K i j * K i j * (t i * t j)) := by
        refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun i _ ↦
          Finset.sum_congr rfl fun j _ ↦ ?_
        ring
    _ = ∑ i, ∑ j, t i * t j * K i j ^ 3 := by
        rw [sum_mul_mul_eq e K hK]
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        ring

/-- `|τ|²` of the diagonal cubic form `T(u, v, w) = ∑ᵢ tᵢ uᵢ vᵢ wᵢ` in a family with kernel `K`:
`∑ᵢⱼ tᵢ tⱼ Kᵢᵢ Kⱼⱼ Kᵢⱼ`. -/
theorem sum_sq_sum_trace (t : d → ℝ) :
    ∑ a, (∑ b, ∑ i, t i * (e a i * e b i * e b i)) ^ 2 =
      ∑ i, ∑ j, t i * t j * K i i * K j j * K i j := by
  have hb : ∀ a, ∑ b, ∑ i, t i * (e a i * e b i * e b i) = ∑ i, t i * K i i * e a i :=
    fun a ↦ by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← hK, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ ↦ by ring
  calc ∑ a, (∑ b, ∑ i, t i * (e a i * e b i * e b i)) ^ 2
      = ∑ a, ∑ i, ∑ j, e a i * e a j * (t i * K i i * (t j * K j j)) := by
        simp only [hb, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun i _ ↦
          Finset.sum_congr rfl fun j _ ↦ ?_
        ring
    _ = ∑ i, ∑ j, t i * t j * K i i * K j j * K i j := by
        rw [sum_mul_mul_eq e K hK]
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        ring

end Contraction

/-! ### The completeness kernel -/

section Kernel

variable [DecidableEq d]

/-- The completeness kernel of the α-metric on the simplex, `Kᵢⱼ = wᵢ δᵢⱼ - wᵢ wⱼ / W` with
`w = x^(1+α)` and `W = ∑ₖ wₖ`: the inverse metric `w` restricted to the hyperplane. -/
noncomputable def alphaKernel (α : ℝ) (x : d → ℝ) (i j : d) : ℝ :=
  (if i = j then x i ^ (1 + α) else 0) - x i ^ (1 + α) * x j ^ (1 + α) / ∑ k, x k ^ (1 + α)

theorem rpow_neg_one_sub_mul_rpow {t : ℝ} (ht : 0 < t) (α : ℝ) :
    t ^ (-1 - α) * t ^ (1 + α) = 1 := by
  rw [← Real.rpow_add ht, show -1 - α + (1 + α) = 0 by ring, Real.rpow_zero]

omit [DecidableEq d] in
theorem sum_rpow_pos (hx : ∀ i, 0 < x i) (j : d) (s : ℝ) : 0 < ∑ k, x k ^ s :=
  Finset.sum_pos (fun k _ ↦ Real.rpow_pos_of_pos (hx k) s) ⟨j, Finset.mem_univ _⟩

theorem sum_alphaKernel (hx : ∀ i, 0 < x i) (j : d) : ∑ i, alphaKernel α x i j = 0 := by
  have hW := (sum_rpow_pos hx j (1 + α)).ne'
  simp only [alphaKernel, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.sum_div, ← Finset.sum_mul]
  field_simp
  ring

/-- **The kernel reproduces coordinates**: `G_x(v, K·ⱼ) = vⱼ` on the tangent space. -/
theorem alphaForm_alphaKernel (hx : ∀ i, 0 < x i) {v : d → ℝ} (hv : v ∈ simplexTangent d)
    (j : d) : alphaForm α x v (fun i ↦ alphaKernel α x i j) = v j := by
  set W := ∑ k, x k ^ (1 + α)
  have hterm : ∀ i, x i ^ (-1 - α) * (v i * alphaKernel α x i j) =
      (if i = j then v i else 0) - v i * (x j ^ (1 + α) / W) := fun i ↦ by
    have h1 := rpow_neg_one_sub_mul_rpow (hx i) α
    rw [alphaKernel]
    split_ifs
    · linear_combination (v i - v i * (x j ^ (1 + α) / W)) * h1
    · linear_combination (-(v i * (x j ^ (1 + α) / W))) * h1
  rw [alphaForm_apply, Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', ← Finset.sum_mul, show ∑ i, v i = 0 from hv]
  simp

omit [DecidableEq d] in
/-- An orthonormal basis of the tangent space of the simplex for the α-metric at `x > 0`. -/
theorem exists_orthonormal_basis_simplexTangent (hx : ∀ i, 0 < x i) :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ (simplexTangent d))) ℝ (simplexTangent d),
      ∀ a c, alphaForm α x (b a) (b c) = if a = c then 1 else 0 := by
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (alphaChart α (simplexTangent d) x 0)
    (fun v w ↦ by simp only [alphaChart_apply]; exact alphaForm_comm _ _ _ _)
    (fun v hv ↦ alphaChart_self_pos hx hv)
  exact ⟨b, fun a c ↦ by rw [← hb, alphaChart_apply, ZeroMemClass.coe_zero, zero_add]⟩

/-- **The completeness kernel**: for any `G_x`-orthonormal basis `e` of the tangent space of the
simplex, `∑ₐ eₐ(i) eₐ(j) = wᵢ δᵢⱼ - wᵢ wⱼ / W`. -/
theorem sum_mul_eq_alphaKernel (hx : ∀ i, 0 < x i) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (simplexTangent d))
    (hb : ∀ a c, alphaForm α x (b a) (b c) = if a = c then 1 else 0) (i j : d) :
    ∑ a, (b a : d → ℝ) i * (b a : d → ℝ) j = alphaKernel α x i j := by
  let k : simplexTangent d := ⟨fun i ↦ alphaKernel α x i j, sum_alphaKernel hx j⟩
  have hb' : ∀ a c, alphaChart α (simplexTangent d) x 0 (b a) (b c) = if a = c then 1 else 0 :=
    fun a c ↦ by rw [alphaChart_apply, ZeroMemClass.coe_zero, zero_add, hb]
  have hrepr : ∀ a, b.repr k a = (b a : d → ℝ) j := fun a ↦ by
    rw [repr_eq_of_orthonormal (G := alphaChart α (simplexTangent d) x) (x := 0) b hb',
      alphaChart_apply, ZeroMemClass.coe_zero, zero_add]
    exact alphaForm_alphaKernel hx (b a).2 j
  have := congrArg (fun y : simplexTangent d ↦ (y : d → ℝ) i) (b.sum_repr k)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, hrepr,
    smul_eq_mul] at this
  change _ = (k : d → ℝ) i
  rw [← this]
  exact Finset.sum_congr rfl fun a _ ↦ mul_comm _ _

end Kernel

/-! ### The scalar curvature -/

section Curvature

variable [DecidableEq d]

/-- **The scalar curvature in kernel form**: with `tᵢ = xᵢ^(-2-α)` and `K` the completeness
kernel, `S = ¼ (1 + α)² ∑ᵢⱼ tᵢ tⱼ Kᵢⱼ (Kᵢⱼ² - Kᵢᵢ Kⱼⱼ)`. -/
theorem scalarCurvature_alphaChart_eq_kernel (hx : ∀ i, 0 < x i) :
    scalarCurvature (alphaChart α (simplexTangent d) x) 0 =
      (1 + α) ^ 2 / 4 * ∑ i, ∑ j, x i ^ (-2 - α) * x j ^ (-2 - α) * alphaKernel α x i j *
        (alphaKernel α x i j ^ 2 - alphaKernel α x i i * alphaKernel α x j j) := by
  obtain ⟨b, hb⟩ := exists_orthonormal_basis_simplexTangent (α := α) hx
  have hb' : ∀ a c, alphaChart α (simplexTangent d) x 0 (b a) (b c) = if a = c then 1 else 0 :=
    fun a c ↦ by rw [alphaChart_apply, ZeroMemClass.coe_zero, zero_add, hb]
  have hK := sum_mul_eq_alphaKernel hx b hb
  have hx0 : ∀ i, (((0 : simplexTangent d) : d → ℝ) + x) i ≠ 0 := fun i ↦ by
    simpa using (hx i).ne'
  have hD : ∀ X u w : simplexTangent d, fderiv ℝ (alphaChart α (simplexTangent d) x) 0 X u w =
      -(1 + α) * ∑ i, x i ^ (-2 - α) * ((X : d → ℝ) i * (u : d → ℝ) i * (w : d → ℝ) i) :=
    fun X u w ↦ by
      rw [fderiv_alphaChart_apply hx0, fderiv_alphaForm_apply hx0, ZeroMemClass.coe_zero,
        zero_add]
  have hT := sum_sq_sum_cube (fun a ↦ (b a : d → ℝ)) (alphaKernel α x) hK
    (fun i ↦ x i ^ (-2 - α))
  have hτ := sum_sq_sum_trace (fun a ↦ (b a : d → ℝ)) (alphaKernel α x) hK
    (fun i ↦ x i ^ (-2 - α))
  rw [scalarCurvature_of_fderiv_comm_of_orthonormal (G := alphaChart α (simplexTangent d) x)
    (Eventually.of_forall fun z v w ↦ by
      simp only [alphaChart_apply]; exact alphaForm_comm _ _ _ _)
    (eventually_fderiv_alphaChart_comm hx) (contDiffAt_alphaChart hx 2)
    (isInvertible_alphaChart hx) b hb']
  simp only [hD, mul_pow, neg_sq, ← Finset.mul_sum] at hT hτ ⊢
  rw [hT, hτ, ← mul_sub, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  rw [div_eq_mul_inv, mul_comm ((1 + α) ^ 2) 4⁻¹, mul_assoc]
  congr 2
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- The kernel-form summand off the diagonal: `tᵢ tⱼ Kᵢⱼ (Kᵢⱼ² - Kᵢᵢ Kⱼⱼ) =
xᵢ^α xⱼ^α (W - wᵢ - wⱼ) / W²`, and `0` on it. -/
theorem alphaKernel_summand (hx : ∀ i, 0 < x i) (i j : d) :
    x i ^ (-2 - α) * x j ^ (-2 - α) * alphaKernel α x i j *
        (alphaKernel α x i j ^ 2 - alphaKernel α x i i * alphaKernel α x j j) =
      if i = j then 0 else x i ^ α * x j ^ α *
        (∑ k, x k ^ (1 + α) - x i ^ (1 + α) - x j ^ (1 + α)) / (∑ k, x k ^ (1 + α)) ^ 2 := by
  split_ifs with h
  · subst h
    ring
  set W := ∑ k, x k ^ (1 + α)
  have hW : W * W⁻¹ = 1 := mul_inv_cancel₀ (sum_rpow_pos hx i _).ne'
  have hu : ∀ k, x k ^ (-2 - α) * x k ^ (1 + α) * x k ^ (1 + α) = x k ^ α := fun k ↦ by
    rw [← Real.rpow_add (hx k), ← Real.rpow_add (hx k)]
    ring_nf
  simp only [alphaKernel, h, ite_false, ite_true]
  set c := W⁻¹ - (x i ^ (1 + α) + x j ^ (1 + α)) / W ^ 2
  linear_combination c * (x j ^ (-2 - α) * x j ^ (1 + α) * x j ^ (1 + α)) * hu i +
    c * x i ^ α * hu j - x i ^ α * x j ^ α * W⁻¹ * hW

omit [Fintype d] in
/-- The off-diagonal sum `∑_{i ≠ j} uᵢ uⱼ (W - wᵢ - wⱼ)` in power sums. -/
theorem sum_offDiag_eq [Fintype d] (u w : d → ℝ) (W : ℝ) :
    ∑ i, ∑ j, (if i = j then 0 else u i * u j * (W - w i - w j)) =
      ((∑ i, u i) ^ 2 - ∑ i, u i * u i) * W - 2 * (∑ i, u i) * ∑ i, u i * w i +
        2 * ∑ i, u i * u i * w i := by
  have h : ∀ i j, (if i = j then 0 else u i * u j * (W - w i - w j)) =
      u i * u j * W - u i * w i * u j - u i * (u j * w j) -
        (if i = j then u i * u i * W else 0) + 2 * if i = j then u i * u i * w i else 0 :=
      fun i j ↦ by
    split_ifs with hij
    · subst hij
      ring
    · ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

omit [DecidableEq d] in
/-- **The scalar curvature of the α-geometry of the simplex**, at a positive point `x` (not
necessarily normalized), in power sums `P(s) = ∑ᵢ xᵢˢ`:
`S = (1 + α)²/4 · ((P(α)² - P(2α)) P(1+α) - 2 P(α) P(1+2α) + 2 P(1+3α)) / P(1+α)²`. -/
theorem scalarCurvature_alphaChart (hx : ∀ i, 0 < x i) :
    scalarCurvature (alphaChart α (simplexTangent d) x) 0 =
      (1 + α) ^ 2 / 4 * (((∑ i, x i ^ α) ^ 2 - ∑ i, x i ^ (2 * α)) * ∑ i, x i ^ (1 + α) -
        2 * (∑ i, x i ^ α) * ∑ i, x i ^ (1 + 2 * α) + 2 * ∑ i, x i ^ (1 + 3 * α)) /
        (∑ i, x i ^ (1 + α)) ^ 2 := by
  classical
  have hpow : ∀ i (s t : ℝ), x i ^ s * x i ^ t = x i ^ (s + t) := fun i s t ↦
    (Real.rpow_add (hx i) s t).symm
  have h2 : ∑ i, x i ^ α * x i ^ α = ∑ i, x i ^ (2 * α) :=
    Finset.sum_congr rfl fun i _ ↦ by rw [hpow]; ring_nf
  have h12 : ∑ i, x i ^ α * x i ^ (1 + α) = ∑ i, x i ^ (1 + 2 * α) :=
    Finset.sum_congr rfl fun i _ ↦ by rw [hpow]; ring_nf
  have h13 : ∑ i, x i ^ α * x i ^ α * x i ^ (1 + α) = ∑ i, x i ^ (1 + 3 * α) :=
    Finset.sum_congr rfl fun i _ ↦ by rw [hpow, hpow]; ring_nf
  rw [scalarCurvature_alphaChart_eq_kernel hx]
  simp only [alphaKernel_summand hx]
  have hdiv : ∀ i j, (if i = j then (0 : ℝ) else x i ^ α * x j ^ α *
      (∑ k, x k ^ (1 + α) - x i ^ (1 + α) - x j ^ (1 + α)) / (∑ k, x k ^ (1 + α)) ^ 2) =
      (if i = j then 0 else x i ^ α * x j ^ α *
        (∑ k, x k ^ (1 + α) - x i ^ (1 + α) - x j ^ (1 + α))) / (∑ k, x k ^ (1 + α)) ^ 2 :=
    fun i j ↦ by split_ifs <;> simp
  simp only [hdiv, ← Finset.sum_div]
  rw [sum_offDiag_eq, h2, h12, h13]
  ring

omit [DecidableEq d] in
/-- **The Fisher metric** (`α = 0`) on the `n`-point simplex is a piece of the sphere of radius
`2`: `S = (n - 1)(n - 2)/4` at every positive probability vector. -/
theorem scalarCurvature_alphaChart_zero (hx : ∀ i, 0 < x i) (hsum : ∑ i, x i = 1) :
    scalarCurvature (alphaChart 0 (simplexTangent d) x) 0 =
      ((Fintype.card d : ℝ) - 1) * ((Fintype.card d : ℝ) - 2) / 4 := by
  rw [scalarCurvature_alphaChart hx]
  simp only [mul_zero, add_zero, Real.rpow_zero, Real.rpow_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, hsum]
  ring

end Curvature

end AlphaCurvature
