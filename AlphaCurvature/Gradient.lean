/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Tactic.FieldSimp
import AlphaCurvature.Metric

/-!
# The gradient of the α-curvature

The scalar curvature as a function on the positive orthant (`alphaCurv`), its gradient
(`alphaGrad`), and the gradient difference `∂ᵢS - ∂ⱼS` in terms of the other points.

`alphaCurv α x = (1 + α)²/4 · B / W²`, with `W = P(1+α)`, is the closed form of the scalar
curvature (`scalarCurvature_alphaChart_eq_alphaCurv`), extended to the positive orthant.
Majorization preserves the total, so the Schur–Ostrowski criterion can work there.
`hasDerivAt_alphaCurv` is its directional-derivative hypothesis.

With `a = xᵢ`, `b = xⱼ`, `A = aᵅ`, `B = bᵅ`, the gradient difference is a positive multiple of
the **gradient numerator** `Z = W (∂ᵢ - ∂ⱼ) B - 2 B (∂ᵢ - ∂ⱼ) W`. The other points enter `Z` only
through five power sums `q = (∑ v, ∑ v², ∑ y v, ∑ y v², ∑ y v³)`, `v = yᵅ`. So `Z` is a function
`alphaNum` of `q`, a polynomial of degree at most three, and one point `y` contributes
`alphaMono y v` to `q`.

## Main definitions

* `AlphaCurvature.alphaMono y v`, `AlphaCurvature.alphaNum α a b A B q`: the power sums of one
  point, and the gradient numerator as a function of the power sums.
* `AlphaCurvature.powSum x s`: the power sum `∑ᵢ xᵢˢ`.
* `AlphaCurvature.alphaB`, `AlphaCurvature.alphaCurv`: `B` and `S`.
* `AlphaCurvature.alphaGrad α x i`: `∂ᵢS = (1 + α)²/4 · (W ∂ᵢB - 2 B ∂ᵢW) / W³`.
* `AlphaCurvature.others i j`: the indices other than `i` and `j`.

## Main statements

* `AlphaCurvature.scalarCurvature_alphaChart_eq_alphaCurv`: `S` is the scalar curvature.
* `AlphaCurvature.hasDerivAt_alphaCurv`: `alphaGrad` is the gradient of `alphaCurv`.
* `AlphaCurvature.alphaGrad_sub_alphaGrad`: `∂ᵢS - ∂ⱼS = (1 + α)²/4 · Z / W³`, with `Z` the
  gradient numerator at `(xᵢ, xⱼ)` and the power sums of the other points.
-/

open Finset
open AlphaCurvature.Curvature

namespace AlphaCurvature

/-! ### The gradient numerator in power sums -/

/-- The contribution `(v, v², y v, y v², y v³)` of a point `y` with `v = y^α` to the five power
sums `∑ v`, `∑ v²`, `∑ y v`, `∑ y v²`, `∑ y v³` on which the gradient numerator depends. -/
def alphaMono (y v : ℝ) : Fin 5 → ℝ :=
  ![v, v ^ 2, y * v, y * v ^ 2, y * v ^ 3]

/-- The `a`-derivative of `B = (P(α)² - P(2α)) P(1+α) - 2 P(α) P(1+2α) + 2 P(1+3α)`, where the
power sums are `P(α) = Pa`, `P(2α) = P2a`, `P(1+α) = W`, `P(1+2α) = P12`, and `A = a^α`. -/
noncomputable def alphaBDeriv (α Pa P2a W P12 a A : ℝ) : ℝ :=
  (2 * Pa * (α * A / a) - 2 * α * A ^ 2 / a) * W + (Pa ^ 2 - P2a) * ((1 + α) * A) -
    2 * (α * A / a) * P12 - 2 * Pa * ((1 + 2 * α) * A ^ 2) + 2 * ((1 + 3 * α) * A ^ 3)

/-- **The gradient numerator** `Z = W (∂ₐ - ∂_b) B - 2 B (∂ₐ - ∂_b) W` for the moving pair
`(a, b)` with `A = a^α`, `B = b^α`, as a function of the power sums `q` of the other points. -/
noncomputable def alphaNum (α a b A B : ℝ) (q : Fin 5 → ℝ) : ℝ :=
  (a * A + b * B + q 2) *
      (alphaBDeriv α (A + B + q 0) (A ^ 2 + B ^ 2 + q 1) (a * A + b * B + q 2)
          (a * A ^ 2 + b * B ^ 2 + q 3) a A -
        alphaBDeriv α (A + B + q 0) (A ^ 2 + B ^ 2 + q 1) (a * A + b * B + q 2)
          (a * A ^ 2 + b * B ^ 2 + q 3) b B) -
    2 * (((A + B + q 0) ^ 2 - (A ^ 2 + B ^ 2 + q 1)) * (a * A + b * B + q 2) -
        2 * (A + B + q 0) * (a * A ^ 2 + b * B ^ 2 + q 3) + 2 * (a * A ^ 3 + b * B ^ 3 + q 4)) *
      ((1 + α) * A - (1 + α) * B)

variable {d : Type*} [Fintype d] {α : ℝ}

/-- The power sum `P(s) = ∑ᵢ xᵢˢ`. -/
noncomputable def powSum (x : d → ℝ) (s : ℝ) : ℝ :=
  ∑ i, x i ^ s

/-- `B = (P(α)² - P(2α)) P(1+α) - 2 P(α) P(1+2α) + 2 P(1+3α)`. -/
noncomputable def alphaB (α : ℝ) (x : d → ℝ) : ℝ :=
  (powSum x α ^ 2 - powSum x (2 * α)) * powSum x (1 + α) -
    2 * powSum x α * powSum x (1 + 2 * α) + 2 * powSum x (1 + 3 * α)

/-- **The α-curvature on the positive orthant**, `S = (1 + α)²/4 · B / P(1+α)²`. -/
noncomputable def alphaCurv (α : ℝ) (x : d → ℝ) : ℝ :=
  (1 + α) ^ 2 / 4 * alphaB α x / powSum x (1 + α) ^ 2

theorem scalarCurvature_alphaChart_eq_alphaCurv {x : d → ℝ} (hx : ∀ i, 0 < x i) :
    scalarCurvature (alphaChart α (simplexTangent d) x) 0 = alphaCurv α x := by
  classical
  exact scalarCurvature_alphaChart hx

/-- `∂ᵢB`. -/
noncomputable def alphaBGrad (α : ℝ) (x : d → ℝ) (i : d) : ℝ :=
  alphaBDeriv α (powSum x α) (powSum x (2 * α)) (powSum x (1 + α)) (powSum x (1 + 2 * α)) (x i)
    (x i ^ α)

/-- **The gradient of the α-curvature**, `∂ᵢS = (1 + α)²/4 · (W ∂ᵢB - 2 B ∂ᵢW) / W³` with
`W = P(1+α)` and `∂ᵢW = (1 + α) xᵢ^α`. -/
noncomputable def alphaGrad (α : ℝ) (x : d → ℝ) (i : d) : ℝ :=
  (1 + α) ^ 2 / 4 * (powSum x (1 + α) * alphaBGrad α x i -
    2 * alphaB α x * ((1 + α) * x i ^ α)) / powSum x (1 + α) ^ 3

theorem powSum_pos [Nonempty d] {x : d → ℝ} (hx : ∀ i, 0 < x i) (s : ℝ) : 0 < powSum x s :=
  Finset.sum_pos (fun i _ ↦ Real.rpow_pos_of_pos (hx i) s) univ_nonempty

theorem hasDerivAt_powSum {z : d → ℝ} (hz : ∀ i, 0 < z i) (v : d → ℝ) (s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ powSum (z + t • v) s) (∑ a, v a * s * z a ^ (s - 1)) 0 := by
  unfold powSum
  refine HasDerivAt.fun_sum fun a _ ↦ ?_
  have h1 : HasDerivAt (fun t : ℝ ↦ z a + t * v a) (v a) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v a)).const_add (z a)
  have h2 := h1.rpow_const (p := s) (Or.inl (by simpa using (hz a).ne'))
  convert h2 using 2
  simp

/-- **The directional derivative of the α-curvature** is `∑ₐ ∂ₐS vₐ`: the hypothesis of the
Schur–Ostrowski criterion. -/
theorem hasDerivAt_alphaCurv [Nonempty d] {z : d → ℝ} (hz : ∀ i, 0 < z i) (v : d → ℝ) :
    HasDerivAt (fun t : ℝ ↦ alphaCurv α (z + t • v)) (∑ a, alphaGrad α z a * v a) 0 := by
  have hP := hasDerivAt_powSum hz v
  have hB : HasDerivAt (fun t : ℝ ↦ alphaB α (z + t • v)) _ 0 :=
    ((((hP α).pow 2).sub (hP (2 * α))).mul (hP (1 + α))).sub
      (((hP α).const_mul 2).mul (hP (1 + 2 * α))) |>.add ((hP (1 + 3 * α)).const_mul 2)
  have hW := (powSum_pos hz (1 + α)).ne'
  have hS := (hB.const_mul ((1 + α) ^ 2 / 4)).div ((hP (1 + α)).pow 2)
    (by simpa using pow_ne_zero 2 hW)
  convert hS using 1
  · ext t
    simp [alphaCurv]
  have hz' : ∀ a, z a ≠ 0 := fun a ↦ (hz a).ne'
  have h2 : ∀ a, z a ^ (2 * α) = (z a ^ α) ^ 2 := fun a ↦ by
    rw [mul_comm, Real.rpow_mul (hz a).le, Real.rpow_two]
  have h3 : ∀ a, z a ^ (3 * α) = (z a ^ α) ^ 3 := fun a ↦ by
    rw [mul_comm, Real.rpow_mul (hz a).le]
    norm_cast
  simp only [zero_smul, add_zero, Real.rpow_sub_one (hz' _), add_sub_cancel_left, h2, h3,
    alphaGrad, alphaBGrad, alphaBDeriv, alphaB, Pi.pow_apply, Pi.sub_apply, Nat.cast_ofNat]
  generalize powSum z α = Pa at *
  generalize powSum z (2 * α) = P2a at *
  generalize powSum z (1 + α) = W at *
  generalize powSum z (1 + 2 * α) = P12 at *
  generalize powSum z (1 + 3 * α) = P13 at *
  rw [eq_div_iff (by positivity)]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  have := hz' a
  field_simp
  ring

/-! ### The gradient difference -/

section Difference

variable [DecidableEq d] {x : d → ℝ}

/-- The points other than `i` and `j`. -/
def others (i j : d) : Finset d :=
  (univ.erase i).erase j

theorem sum_univ_eq_add_sum_others {i j : d} (hij : i ≠ j) (f : d → ℝ) :
    ∑ k, f k = f i + f j + ∑ k ∈ others i j, f k := by
  rw [others, ← add_sum_erase _ _ (mem_univ i), ← add_sum_erase _ _ (mem_erase.2 ⟨hij.symm,
    mem_univ j⟩), add_assoc]

/-- **The gradient difference in power sums of the other points**: `∂ᵢS - ∂ⱼS = (1 + α)²/4 · Z /
P(1+α)³`, with `Z = alphaNum` evaluated at the moving pair `(xᵢ, xⱼ)` and the power sums of the
other points. -/
theorem alphaGrad_sub_alphaGrad (hx : ∀ i, 0 < x i) {i j : d} (hij : i ≠ j) :
    alphaGrad α x i - alphaGrad α x j =
      (1 + α) ^ 2 / 4 * alphaNum α (x i) (x j) (x i ^ α) (x j ^ α)
        (∑ k ∈ others i j, alphaMono (x k) (x k ^ α)) / powSum x (1 + α) ^ 3 := by
  have hp : ∀ k (s t : ℝ), x k ^ (s + t) = x k ^ s * x k ^ t :=
    fun k s t ↦ Real.rpow_add (hx k) s t
  have e2 : ∀ k, x k ^ (2 * α) = (x k ^ α) ^ 2 := fun k ↦ by rw [two_mul, hp, sq]
  have e3 : ∀ k, x k ^ (3 * α) = (x k ^ α) ^ 3 := fun k ↦ by
    rw [show 3 * α = α + α + α by ring, hp, hp]
    ring
  have f1 : ∀ k, x k ^ (1 + α) = x k * x k ^ α := fun k ↦ by rw [hp, Real.rpow_one]
  have f2 : ∀ k, x k ^ (1 + 2 * α) = x k * (x k ^ α) ^ 2 := fun k ↦ by
    rw [hp, Real.rpow_one, e2]
  have f3 : ∀ k, x k ^ (1 + 3 * α) = x k * (x k ^ α) ^ 3 := fun k ↦ by
    rw [hp, Real.rpow_one, e3]
  have q : ∀ c, (∑ k ∈ others i j, alphaMono (x k) (x k ^ α)) c =
      ∑ k ∈ others i j, alphaMono (x k) (x k ^ α) c := fun c ↦ Finset.sum_apply _ _ _
  have s0 : x i ^ α + x j ^ α + ∑ k ∈ others i j, alphaMono (x k) (x k ^ α) 0 = powSum x α := by
    rw [powSum, sum_univ_eq_add_sum_others hij]
    rfl
  have s1 : (x i ^ α) ^ 2 + (x j ^ α) ^ 2 + ∑ k ∈ others i j, alphaMono (x k) (x k ^ α) 1 =
      powSum x (2 * α) := by
    rw [powSum, sum_univ_eq_add_sum_others hij]
    simp [alphaMono, e2]
  have s2 : x i * x i ^ α + x j * x j ^ α + ∑ k ∈ others i j, alphaMono (x k) (x k ^ α) 2 =
      powSum x (1 + α) := by
    rw [powSum, sum_univ_eq_add_sum_others hij]
    simp [alphaMono, f1]
  have s3 : x i * (x i ^ α) ^ 2 + x j * (x j ^ α) ^ 2 +
      ∑ k ∈ others i j, alphaMono (x k) (x k ^ α) 3 = powSum x (1 + 2 * α) := by
    rw [powSum, sum_univ_eq_add_sum_others hij]
    simp [alphaMono, f2]
  have s4 : x i * (x i ^ α) ^ 3 + x j * (x j ^ α) ^ 3 +
      ∑ k ∈ others i j, alphaMono (x k) (x k ^ α) 4 = powSum x (1 + 3 * α) := by
    rw [powSum, sum_univ_eq_add_sum_others hij]
    simp [alphaMono, f3]
  simp only [alphaNum, q, s0, s1, s2, s3, s4, alphaGrad, alphaBGrad, alphaB]
  ring

end Difference

end AlphaCurvature
