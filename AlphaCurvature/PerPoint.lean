/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import AlphaCurvature.Gradient

/-!
# The per-point form of the α-curvature gradient

The gradient numerator `Z` (`alphaNum`) has the sign of `-α` for every `α ∈ (-1, 0) ∪ (0, 1]`,
when `a > b` and there is at least one other point. The proof splits `Z` into one term per point.

`Z` is a polynomial of degree at most three in the power sums `q` of the other points. Assign
each of its monomials to the power sum of highest index that it contains. Then
`Z(q) = ∑ᵢ qᵢ Hᵢ(q)`, and so `Z = ∑ₖ Ψ(yₖ; q)` with `Ψ(y; q) = ∑ᵢ mᵢ(y) Hᵢ(q)`
(`alphaNum_sum_eq_sum_alphaPsi`). In closed form (`alphaPsi`), with `S₀ = ∑ v`, `S₁ = ∑ v²`,
`U = ∑ y v` over all the other points (`y` included), `c = (1+α)(A - B)` and
`κ = 2αAB(1/b - 1/a)`:

`Ψ = -Γ (a+b+y) v - c (Aa+Bb) v (S₀ - v) - c yv (S₀ - 2v)² - 2yv (C S₀ - C' v)`
`  - 2α (B/b - A/a) yv U (S₀ - v) + yv (c S₁ - κ U)`.

* For `0 < α ≤ 1`, every term but the last is `≤ 0`. The last, together with `-2yv C S₀`, is a
  sum over the points `l` of `yv · vₗ (c vₗ - κ yₗ - 2C)`, and the one-variable inequality
  `c sᵅ - κ s ≤ 2(C - C')` (`alphaPsi_key`) bounds each summand. It follows from the tangent line
  of `sᵅ` at `b`, then `a^(α-1) ≤ b^(α-1)`, then Bernoulli. So `Ψ < 0` (`alphaPsi_neg`).
* For `-1 < α < 0`, every term but `c yv S₁` is `≥ 0`. Together with the square, that term costs
  at most `-2c yv² (S₀ - v)`, since `∑ₗ vₗ² ≤ (∑ₗ vₗ)²` over the other points. The tangent line
  of `t^(1+α)` at `b` bounds `yv = y^(1+α)`, and the remaining coefficient of `v (S₀ - v)` is then
  `≥ 0`. So `Ψ > 0` (`alphaPsi_pos`).

At `α = 1` the expansion is a sum of squares, with top-degree part
`-2(a - b) ∑ₖ yₖ² (∑ₗ yₗ - 2yₖ)²`.

## Main definitions

* `AlphaCurvature.alphaPsi α a b A B y v q`: the per-point term.

## Main statements

* `AlphaCurvature.alphaNum_sum_eq_sum_alphaPsi`: the per-point expansion of `Z`.
* `AlphaCurvature.alphaPsi_key`: the one-variable inequality.
* `AlphaCurvature.alphaPsi_neg`, `alphaPsi_pos`: the sign of `Ψ`.
* `AlphaCurvature.alphaNum_neg`, `alphaNum_nonpos`, `alphaNum_pos`, `alphaNum_nonneg`: the sign
  of `Z`.

## References

* [P. Gibilisco, T. Isola, *On the monotonicity of scalar curvature in classical and quantum
  information geometry*][gibilisco2004], J. Math. Phys. 46 (2005), arXiv math-ph/0407007.
* [P. Gibilisco, *Lp unit spheres and the α-geometries: questions and perspectives*][gibilisco2020],
  Entropy 22 (2020) 1409.
-/

open Finset

namespace AlphaCurvature

/-! ### Elementary bounds for powers -/

section Rpow

variable {α a b c y p : ℝ}

/-- `a^α - b^α ≤ α b^α (a - b) / b` for `0 ≤ α ≤ 1` and `a ≥ b > 0` (concavity of `t^α`). -/
theorem rpow_sub_rpow_le (hb : 0 < b) (hab : b ≤ a) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    a ^ α - b ^ α ≤ α * b ^ α * (a - b) / b := by
  have ha : 0 < a := hb.trans_le hab
  have h := rpow_one_add_le_one_add_mul_self (s := a / b - 1)
    (by have : 0 ≤ a / b - 1 := by rw [sub_nonneg, le_div_iff₀ hb]; linarith
        linarith) h0 h1
  rw [add_sub_cancel, Real.div_rpow ha.le hb.le] at h
  have hB := Real.rpow_pos_of_pos hb α
  rw [div_le_iff₀ hB] at h
  have e : α * b ^ α * (a - b) / b = α * (a / b - 1) * b ^ α := by field_simp
  rw [e]
  linarith

/-- For `α > 0`, `bᵅ/a < aᵅ/b` when `a > b > 0`. -/
theorem rpow_div_lt_rpow_div (hb : 0 < b) (hab : b < a) (hα : 0 < α) :
    b ^ α / a < a ^ α / b := by
  have h := Real.rpow_lt_rpow hb.le hab hα
  have ha := hb.trans hab
  calc b ^ α / a < b ^ α / b := div_lt_div_of_pos_left (Real.rpow_pos_of_pos hb α) hb hab
    _ < a ^ α / b := div_lt_div_of_pos_right h hb

/-- For `α > -1`, `bᵅ/a < aᵅ/b`, i.e. `b^(1+α) < a^(1+α)`. -/
theorem rpow_div_lt_rpow_div_of_neg (hb : 0 < b) (hab : b < a) (hα : -1 < α) :
    b ^ α / a < a ^ α / b := by
  have ha := hb.trans hab
  have h := Real.rpow_lt_rpow hb.le hab (show 0 < 1 + α by linarith)
  rw [Real.rpow_add hb, Real.rpow_add ha, Real.rpow_one, Real.rpow_one] at h
  rw [div_lt_div_iff₀ ha hb]
  linarith

/-- The tangent-line bound for the concave power `t ↦ t^p`, `0 ≤ p ≤ 1`:
`y^p ≤ c^p + p c^p (y - c) / c`. -/
theorem rpow_le_tangent (hc : 0 < c) (hy : 0 ≤ y) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    y ^ p ≤ c ^ p + p * c ^ p * (y - c) / c := by
  have h := rpow_one_add_le_one_add_mul_self (s := y / c - 1)
    (by have : 0 ≤ y / c := by positivity
        linarith) h0 h1
  rw [add_sub_cancel, Real.div_rpow hy hc.le] at h
  have hC := Real.rpow_pos_of_pos hc p
  rw [div_le_iff₀ hC] at h
  have e : (1 + p * (y / c - 1)) * c ^ p = c ^ p + p * c ^ p * (y - c) / c := by
    field_simp
  linarith

end Rpow


variable {α a b A B : ℝ}

/-- **The per-point term** `Ψ(y; q)` of the gradient numerator, for a point `y` with `v = yᵅ` and
the power sums `q` of all the other points (including `y`): with `S₀ = q 0`, `S₁ = q 1`,
`U = q 2`,
`Ψ = -Γ (a+b+y) v - c (Aa+Bb) v (S₀ - v) - c yv (S₀ - 2v)² - 2yv (C S₀ - C' v)
  - 2α D yv U (S₀ - v) + yv (c S₁ - κ U)`. -/
noncomputable def alphaPsi (α a b A B y v : ℝ) (q : Fin 5 → ℝ) : ℝ :=
  -(2 * A * B * (α * (a + b) * (A / b - B / a) + 2 * (A - B))) * (a + b + y) * v -
    (1 + α) * (A - B) * (A * a + B * b) * v * (q 0 - v) -
    (1 + α) * (A - B) * (y * v) * (q 0 - 2 * v) ^ 2 -
    2 * (y * v) * (((α + 2) * (A ^ 2 - B ^ 2) + 2 * α * A * B * (a / b - b / a)) * q 0 -
      ((α + 2) * (A ^ 2 - B ^ 2) + α * A * B * (a / b - b / a)) * v) -
    2 * α * (B / b - A / a) * (y * v) * q 2 * (q 0 - v) +
    (y * v) * ((1 + α) * (A - B) * q 1 - 2 * α * A * B * (1 / b - 1 / a) * q 2)

/-- `Ψ` is linear in the monomials `(v, v², yv, yv², yv³)` of the point. -/
theorem alphaPsi_eq (α a b A B y v : ℝ) (q : Fin 5 → ℝ) :
    alphaPsi α a b A B y v q =
      v * (-(2 * A * B * (α * (a + b) * (A / b - B / a) + 2 * (A - B))) * (a + b) -
          (1 + α) * (A - B) * (A * a + B * b) * q 0) +
        v ^ 2 * ((1 + α) * (A - B) * (A * a + B * b)) +
        y * v * (-(2 * α * A * B * (1 / b - 1 / a)) * q 2 -
          2 * A * B * (α * (a + b) * (A / b - B / a) + 2 * (A - B)) -
          (1 + α) * (A - B) * q 0 ^ 2 + (1 + α) * (A - B) * q 1 -
          2 * ((α + 2) * (A ^ 2 - B ^ 2) + 2 * α * A * B * (a / b - b / a)) * q 0 -
          2 * α * (B / b - A / a) * q 0 * q 2) +
        y * v ^ 2 * (4 * (1 + α) * (A - B) * q 0 + 2 * α * (B / b - A / a) * q 2 +
          2 * ((α + 2) * (A ^ 2 - B ^ 2) + α * A * B * (a / b - b / a))) +
        y * v ^ 3 * (-(4 * (1 + α) * (A - B))) := by
  unfold alphaPsi
  ring

/-- **The per-point expansion**: the gradient numerator at the power sums of the points `O` is
the sum over the points of `O` of their per-point terms. -/
theorem alphaNum_sum_eq_sum_alphaPsi {ι : Type*} (ha : a ≠ 0) (hb : b ≠ 0) (O : Finset ι)
    (y v : ι → ℝ) :
    alphaNum α a b A B (∑ k ∈ O, alphaMono (y k) (v k)) =
      ∑ k ∈ O, alphaPsi α a b A B (y k) (v k) (∑ k ∈ O, alphaMono (y k) (v k)) := by
  set q := ∑ k ∈ O, alphaMono (y k) (v k) with hq
  have e : ∀ i, q i = ∑ k ∈ O, alphaMono (y k) (v k) i := fun i ↦ by rw [hq, Finset.sum_apply]
  have s0 : ∑ k ∈ O, v k = q 0 := by rw [e]; simp [alphaMono]
  have s1 : ∑ k ∈ O, v k ^ 2 = q 1 := by rw [e]; simp [alphaMono]
  have s2 : ∑ k ∈ O, y k * v k = q 2 := by rw [e]; simp [alphaMono]
  have s3 : ∑ k ∈ O, y k * v k ^ 2 = q 3 := by rw [e]; simp [alphaMono]
  have s4 : ∑ k ∈ O, y k * v k ^ 3 = q 4 := by rw [e]; simp [alphaMono]
  simp only [alphaPsi_eq, sum_add_distrib, ← sum_mul, s0, s1, s2, s3, s4]
  unfold alphaNum alphaBDeriv
  field_simp
  ring

/-! ### The sign of the per-point term -/

variable {s : ℝ}

/-- **The one-variable lemma**: for `0 < α ≤ 1` and `a > b > 0`,
`(1+α)(aᵅ - bᵅ) sᵅ - 2α aᵅbᵅ (1/b - 1/a) s ≤ 2α aᵅbᵅ (a/b - b/a)` for every `s > 0`. -/
theorem alphaPsi_key (hα : 0 < α) (hα₁ : α ≤ 1) (hb : 0 < b) (hab : b < a) (hs : 0 < s) :
    (1 + α) * (a ^ α - b ^ α) * s ^ α - 2 * α * a ^ α * b ^ α * (1 / b - 1 / a) * s ≤
      2 * α * a ^ α * b ^ α * (a / b - b / a) := by
  have ha := hb.trans hab
  have hA := Real.rpow_pos_of_pos ha α
  have hB := Real.rpow_pos_of_pos hb α
  have hK : 0 < a ^ α - b ^ α := sub_pos.2 (Real.rpow_lt_rpow hb.le hab hα)
  have hc : 0 < (1 + α) * (a ^ α - b ^ α) := mul_pos (by linarith) hK
  -- the tangent line of `sᵅ` at `b`
  have ht := rpow_le_tangent hb hs.le hα.le hα₁
  have h1 := mul_le_mul_of_nonneg_left ht hc.le
  -- `aᵅ b ≤ bᵅ a`
  have hAb : a ^ α * b ≤ b ^ α * a := by
    have h := Real.rpow_le_rpow_of_nonpos hb hab.le (by linarith : α - 1 ≤ 0)
    rw [Real.rpow_sub_one ha.ne', Real.rpow_sub_one hb.ne', div_le_div_iff₀ ha hb] at h
    linarith
  -- the coefficient of `s`
  have hs1 : (1 + α) * (a ^ α - b ^ α) * (α * b ^ α / b) ≤
      2 * α * a ^ α * b ^ α * (1 / b - 1 / a) := by
    have e1 : (1 + α) * (a ^ α - b ^ α) * (α * b ^ α / b) =
        α * b ^ α / (a * b) * ((1 + α) * ((a ^ α - b ^ α) * a)) := by
      field_simp
    have e2 : 2 * α * a ^ α * b ^ α * (1 / b - 1 / a) =
        α * b ^ α / (a * b) * (2 * (a ^ α * (a - b))) := by
      field_simp
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have : (a ^ α - b ^ α) * a ≤ a ^ α * (a - b) := by nlinarith
    have : 0 ≤ a ^ α * (a - b) := mul_nonneg hA.le (by linarith)
    nlinarith
  -- the constant
  have hs0 : (1 + α) * (a ^ α - b ^ α) * (b ^ α - α * b ^ α) ≤
      2 * α * a ^ α * b ^ α * (a / b - b / a) := by
    have hKle := rpow_sub_rpow_le hb hab.le hα.le hα₁
    have hr : (a - b) / b ≤ a / b - b / a := by
      rw [div_sub_div _ _ hb.ne' ha.ne', div_le_div_iff₀ hb (by positivity)]
      nlinarith
    have e : (1 + α) * (a ^ α - b ^ α) * (b ^ α - α * b ^ α) =
        (1 - α ^ 2) * b ^ α * (a ^ α - b ^ α) := by ring
    rw [e]
    have h1α : 0 ≤ 1 - α ^ 2 := by nlinarith
    have hKle' : a ^ α - b ^ α ≤ α * a ^ α * ((a - b) / b) := by
      have : α * b ^ α * (a - b) / b ≤ α * a ^ α * ((a - b) / b) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hb.le hab.le hα.le) hα.le)
          (div_nonneg (by linarith) hb.le)
      linarith
    have hab' : 0 ≤ (a - b) / b := div_nonneg (by linarith) hb.le
    calc (1 - α ^ 2) * b ^ α * (a ^ α - b ^ α) ≤ 1 * b ^ α * (a ^ α - b ^ α) := by
          gcongr
          nlinarith
      _ ≤ b ^ α * (α * a ^ α * ((a - b) / b)) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left hKle' hB.le
      _ ≤ 2 * α * a ^ α * b ^ α * (a / b - b / a) := by
          have := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ α * a ^ α * b ^ α)
          have : 0 ≤ α * a ^ α * b ^ α * (a / b - b / a) := le_trans (by positivity) this
          nlinarith
  have e : b ^ α + α * b ^ α * (s - b) / b = (b ^ α - α * b ^ α) + α * b ^ α / b * s := by
    field_simp
    ring
  rw [e] at h1
  have := mul_le_mul_of_nonneg_right hs1 hs.le
  nlinarith

/-- **The per-point term is negative** for `0 < α ≤ 1` and `a > b > 0`: at a point `j` of a set
`O` of positive points, with the power sums of `O`. -/
theorem alphaPsi_neg {ι : Type*} (hα : 0 < α) (hα₁ : α ≤ 1) (hb : 0 < b) (hab : b < a)
    {y : ι → ℝ} (hy : ∀ k, 0 < y k) {O : Finset ι} {j : ι} (hj : j ∈ O) :
    alphaPsi α a b (a ^ α) (b ^ α) (y j) (y j ^ α) (∑ k ∈ O, alphaMono (y k) (y k ^ α)) < 0 := by
  classical
  have ha := hb.trans hab
  have hA := Real.rpow_pos_of_pos ha α
  have hB := Real.rpow_pos_of_pos hb α
  have hK : 0 < a ^ α - b ^ α := sub_pos.2 (Real.rpow_lt_rpow hb.le hab hα)
  have hc : 0 < (1 + α) * (a ^ α - b ^ α) := mul_pos (by linarith) hK
  have hv : ∀ k, 0 < y k ^ α := fun k ↦ Real.rpow_pos_of_pos (hy k) α
  set q := ∑ k ∈ O, alphaMono (y k) (y k ^ α) with hq
  have e : ∀ i, q i = ∑ k ∈ O, alphaMono (y k) (y k ^ α) i := fun i ↦ by
    rw [hq, Finset.sum_apply]
  have s0 : q 0 = ∑ k ∈ O, y k ^ α := by rw [e]; simp [alphaMono]
  have s1 : q 1 = ∑ k ∈ O, (y k ^ α) ^ 2 := by rw [e]; simp [alphaMono]
  have s2 : q 2 = ∑ k ∈ O, y k * y k ^ α := by rw [e]; simp [alphaMono]
  -- the other points
  have hR : q 0 - y j ^ α = ∑ k ∈ O.erase j, y k ^ α := by
    rw [s0, ← add_sum_erase _ _ hj]
    ring
  have hR0 : 0 ≤ q 0 - y j ^ α := hR ▸ sum_nonneg fun k _ ↦ (hv k).le
  have hU : 0 ≤ q 2 := s2 ▸ sum_nonneg fun k _ ↦ (mul_pos (hy k) (hv k)).le
  -- the signs of the coefficients
  have hΓ : 0 < 2 * a ^ α * b ^ α *
      (α * (a + b) * (a ^ α / b - b ^ α / a) + 2 * (a ^ α - b ^ α)) := by
    have := sub_pos.2 (rpow_div_lt_rpow_div hb hab hα)
    have : 0 < α * (a + b) * (a ^ α / b - b ^ α / a) := by positivity
    have : 0 < α * (a + b) * (a ^ α / b - b ^ α / a) + 2 * (a ^ α - b ^ α) := by linarith
    positivity
  have hD : 0 ≤ b ^ α / b - a ^ α / a := by
    rw [← Real.rpow_sub_one ha.ne', ← Real.rpow_sub_one hb.ne', sub_nonneg]
    exact Real.rpow_le_rpow_of_nonpos hb hab.le (by linarith)
  have hr : 0 ≤ a / b - b / a := by
    rw [sub_nonneg, div_le_div_iff₀ ha hb]
    nlinarith
  have hC' : 0 ≤ (α + 2) * ((a ^ α) ^ 2 - (b ^ α) ^ 2) +
      α * a ^ α * b ^ α * (a / b - b / a) := by
    have : 0 ≤ (a ^ α) ^ 2 - (b ^ α) ^ 2 := by nlinarith
    positivity
  -- the bad term, point by point
  have hsum : ∑ k ∈ O, ((1 + α) * (a ^ α - b ^ α) * (y k ^ α) ^ 2 -
      2 * α * a ^ α * b ^ α * (1 / b - 1 / a) * (y k * y k ^ α) -
      2 * α * a ^ α * b ^ α * (a / b - b / a) * y k ^ α) ≤ 0 := by
    refine sum_nonpos fun k _ ↦ ?_
    have h := mul_le_mul_of_nonneg_left (alphaPsi_key hα hα₁ hb hab (hy k)) (hv k).le
    linarith
  simp only [sum_sub_distrib, ← mul_sum] at hsum
  rw [← s0, ← s1, ← s2] at hsum
  have hyv : 0 < y j * y j ^ α := mul_pos (hy j) (hv j)
  have t46 : y j * y j ^ α * ((1 + α) * (a ^ α - b ^ α) * q 1 -
      2 * α * a ^ α * b ^ α * (1 / b - 1 / a) * q 2 -
      2 * (((α + 2) * ((a ^ α) ^ 2 - (b ^ α) ^ 2) + 2 * α * a ^ α * b ^ α * (a / b - b / a)) *
        q 0 - ((α + 2) * ((a ^ α) ^ 2 - (b ^ α) ^ 2) + α * a ^ α * b ^ α * (a / b - b / a)) *
          y j ^ α)) ≤ 0 := by
    refine mul_nonpos_of_nonneg_of_nonpos hyv.le ?_
    have := mul_nonneg hC' hR0
    linarith
  have t1 : 0 < 2 * a ^ α * b ^ α *
      (α * (a + b) * (a ^ α / b - b ^ α / a) + 2 * (a ^ α - b ^ α)) * (a + b + y j) *
        y j ^ α := by
    have := hy j
    have := hv j
    positivity
  have t2 : 0 ≤ (1 + α) * (a ^ α - b ^ α) * (a ^ α * a + b ^ α * b) * y j ^ α *
      (q 0 - y j ^ α) := by
    have := hv j
    positivity
  have t3 : 0 ≤ (1 + α) * (a ^ α - b ^ α) * (y j * y j ^ α) * (q 0 - 2 * y j ^ α) ^ 2 := by
    positivity
  have t5 : 0 ≤ 2 * α * (b ^ α / b - a ^ α / a) * (y j * y j ^ α) * q 2 *
      (q 0 - y j ^ α) := by
    positivity
  unfold alphaPsi
  linarith

/-- For `0 < α ≤ 1`, the per-point expansion of the gradient numerator is negative when there
are other points. -/
theorem alphaNum_neg {ι : Type*} (hα : 0 < α) (hα₁ : α ≤ 1) (hb : 0 < b) (hab : b < a)
    {y : ι → ℝ} (hy : ∀ k, 0 < y k) {O : Finset ι} (hO : O.Nonempty) :
    alphaNum α a b (a ^ α) (b ^ α) (∑ k ∈ O, alphaMono (y k) (y k ^ α)) < 0 := by
  have ha := hb.trans hab
  rw [alphaNum_sum_eq_sum_alphaPsi ha.ne' hb.ne']
  exact sum_neg (fun j hj ↦ alphaPsi_neg hα hα₁ hb hab hy hj) hO

/-- For `0 < α ≤ 1`, the gradient numerator is `≤ 0`. -/
theorem alphaNum_nonpos {ι : Type*} (hα : 0 < α) (hα₁ : α ≤ 1) (hb : 0 < b) (hab : b < a)
    {y : ι → ℝ} (hy : ∀ k, 0 < y k) (O : Finset ι) :
    alphaNum α a b (a ^ α) (b ^ α) (∑ k ∈ O, alphaMono (y k) (y k ^ α)) ≤ 0 := by
  have ha := hb.trans hab
  rw [alphaNum_sum_eq_sum_alphaPsi ha.ne' hb.ne']
  exact sum_nonpos fun j hj ↦ (alphaPsi_neg hα hα₁ hb hab hy hj).le

/-- `∑ fₖ² ≤ (∑ fₖ)²` for nonnegative `f`. -/
theorem sum_sq_le_sq_sum {ι : Type*} {O : Finset ι} {f : ι → ℝ} (hf : ∀ k ∈ O, 0 ≤ f k) :
    ∑ k ∈ O, f k ^ 2 ≤ (∑ k ∈ O, f k) ^ 2 := by
  rw [sq, sum_mul]
  refine sum_le_sum fun k hk ↦ ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (single_le_sum hf hk) (hf k hk)

/-- **The per-point term is positive** for `-1 < α < 0` and `a > b > 0`: at a point `j` of a set
`O` of positive points, with the power sums of `O`. -/
theorem alphaPsi_pos {ι : Type*} (hα₁ : -1 < α) (hα : α < 0) (hb : 0 < b) (hab : b < a)
    {y : ι → ℝ} (hy : ∀ k, 0 < y k) {O : Finset ι} {j : ι} (hj : j ∈ O) :
    0 < alphaPsi α a b (a ^ α) (b ^ α) (y j) (y j ^ α) (∑ k ∈ O, alphaMono (y k) (y k ^ α)) := by
  classical
  have ha := hb.trans hab
  have hA := Real.rpow_pos_of_pos ha α
  have hB := Real.rpow_pos_of_pos hb α
  have hAB : a ^ α < b ^ α := Real.rpow_lt_rpow_of_neg hb hab hα
  have hv : ∀ k, 0 < y k ^ α := fun k ↦ Real.rpow_pos_of_pos (hy k) α
  set q := ∑ k ∈ O, alphaMono (y k) (y k ^ α) with hq
  have e : ∀ i, q i = ∑ k ∈ O, alphaMono (y k) (y k ^ α) i := fun i ↦ by
    rw [hq, Finset.sum_apply]
  have s0 : q 0 = ∑ k ∈ O, y k ^ α := by rw [e]; simp [alphaMono]
  have s1 : q 1 = ∑ k ∈ O, (y k ^ α) ^ 2 := by rw [e]; simp [alphaMono]
  have s2 : q 2 = ∑ k ∈ O, y k * y k ^ α := by rw [e]; simp [alphaMono]
  -- the other points
  have hR : q 0 - y j ^ α = ∑ k ∈ O.erase j, y k ^ α := by
    rw [s0, ← add_sum_erase _ _ hj]
    ring
  have hR0 : 0 ≤ q 0 - y j ^ α := hR ▸ sum_nonneg fun k _ ↦ (hv k).le
  have hS1 : q 1 - (y j ^ α) ^ 2 ≤ (q 0 - y j ^ α) ^ 2 := by
    have h1 : q 1 - (y j ^ α) ^ 2 = ∑ k ∈ O.erase j, (y k ^ α) ^ 2 := by
      rw [s1, ← add_sum_erase _ _ hj]
      ring
    rw [h1, hR]
    exact sum_sq_le_sq_sum fun k _ ↦ (hv k).le
  have hU : 0 ≤ q 2 := s2 ▸ sum_nonneg fun k _ ↦ (mul_pos (hy k) (hv k)).le
  -- signs of the coefficients
  have hc : (1 + α) * (a ^ α - b ^ α) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
  have hAa : b ^ α * b < a ^ α * a := by
    have h := rpow_div_lt_rpow_div_of_neg hb hab hα₁
    rw [div_lt_div_iff₀ ha hb] at h
    linarith
  have hr : 0 < a / b - b / a := by
    rw [sub_pos, div_lt_div_iff₀ ha hb]
    nlinarith
  have hr' : 0 < 1 / b - 1 / a := sub_pos.2 (one_div_lt_one_div_of_lt hb hab)
  have hD : 0 ≤ b ^ α / b - a ^ α / a := by
    rw [← Real.rpow_sub_one ha.ne', ← Real.rpow_sub_one hb.ne', sub_nonneg]
    exact (Real.rpow_lt_rpow_of_neg hb hab (by linarith)).le
  have hΓ : 2 * a ^ α * b ^ α *
      (α * (a + b) * (a ^ α / b - b ^ α / a) + 2 * (a ^ α - b ^ α)) < 0 := by
    have := sub_pos.2 (rpow_div_lt_rpow_div_of_neg hb hab hα₁)
    have : 0 < -α * (a + b) * (a ^ α / b - b ^ α / a) := by
      have := neg_pos.2 hα
      positivity
    have : α * (a + b) * (a ^ α / b - b ^ α / a) + 2 * (a ^ α - b ^ α) < 0 := by linarith
    exact mul_neg_of_pos_of_neg (by positivity) this
  -- the tangent line of `t^(1+α)` at `b`
  have htan : y j * y j ^ α ≤ -α * (b ^ α * b) + (1 + α) * (b ^ α * y j) := by
    have h := rpow_le_tangent hb (hy j).le (p := 1 + α) (by linarith) (by linarith)
    rw [add_comm 1 α, Real.rpow_add_one hb.ne', Real.rpow_add_one (hy j).ne'] at h
    have e : b ^ α * b + (α + 1) * (b ^ α * b) * (y j - b) / b =
        -α * (b ^ α * b) + (1 + α) * (b ^ α * y j) := by
      field_simp
      ring
    linarith
  -- the coefficient of `v R`
  have hX : 0 ≤ (1 + α) * (a ^ α - b ^ α) * (1 + α) * b ^ α -
      ((α + 2) * ((a ^ α) ^ 2 - (b ^ α) ^ 2) + 2 * α * a ^ α * b ^ α * (a / b - b / a)) := by
    have k1 : 0 < -α * (a ^ α * b ^ α) * (a / b - b / a) :=
      mul_pos (mul_pos (neg_pos.2 hα) (mul_pos hA hB)) hr
    have k2 : (1 + α) ^ 2 ≤ α + 2 := by nlinarith
    have k3 : (1 + α) ^ 2 * ((b ^ α - a ^ α) * b ^ α) ≤
        (α + 2) * ((b ^ α - a ^ α) * (b ^ α + a ^ α)) := by
      have h0 : 0 ≤ (b ^ α - a ^ α) * b ^ α := mul_nonneg (by linarith) hB.le
      have h1 : (b ^ α - a ^ α) * b ^ α ≤ (b ^ α - a ^ α) * (b ^ α + a ^ α) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      exact mul_le_mul k2 h1 h0 (by linarith)
    linarith
  have hβ : 0 ≤ -((1 + α) * (a ^ α - b ^ α)) * (a ^ α * a + b ^ α * b) +
      2 * ((1 + α) * (a ^ α - b ^ α)) * (y j * y j ^ α) -
      2 * ((α + 2) * ((a ^ α) ^ 2 - (b ^ α) ^ 2) + 2 * α * a ^ α * b ^ α * (a / b - b / a)) *
        y j := by
    have t1 := mul_le_mul_of_nonpos_left htan (by linarith : 2 * ((1 + α) * (a ^ α - b ^ α)) ≤ 0)
    have t2 : 0 ≤ -((1 + α) * (a ^ α - b ^ α)) *
        (a ^ α * a + b ^ α * b + 2 * α * (b ^ α * b)) := by
      refine mul_nonneg (by linarith) ?_
      have : 0 < (1 + α) * (b ^ α * b) := mul_pos (by linarith) (mul_pos hB hb)
      linarith
    have t3 := mul_nonneg hX (hy j).le
    linarith
  have hyv : 0 < y j * y j ^ α := mul_pos (hy j) (hv j)
  have f2 : 2 * ((1 + α) * (a ^ α - b ^ α)) * (y j * y j ^ α) * y j ^ α * (q 0 - y j ^ α) ≤
      -((1 + α) * (a ^ α - b ^ α)) * (y j * y j ^ α) * ((q 0 - 2 * y j ^ α) ^ 2 - q 1) := by
    have h : -(2 * y j ^ α * (q 0 - y j ^ α)) ≤ (q 0 - 2 * y j ^ α) ^ 2 - q 1 := by linarith
    have := mul_le_mul_of_nonneg_left h (mul_nonneg (by linarith) hyv.le :
      0 ≤ -((1 + α) * (a ^ α - b ^ α)) * (y j * y j ^ α))
    linarith
  have f3 := mul_nonneg (mul_nonneg (hv j).le hR0) hβ
  have f4 : 0 ≤ -(2 * (y j * y j ^ α) * (α * a ^ α * b ^ α * (a / b - b / a)) * y j ^ α) := by
    have := neg_pos.2 hα
    have : 0 < -α * a ^ α * b ^ α * (a / b - b / a) * (y j * y j ^ α) * y j ^ α := by
      have := hv j
      positivity
    linarith
  have f5 : 0 ≤ -(2 * α * (b ^ α / b - a ^ α / a) * (y j * y j ^ α) * q 2 * (q 0 - y j ^ α)) := by
    have := neg_pos.2 hα
    have : 0 ≤ -α * (b ^ α / b - a ^ α / a) * (y j * y j ^ α) * q 2 * (q 0 - y j ^ α) := by
      positivity
    linarith
  have f6 : 0 ≤ -(2 * α * a ^ α * b ^ α * (1 / b - 1 / a)) * (y j * y j ^ α) * q 2 := by
    have := neg_pos.2 hα
    have : 0 ≤ -α * a ^ α * b ^ α * (1 / b - 1 / a) * (y j * y j ^ α) * q 2 := by positivity
    linarith
  have f1 : 0 < -(2 * a ^ α * b ^ α *
      (α * (a + b) * (a ^ α / b - b ^ α / a) + 2 * (a ^ α - b ^ α))) * (a + b + y j) * y j ^ α := by
    have := hy j
    have := hv j
    have : 0 < -(2 * a ^ α * b ^ α *
        (α * (a + b) * (a ^ α / b - b ^ α / a) + 2 * (a ^ α - b ^ α))) := by linarith
    positivity
  unfold alphaPsi
  linarith

/-- For `-1 < α < 0`, the gradient numerator is positive when there are other points. -/
theorem alphaNum_pos {ι : Type*} (hα₁ : -1 < α) (hα : α < 0) (hb : 0 < b) (hab : b < a)
    {y : ι → ℝ} (hy : ∀ k, 0 < y k) {O : Finset ι} (hO : O.Nonempty) :
    0 < alphaNum α a b (a ^ α) (b ^ α) (∑ k ∈ O, alphaMono (y k) (y k ^ α)) := by
  have ha := hb.trans hab
  rw [alphaNum_sum_eq_sum_alphaPsi ha.ne' hb.ne']
  exact sum_pos (fun j hj ↦ alphaPsi_pos hα₁ hα hb hab hy hj) hO

/-- For `-1 < α < 0`, the gradient numerator is `≥ 0`. -/
theorem alphaNum_nonneg {ι : Type*} (hα₁ : -1 < α) (hα : α < 0) (hb : 0 < b) (hab : b < a)
    {y : ι → ℝ} (hy : ∀ k, 0 < y k) (O : Finset ι) :
    0 ≤ alphaNum α a b (a ^ α) (b ^ α) (∑ k ∈ O, alphaMono (y k) (y k ^ α)) := by
  have ha := hb.trans hab
  rw [alphaNum_sum_eq_sum_alphaPsi ha.ne' hb.ne']
  exact sum_nonneg fun j hj ↦ (alphaPsi_pos hα₁ hα hb hab hy hj).le

end AlphaCurvature
