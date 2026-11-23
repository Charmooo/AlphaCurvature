/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The derivative of the exponential and the Daleckii–Krein formula

In a complete normed algebra over `ℝ` or `ℂ` the exponential has derivative
  `D exp(x)[h] = ∑ₙ (1/n!) ∑_{i<n} x^{n−1−i} h x^i`
at every point (`AlphaCurvature.hasFDerivAt_exp'`, with `AlphaCurvature.expDeriv`). Mathlib's
`hasFDerivAt_exp` covers commutative algebras only. The proof differentiates the exponential
series term by term.

At a diagonal matrix `diag(a)` the derivative acts entrywise by the first divided difference of
`exp`: `(D exp(diag a)[C])ᵢⱼ = e^{[1]}(aᵢ, aⱼ) Cᵢⱼ` (`Matrix.expDeriv_diagonal_apply`), where
`e^{[1]}(x, y)` is `(e^x − e^y)/(x − y)` for `x ≠ y` (`Matrix.expDividedDiff_of_ne`) and `e^x` for
`x = y` (`Matrix.expDividedDiff_self`).

This file is the first-order part of `TimelibBeta/Mathlib/Analysis/Normed/Algebra/ExponentialDeriv`
and `TimelibBeta/Mathlib/Analysis/Matrix/DaleckiiKrein` in the Time Library project, by the same
author.

## Main definitions

* `AlphaCurvature.expDeriv 𝕂 x`: the derivative of the exponential at `x`.
* `AlphaCurvature.Matrix.expDividedDiff x y`: the first divided difference of `exp`.

## Main statements

* `AlphaCurvature.hasFDerivAt_exp'`: the exponential has derivative `expDeriv 𝕂 x` at `x`.
* `AlphaCurvature.Matrix.expDeriv_diagonal_apply`: the Daleckii–Krein formula at a diagonal.
* `AlphaCurvature.Matrix.expDividedDiff_of_ne`, `AlphaCurvature.Matrix.expDividedDiff_self`:
  its closed forms.

## References

* Ju. L. Daleckiĭ and S. G. Kreĭn, *Integration and differentiation of functions of Hermitian
  operators and applications to the theory of perturbations* (1965).
-/

open Finset Metric Nat NormedSpace
open scoped RightActions

namespace AlphaCurvature

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

variable (𝕂) in
/-- The derivative of `y ↦ yⁿ` at `x`: `h ↦ ∑_{i<n} x^{n−1−i} h x^i`. -/
noncomputable def powDeriv (x : 𝔸) (n : ℕ) : 𝔸 →L[𝕂] 𝔸 :=
  ∑ i ∈ range n, x ^ (n.pred - i) •> ContinuousLinearMap.id 𝕂 𝔸 <• x ^ i

omit [CompleteSpace 𝔸] in
theorem powDeriv_apply (x : 𝔸) (n : ℕ) (h : 𝔸) :
    powDeriv 𝕂 x n h = ∑ i ∈ range n, x ^ (n.pred - i) * h * x ^ i := by
  simp [powDeriv, mul_assoc]

omit [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸] in
private theorem norm_pow_le_one_add (y : 𝔸) (k : ℕ) : ‖y ^ k‖ ≤ (‖(1 : 𝔸)‖ + 1) * ‖y‖ ^ k := by
  rcases k with _ | k
  · simp
  · calc ‖y ^ (k + 1)‖ ≤ ‖y‖ ^ (k + 1) := norm_pow_le' y k.succ_pos
      _ ≤ (‖(1 : 𝔸)‖ + 1) * ‖y‖ ^ (k + 1) :=
        le_mul_of_one_le_left (by positivity) (by linarith [norm_nonneg (1 : 𝔸)])

omit [CompleteSpace 𝔸] in
theorem norm_powDeriv_le (x : 𝔸) (n : ℕ) :
    ‖powDeriv 𝕂 x n‖ ≤ (‖(1 : 𝔸)‖ + 1) ^ 2 * (n * ‖x‖ ^ n.pred) := by
  set K := ‖(1 : 𝔸)‖ + 1
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [powDeriv_apply]
  calc ‖∑ i ∈ range n, x ^ (n.pred - i) * h * x ^ i‖
      ≤ ∑ i ∈ range n, ‖x ^ (n.pred - i) * h * x ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range n, K ^ 2 * ‖x‖ ^ n.pred * ‖h‖ := by
        refine sum_le_sum fun i hi => ?_
        have hi' : i ≤ n.pred := by
          have := mem_range.mp hi
          rw [Nat.pred_eq_sub_one]
          omega
        calc ‖x ^ (n.pred - i) * h * x ^ i‖
            ≤ K * ‖x‖ ^ (n.pred - i) * ‖h‖ * (K * ‖x‖ ^ i) := by
              refine (norm_mul_le _ _).trans ?_
              refine mul_le_mul ((norm_mul_le _ _).trans ?_) (norm_pow_le_one_add _ _)
                (norm_nonneg _) (by positivity)
              exact mul_le_mul_of_nonneg_right (norm_pow_le_one_add _ _) (norm_nonneg _)
          _ = K ^ 2 * ‖x‖ ^ n.pred * ‖h‖ := by
              rw [← Nat.sub_add_cancel hi', pow_add]
              simp only [Nat.add_sub_cancel]
              ring
    _ = K ^ 2 * (n * ‖x‖ ^ n.pred) * ‖h‖ := by
        rw [sum_const, card_range, nsmul_eq_mul]
        ring

omit [CompleteSpace 𝔸] in
theorem hasFDerivAt_pow_powDeriv (x : 𝔸) (n : ℕ) :
    HasFDerivAt (fun y : 𝔸 => y ^ n) (powDeriv 𝕂 x n) x :=
  hasFDerivAt_pow' n

variable (𝕂) in
/-- The derivative of the exponential at `x`: `∑ₙ (1/n!) powDeriv x n`. -/
noncomputable def expDeriv (x : 𝔸) : 𝔸 →L[𝕂] 𝔸 :=
  ∑' n : ℕ, (n !⁻¹ : 𝕂) • powDeriv 𝕂 x n

private theorem summable_bound (K R : ℝ) :
    Summable fun n : ℕ => (n ! : ℝ)⁻¹ * (K * (n * R ^ n.pred)) := by
  have h : Summable fun n : ℕ => (n ! : ℝ)⁻¹ * (n * R ^ n.pred) := by
    refine (summable_nat_add_iff 1).mp ?_
    refine (Real.summable_pow_div_factorial R).congr fun n => ?_
    simp only [Nat.pred_succ, Nat.cast_add, Nat.cast_one, Nat.factorial_succ, Nat.cast_mul]
    field_simp
  exact (h.mul_left K).congr fun n => by ring

omit [CompleteSpace 𝔸] in
private theorem norm_term_le {x : 𝔸} {R : ℝ} (hx : ‖x‖ ≤ R) (n : ℕ) :
    ‖(n !⁻¹ : 𝕂) • powDeriv 𝕂 x n‖ ≤
      (n ! : ℝ)⁻¹ * ((‖(1 : 𝔸)‖ + 1) ^ 2 * (n * R ^ n.pred)) := by
  rw [norm_smul, norm_inv, RCLike.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_powDeriv_le x n).trans ?_) (by positivity)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hx _) (by positivity)) (by positivity)

private theorem summable_powDeriv (x : 𝔸) :
    Summable fun n : ℕ => (n !⁻¹ : 𝕂) • powDeriv 𝕂 x n :=
  Summable.of_norm_bounded (summable_bound _ ‖x‖) (norm_term_le le_rfl)

/-- **The derivative of the exponential** in a complete normed algebra, at every point. -/
theorem hasFDerivAt_exp' (x : 𝔸) : HasFDerivAt (exp : 𝔸 → 𝔸) (expDeriv 𝕂 x) x := by
  let : NormedSpace ℝ 𝔸 := NormedSpace.restrictScalars ℝ 𝕂 𝔸
  rw [exp_eq_tsum 𝕂]
  set R := ‖x‖ + 1
  have hs : x ∈ ball (0 : 𝔸) R := by simp [R]
  exact hasFDerivAt_tsum_of_isPreconnected (f := fun n y => (n !⁻¹ : 𝕂) • y ^ n)
    (f' := fun n y => (n !⁻¹ : 𝕂) • powDeriv 𝕂 y n) (summable_bound _ R) isOpen_ball
    (convex_ball _ _).isPreconnected
    (fun n y _ => (hasFDerivAt_pow_powDeriv (𝕂 := 𝕂) y n).const_smul (n !⁻¹ : 𝕂))
    (fun n y hy => norm_term_le (mem_ball_zero_iff.mp hy).le n) hs
    (expSeries_summable' x) hs

/-- The series of `expDeriv x h`. -/
theorem hasSum_expDeriv (x h : 𝔸) :
    HasSum (fun n : ℕ => (n !⁻¹ : 𝕂) • ∑ i ∈ range n, x ^ (n.pred - i) * h * x ^ i)
      (expDeriv 𝕂 x h) := by
  have hsum := (summable_powDeriv (𝕂 := 𝕂) x).hasSum.mapL (ContinuousLinearMap.apply 𝕂 𝔸 h)
  simp only [ContinuousLinearMap.apply_apply, smul_apply, powDeriv_apply] at hsum
  exact hsum

theorem expDeriv_apply (x h : 𝔸) :
    expDeriv 𝕂 x h = ∑' n : ℕ, (n !⁻¹ : 𝕂) • ∑ i ∈ range n, x ^ (n.pred - i) * h * x ^ i :=
  (hasSum_expDeriv x h).tsum_eq.symm

/-! ### The Daleckii–Krein formula at a diagonal matrix -/

namespace Matrix

open _root_.Matrix
open scoped Matrix.Norms.L2Operator

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ### Shifting a factorial series -/

/-- If `∑ₘ g m / m! = S`, then `∑ₙ n g(n − 1) / n! = S`. -/
theorem hasSum_factorial_mul_pred {g : ℕ → ℂ} {S : ℂ} (h : HasSum (fun m => (m !⁻¹ : ℂ) * g m) S) :
    HasSum (fun n => (n !⁻¹ : ℂ) * (n * g n.pred)) S := by
  refine (hasSum_nat_add_iff' 1).mp ?_
  simp only [range_one, sum_singleton, Nat.cast_zero, zero_mul, mul_zero, sub_zero]
  refine h.congr_fun fun n => ?_
  simp only [Nat.pred_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp

/-! ### Entries at a diagonal matrix -/

theorem diagonal_pow_mul_mul_diagonal_pow_apply (a : d → ℂ) (C : Matrix d d ℂ) (k m : ℕ)
    (i j : d) : (diagonal a ^ k * C * diagonal a ^ m) i j = a i ^ k * C i j * a j ^ m := by
  simp [diagonal_pow, diagonal_mul, mul_diagonal]

omit [DecidableEq d] in
private noncomputable def entryCLM (i j : d) : Matrix d d ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (entryLinearMap ℂ ℂ i j)

omit [DecidableEq d] in
private theorem entryCLM_apply (i j : d) (M : Matrix d d ℂ) : entryCLM i j M = M i j :=
  rfl

private theorem hasSum_entry (a : d → ℂ) (C : Matrix d d ℂ) (i j : d) :
    HasSum (fun n : ℕ => (n !⁻¹ : ℂ) *
      ∑ k ∈ range n, a i ^ (n.pred - k) * a j ^ k * C i j)
      (expDeriv ℂ (diagonal a) C i j) := by
  have h := (hasSum_expDeriv (𝕂 := ℂ) (diagonal a) C).mapL (entryCLM i j)
  simp only [entryCLM_apply, _root_.Matrix.smul_apply, smul_eq_mul, _root_.Matrix.sum_apply,
    diagonal_pow_mul_mul_diagonal_pow_apply] at h
  refine h.congr_fun fun n => ?_
  congr 1
  exact sum_congr rfl fun k _ => by ring

/-- The **first divided difference of the exponential**:
`e^{[1]}(x, y) = ∑ₙ (1/n!) ∑_{i<n} x^{n−1−i} yⁱ`. -/
noncomputable def expDividedDiff (x y : ℂ) : ℂ :=
  ∑' n : ℕ, (n !⁻¹ : ℂ) * ∑ i ∈ range n, x ^ (n.pred - i) * y ^ i

theorem hasSum_expDividedDiff (x y : ℂ) :
    HasSum (fun n : ℕ => (n !⁻¹ : ℂ) * ∑ i ∈ range n, x ^ (n.pred - i) * y ^ i)
      (expDividedDiff x y) := by
  refine Summable.hasSum ?_
  have h := (hasSum_entry (d := Fin 2) ![x, y] (Matrix.single 0 1 1) 0 1).summable
  simpa using h

/-- **The Daleckii–Krein formula for the exponential**: at `diag(a)`,
`(D exp(diag a)[C])ᵢⱼ = e^{[1]}(aᵢ, aⱼ) Cᵢⱼ`. -/
theorem expDeriv_diagonal_apply (a : d → ℂ) (C : Matrix d d ℂ) (i j : d) :
    expDeriv ℂ (diagonal a) C i j = expDividedDiff (a i) (a j) * C i j := by
  refine (hasSum_entry a C i j).unique ?_
  refine ((hasSum_expDividedDiff (a i) (a j)).mul_right (C i j)).congr_fun fun n => ?_
  rw [mul_assoc, sum_mul]

/-- `e^{[1]}(x, y) (x − y) = e^x − e^y`. -/
theorem expDividedDiff_mul_sub (x y : ℂ) : expDividedDiff x y * (x - y) = exp x - exp y := by
  refine ((hasSum_expDividedDiff x y).mul_right (x - y)).unique ?_
  have h := (exp_series_hasSum_exp' (𝕂 := ℂ) x).sub (exp_series_hasSum_exp' (𝕂 := ℂ) y)
  refine h.congr_fun fun n => ?_
  rw [mul_assoc, smul_eq_mul, smul_eq_mul, ← mul_sub]
  congr 1
  have e : ∑ i ∈ range n, x ^ (n.pred - i) * y ^ i =
      ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun i hi => ?_
    have := mem_range.mp hi
    rw [Nat.pred_eq_sub_one]
    congr 2
    omega
  rw [e, geom_sum₂_mul]

theorem expDividedDiff_of_ne {x y : ℂ} (h : x ≠ y) :
    expDividedDiff x y = (exp x - exp y) / (x - y) :=
  eq_div_of_mul_eq (sub_ne_zero.mpr h) (expDividedDiff_mul_sub x y)

theorem expDividedDiff_self (x : ℂ) : expDividedDiff x x = exp x := by
  refine (hasSum_expDividedDiff x x).unique ?_
  have h := hasSum_factorial_mul_pred (g := fun m => x ^ m)
    ((exp_series_hasSum_exp' (𝕂 := ℂ) x).congr_fun fun m => smul_eq_mul _ _)
  refine h.congr_fun fun n => ?_
  congr 1
  have hs : ∑ i ∈ range n, x ^ (n.pred - i) * x ^ i = n * x ^ n.pred := by
    rw [sum_congr rfl fun i hi => (show x ^ (n.pred - i) * x ^ i = x ^ n.pred by
      rw [← pow_add, Nat.sub_add_cancel
        (by have := mem_range.mp hi; rw [Nat.pred_eq_sub_one]; omega)]),
      sum_const, card_range, nsmul_eq_mul]
  rw [hs]

/-- `e^{[1]}` is symmetric. -/
theorem expDividedDiff_comm (x y : ℂ) : expDividedDiff x y = expDividedDiff y x := by
  rcases eq_or_ne x y with rfl | h
  · rfl
  · rw [expDividedDiff_of_ne h, expDividedDiff_of_ne h.symm, ← neg_div_neg_eq, neg_sub, neg_sub]

end Matrix

end AlphaCurvature
