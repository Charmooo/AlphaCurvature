/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import AlphaCurvature.Quantum.Excess

/-!
# The sign of the gradient difference of the quantum excess

Let `a = λᵢ > b = λⱼ`, write `∂ = ∂ᵢ - ∂ⱼ`, and let `y` range over the other eigenvalues. With the
unordered sums `M`, `Q`, the gradient difference is `W³ ∂E = Z` (`exGradF_eq`):

  `Z = 4M H₁ + 4cW T̂ ∂M + W²(4M ∂M - 2∂Q) - 2W ∂W (2M² - Q)`,  `H₁ = cX + W² ∂M`.

Only the pairs containing `a` or `b` move, so `∂M = κ + ∑_y φ(y)` with `κ = K₁(a, b) - K₁(b, a)`
and `φ(y) = K₁(a, y) - K₁(b, y)` (`offGrad_sub_offGrad`), and similarly for `∂Q`.

* **`0 < α ≤ 1`** (`excessGrad_lt_excessGrad`): every term of `Z` is `≤ 0` by the kernel facts
  `K₁ ≥ 0`, `K₁₁ ≤ 0` and `κ ≤ 0`, and `H₁ < 0`: in the other points,
  `H₁ ≤ H₀ + ∑_y y¹⁺ᵅ[c ∂W (yᵅ - π) - c ∂P(1+2α) + y¹⁺ᵅ φ(y)]` with
  `H₀ = c[-w ∂P(1+2α) + ∂W (2ρ - wπ)] < 0`, and each bracket is `≤ 0`: trivially for `y ≤ a`,
  and by `kerG_nonpos` (the lemma L1) for `y > a`.
* **`-1 < α < 0`** (`excessGrad_lt_excessGrad_of_neg`): `Z = 4cM X + 4cW T̂ ∂M + W²(8M ∂M - 2∂Q) -
  2W ∂W (2M² - Q)` with `X = W(W ∂P(α) - ∂P(1+2α)) - ∂W (W P(α) - 2P(1+2α)) > 0`, and the other
  terms `≥ 0` by the mirror facts and log-convexity of the kernel (`kerD_mul_kerInt_le`).
-/

open Finset

namespace AlphaCurvature.Quantum

variable {d : Type*} [Fintype d] [DecidableEq d] {α : ℝ}

/-! ### Splitting off the moving pair -/

section Split

variable {i j : d}

theorem mem_others {k : d} : k ∈ others i j ↔ k ≠ j ∧ k ≠ i := by
  simp [others, and_comm]

theorem sum_ite_eq_add_sum_others (hij : i ≠ j) (f : d → ℝ) :
    ∑ k, (if i = k then 0 else f k) = f j + ∑ k ∈ others i j, f k := by
  rw [sum_univ_eq_add_sum_others hij]
  simp only [↓reduceIte, hij, zero_add]
  congr 1
  exact sum_congr rfl fun k hk ↦ by simp [Ne.symm (mem_others.1 hk).2]

theorem sum_ite_eq_add_sum_others' (hij : i ≠ j) (f : d → ℝ) :
    ∑ k, (if j = k then 0 else f k) = f i + ∑ k ∈ others i j, f k := by
  rw [sum_univ_eq_add_sum_others hij]
  simp only [↓reduceIte, Ne.symm hij, add_zero]
  congr 1
  exact sum_congr rfl fun k hk ↦ by simp [Ne.symm (mem_others.1 hk).1]

variable {z : d → ℝ}

/-- `∂M = κ + ∑_y φ(y)` in the unordered sum. -/
theorem offGrad_sub_offGrad (hij : i ≠ j) :
    (offGrad α z i - offGrad α z j) / 2 = (kerD α (z i) (z j) - kerD α (z j) (z i)) +
      ∑ k ∈ others i j, (kerD α (z i) (z k) - kerD α (z j) (z k)) := by
  rw [offGrad, offGrad, sum_ite_eq_add_sum_others hij, sum_ite_eq_add_sum_others' hij,
    sum_sub_distrib]
  ring

/-- `∂Q = 2 Kₐᵦ κ + 2 ∑_y (K(a, y) K₁(a, y) - K(b, y) K₁(b, y))` in the unordered sum. -/
theorem offGradSq_sub_offGradSq (hij : i ≠ j) :
    (offGradSq α z i - offGradSq α z j) / 2 =
      2 * curvKernel α (z i) (z j) * (kerD α (z i) (z j) - kerD α (z j) (z i)) +
        2 * ∑ k ∈ others i j, (curvKernel α (z i) (z k) * kerD α (z i) (z k) -
          curvKernel α (z j) (z k) * kerD α (z j) (z k)) := by
  rw [offGradSq, offGradSq, sum_ite_eq_add_sum_others hij, sum_ite_eq_add_sum_others' hij,
    sum_sub_distrib, curvKernel_comm (z j) (z i)]
  ring

/-- The gradient depends on the index only through the entry. -/
theorem excessGrad_eq_excessGrad (h : z i = z j) : excessGrad α z i = excessGrad α z j := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  have hM : offGrad α z i = offGrad α z j := by
    have := offGrad_sub_offGrad (α := α) (z := z) hij
    simp only [h, sub_self, zero_add, sum_const_zero] at this
    linarith
  have hQ : offGradSq α z i = offGradSq α z j := by
    have := offGradSq_sub_offGradSq (α := α) (z := z) hij
    simp only [h, sub_self, mul_zero, zero_add, sum_const_zero] at this
    linarith
  simp only [excessGrad, hM, hQ, h]

end Split

/-! ### Bounds on the global sums -/

/-- A product of sums of nonnegative terms dominates the sum of the diagonal products. -/
theorem sum_mul_le_sum_mul_sum {ι : Type*} {O : Finset ι} {f g : ι → ℝ} (hf : ∀ k ∈ O, 0 ≤ f k)
    (hg : ∀ k ∈ O, 0 ≤ g k) : ∑ k ∈ O, f k * g k ≤ (∑ k ∈ O, f k) * ∑ k ∈ O, g k := by
  rw [sum_mul]
  exact sum_le_sum fun k hk ↦ mul_le_mul_of_nonneg_left (single_le_sum hg hk) (hf k hk)

section Global

variable {z : d → ℝ} (hα₁ : -1 < α) (hα : α ≤ 1) (hz : ∀ i, 0 < z i)
include hα₁ hα hz

omit [Fintype d] [DecidableEq d] in
theorem curvKernel_pos' (k l : d) : 0 < curvKernel α (z k) (z l) := by
  rw [curvKernel_eq_kerInt hα₁ hα (hz k) (hz l)]
  exact kerInt_pos hα₁ (hz k) (hz l)

theorem offSum_row_nonneg (k : d) :
    0 ≤ ∑ l, (if k = l then 0 else curvKernel α (z k) (z l)) :=
  sum_nonneg fun l _ ↦ by split_ifs <;> [exact le_rfl; exact (curvKernel_pos' hα₁ hα hz k l).le]

/-- `M ≥ Kₐᵦ + K(a, y) + K(b, y)` for every other point `y`. -/
theorem offSum_ge {i j y : d} (hij : i ≠ j) (hy : y ∈ others i j) :
    2 * (curvKernel α (z i) (z j) + curvKernel α (z i) (z y) + curvKernel α (z j) (z y)) ≤
      offSum α z := by
  have hO := fun k ↦ offSum_row_nonneg hα₁ hα hz k
  have hp := fun k l ↦ (curvKernel_pos' hα₁ hα hz k l).le
  rw [offSum, sum_univ_eq_add_sum_others hij, sum_ite_eq_add_sum_others hij,
    sum_ite_eq_add_sum_others' hij]
  have h1 := single_le_sum (f := fun k ↦ curvKernel α (z i) (z k)) (fun k _ ↦ hp i k) hy
  have h2 := single_le_sum (f := fun k ↦ curvKernel α (z j) (z k)) (fun k _ ↦ hp j k) hy
  have h3 := single_le_sum (f := fun k ↦ ∑ l, (if k = l then 0 else curvKernel α (z k) (z l)))
    (fun k _ ↦ hO k) hy
  have hyi := (mem_others.1 hy).2
  have hyj := (mem_others.1 hy).1
  have h4 : curvKernel α (z y) (z i) + curvKernel α (z y) (z j) ≤
      ∑ l, (if y = l then 0 else curvKernel α (z y) (z l)) := by
    rw [sum_univ_eq_add_sum_others hij]
    simp only [hyi, hyj, ↓reduceIte]
    have : 0 ≤ ∑ l ∈ others i j, (if y = l then 0 else curvKernel α (z y) (z l)) :=
      sum_nonneg fun l _ ↦ by split_ifs <;> [exact le_rfl; exact hp y l]
    linarith
  rw [curvKernel_comm (z y) (z i), curvKernel_comm (z y) (z j)] at h4
  rw [curvKernel_comm (z j) (z i)]
  linarith

/-- `M ≥ Kₐᵦ`. -/
theorem offSum_ge_pair {i j : d} (hij : i ≠ j) : 2 * curvKernel α (z i) (z j) ≤ offSum α z := by
  have hO := fun k ↦ offSum_row_nonneg hα₁ hα hz k
  have hp := fun k l ↦ (curvKernel_pos' hα₁ hα hz k l).le
  rw [offSum, sum_univ_eq_add_sum_others hij, sum_ite_eq_add_sum_others hij,
    sum_ite_eq_add_sum_others' hij, curvKernel_comm (z j) (z i)]
  have h1 : 0 ≤ ∑ k ∈ others i j, curvKernel α (z i) (z k) := sum_nonneg fun k _ ↦ hp i k
  have h2 : 0 ≤ ∑ k ∈ others i j, curvKernel α (z j) (z k) := sum_nonneg fun k _ ↦ hp j k
  have h3 : 0 ≤ ∑ k ∈ others i j, ∑ l, (if k = l then 0 else curvKernel α (z k) (z l)) :=
    sum_nonneg fun k _ ↦ hO k
  linarith

/-- `Q ≤ M²` in the ordered sums, so `2M'² - Q' ≥ 0` in the unordered ones. -/
theorem offSumSq_le : offSumSq α z ≤ offSum α z ^ 2 := by
  have hp := fun k l ↦ (curvKernel_pos' hα₁ hα hz k l).le
  have h1 : ∀ k, ∑ l, (if k = l then (0 : ℝ) else curvKernel α (z k) (z l) ^ 2) ≤
      (∑ l, if k = l then 0 else curvKernel α (z k) (z l)) ^ 2 := fun k ↦ by
    have := sum_sq_le_sq_sum (O := univ) (f := fun l ↦ if k = l then 0 else
      curvKernel α (z k) (z l)) fun l _ ↦ by split_ifs <;> [exact le_rfl; exact hp k l]
    refine le_trans (le_of_eq (sum_congr rfl fun l _ ↦ ?_)) this
    split_ifs <;> simp
  have h2 := sum_sq_le_sq_sum (O := univ) (f := fun k ↦ ∑ l, if k = l then 0 else
    curvKernel α (z k) (z l)) fun k _ ↦ offSum_row_nonneg hα₁ hα hz k
  exact (sum_le_sum fun k _ ↦ h1 k).trans h2

omit [DecidableEq d] hα₁ hα in
/-- `T̂ = P(α) W - P(1+2α) ≥ 0`. -/
theorem powSum_le_mul : powSum z (1 + 2 * α) ≤ powSum z α * powSum z (1 + α) := by
  have h := sum_mul_le_sum_mul_sum (O := univ) (f := fun k ↦ z k ^ α)
    (g := fun k ↦ z k ^ (1 + α)) (fun k _ ↦ (Real.rpow_pos_of_pos (hz k) _).le)
    (fun k _ ↦ (Real.rpow_pos_of_pos (hz k) _).le)
  refine le_trans (le_of_eq (sum_congr rfl fun k _ ↦ ?_)) h
  rw [← Real.rpow_add (hz k)]
  ring_nf

end Global

/-! ### Algebra of the final step -/

section Algebra

/-- `Z < 0` from the signs of its four terms (`0 < α ≤ 1`). -/
theorem Z_neg {c W P R M Q dM dQ dW H : ℝ} (hc : 0 ≤ c) (hW : 0 < W) (hM : 0 < M)
    (hT : 0 ≤ P * W - R) (hdM : dM ≤ 0) (hMQ : 4 * M * dM - 2 * dQ ≤ 0) (hdW : 0 ≤ dW)
    (hQ : 0 ≤ 2 * M ^ 2 - Q) (hH : H < 0) :
    4 * M * H + 4 * c * W * (P * W - R) * dM + W ^ 2 * (4 * M * dM - 2 * dQ) -
      2 * W * dW * (2 * M ^ 2 - Q) < 0 := by
  have h1 : 4 * M * H < 0 := by nlinarith
  have h2 : 4 * c * W * (P * W - R) * dM ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by positivity) hT) hdM
  have h3 : W ^ 2 * (4 * M * dM - 2 * dQ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hMQ
  have h4 : 0 ≤ 2 * W * dW * (2 * M ^ 2 - Q) := mul_nonneg (mul_nonneg (by positivity) hdW) hQ
  linarith

/-- `0 < Z` from the signs of its four terms (`-1 < α < 0`). -/
theorem Z_pos {c W P R M Q dM dQ dW X : ℝ} (hc : 0 < c) (hW : 0 < W) (hM : 0 < M)
    (hT : 0 ≤ P * W - R) (hdM : 0 ≤ dM) (hMQ : 0 ≤ 8 * M * dM - 2 * dQ) (hdW : dW ≤ 0)
    (hQ : 0 ≤ 2 * M ^ 2 - Q) (hX : 0 < X) :
    0 < 4 * M * (c * X + W ^ 2 * dM) + 4 * c * W * (P * W - R) * dM +
      W ^ 2 * (4 * M * dM - 2 * dQ) - 2 * W * dW * (2 * M ^ 2 - Q) := by
  have h1 : 0 < 4 * c * M * X := by positivity
  have h2 : 0 ≤ 4 * c * W * (P * W - R) * dM := mul_nonneg (mul_nonneg (by positivity) hT) hdM
  have h3 : 0 ≤ W ^ 2 * (8 * M * dM - 2 * dQ) := mul_nonneg (by positivity) hMQ
  have h4 : 2 * W * dW * (2 * M ^ 2 - Q) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith) hQ
  nlinarith

/-- **`H₀ < 0`**: the two-point part of `H₁`, with `A = aᵅ > B = bᵅ`. -/
theorem H0_neg {c α a b A B : ℝ} (hc : 0 < c) (hα : 0 < α) (hb : 0 < b) (hab : b < a)
    (hB : 0 < B) (hAB : B < A) :
    -(c * (a * A + b * B) * ((1 + 2 * α) * (A ^ 2 - B ^ 2))) +
      c * ((1 + α) * (A - B)) * (2 * (a * A ^ 2 + b * B ^ 2) - (a * A + b * B) * (A + B)) < 0 := by
  have e : 2 * (a * A ^ 2 + b * B ^ 2) - (a * A + b * B) * (A + B) = (a * A - b * B) * (A - B) := by
    ring
  rw [e]
  have h1 : 0 < A - B := by linarith
  have h2 : 0 < a * A - b * B := by nlinarith
  have h3 : (A - B) * (a * A - b * B) < (A + B) * (a * A + b * B) := by
    have e2 : (A + B) * (a * A + b * B) - (A - B) * (a * A - b * B) = 2 * (A * b * B + B * a * A) :=
      by ring
    have ha : 0 < a := by linarith
    have hA : 0 < A := by linarith
    have : 0 < 2 * (A * b * B + B * a * A) := by positivity
    linarith
  have h4 : (1 + α) * ((A - B) * (a * A - b * B)) < (1 + 2 * α) * ((A + B) * (a * A + b * B)) := by
    have : 0 ≤ (A - B) * (a * A - b * B) := by positivity
    nlinarith
  have : c * (A - B) * ((1 + α) * ((A - B) * (a * A - b * B)) -
      (1 + 2 * α) * ((A + B) * (a * A + b * B))) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (by linarith)
  nlinarith

end Algebra

/-! ### `0 < α ≤ 1` -/

section Positive

variable {z : d → ℝ} {i j : d}

theorem rpow_one_add_two_mul_sub_one {x : ℝ} (hx : 0 < x) :
    x ^ (1 + 2 * α - 1) = (x ^ α) ^ 2 := by
  rw [show 1 + 2 * α - 1 = α * 2 by ring, Real.rpow_mul hx.le]
  norm_cast

theorem rpow_one_add_sub_one {x : ℝ} : x ^ (1 + α - 1) = x ^ α := by ring_nf

theorem rpow_one_add_eq {x : ℝ} (hx : 0 < x) : x ^ (1 + α) = x * x ^ α := by
  rw [Real.rpow_add hx, Real.rpow_one]

theorem rpow_one_add_two_mul_eq {x : ℝ} (hx : 0 < x) : x ^ (1 + 2 * α) = x * (x ^ α) ^ 2 := by
  rw [Real.rpow_add hx, Real.rpow_one, ← rpow_one_add_two_mul_sub_one hx]
  ring_nf

/-- The algebra of `H₁ < 0`: in the sums over the other points, `H₁` is `H₀ + ∑_y ψ(y)` plus
terms `≤ 0`. -/
theorem H1_neg_aux {c α a b A B W P R S Pi' Ry Φ Ψ2 κ dP dM : ℝ}
    (hW : W = a * A + b * B + S) (hP : P = A + B + Pi') (hR : R = a * A ^ 2 + b * B ^ 2 + Ry)
    (hdM : dM = κ + Φ) (hc : 0 ≤ c) (hdP : dP ≤ 0) (hκ : κ ≤ 0)
    (hdW : 0 ≤ (1 + α) * A - (1 + α) * B) (ha : 0 ≤ a * A + b * B) (hPi : 0 ≤ Pi')
    (i3 : W ^ 2 * Φ ≤ Ψ2) (i5 : Ry ≤ S * Pi')
    (i6 : -(c * ((1 + 2 * α) * A ^ 2 - (1 + 2 * α) * B ^ 2)) * S +
      c * ((1 + α) * A - (1 + α) * B) * Ry - c * ((1 + α) * A - (1 + α) * B) * (A + B) * S +
        Ψ2 ≤ 0)
    (i7 : -(c * (a * A + b * B) * ((1 + 2 * α) * (A ^ 2 - B ^ 2))) +
      c * ((1 + α) * (A - B)) * (2 * (a * A ^ 2 + b * B ^ 2) - (a * A + b * B) * (A + B)) < 0) :
    c * (W ^ 2 * dP - W * ((1 + 2 * α) * A ^ 2 - (1 + 2 * α) * B ^ 2) +
      ((1 + α) * A - (1 + α) * B) * (2 * R - W * P)) + W ^ 2 * dM < 0 := by
  have i1 : c * (W ^ 2 * dP) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc
    (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hdP)
  have i2 : W ^ 2 * κ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hκ
  have i4 : 0 ≤ c * ((1 + α) * A - (1 + α) * B) * (a * A + b * B) * Pi' :=
    mul_nonneg (mul_nonneg (mul_nonneg hc hdW) ha) hPi
  have i5' : c * ((1 + α) * A - (1 + α) * B) * (Ry - S * Pi') ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc hdW) (by linarith)
  have e : c * (W ^ 2 * dP - W * ((1 + 2 * α) * A ^ 2 - (1 + 2 * α) * B ^ 2) +
      ((1 + α) * A - (1 + α) * B) * (2 * R - W * P)) + W ^ 2 * dM =
      (-(c * (a * A + b * B) * ((1 + 2 * α) * (A ^ 2 - B ^ 2))) +
        c * ((1 + α) * (A - B)) * (2 * (a * A ^ 2 + b * B ^ 2) - (a * A + b * B) * (A + B))) +
      (-(c * ((1 + 2 * α) * A ^ 2 - (1 + 2 * α) * B ^ 2)) * S +
        c * ((1 + α) * A - (1 + α) * B) * Ry -
        c * ((1 + α) * A - (1 + α) * B) * (A + B) * S + Ψ2) +
      c * (W ^ 2 * dP) + W ^ 2 * κ + (W ^ 2 * Φ - Ψ2) -
      c * ((1 + α) * A - (1 + α) * B) * (a * A + b * B) * Pi' +
      c * ((1 + α) * A - (1 + α) * B) * (Ry - S * Pi') := by
    rw [hdM, hP, hR, hW]
    ring
  rw [e]
  linarith

omit [Fintype d] [DecidableEq d] in
theorem ne_of_lt_apply (h : z j < z i) : i ≠ j := fun e ↦ by rw [e] at h; exact lt_irrefl _ h

variable (hα0 : 0 < α) (hα1 : α ≤ 1) (hz : ∀ k, 0 < z k) (h : z j < z i)
include hα0 hα1 hz h

/-- `∂M ≤ 0` for `0 ≤ α ≤ 1`. -/
theorem offGrad_sub_nonpos : (offGrad α z i - offGrad α z j) / 2 ≤ 0 := by
  rw [offGrad_sub_offGrad (ne_of_lt_apply h)]
  have h1 := kerD_le_kerD_swap hα0.le hα1 (hz j) h.le
  have h2 : ∑ k ∈ others i j, (kerD α (z i) (z k) - kerD α (z j) (z k)) ≤ 0 :=
    sum_nonpos fun k _ ↦ by have := kerD_le_kerD hα0.le hα1 (hz j) h.le (hz k); linarith
  linarith

/-- `4M ∂M - 2 ∂Q ≤ 0` for `0 ≤ α ≤ 1`. -/
theorem offGrad_bracket_nonpos :
    4 * (offSum α z / 2) * ((offGrad α z i - offGrad α z j) / 2) -
      2 * ((offGradSq α z i - offGradSq α z j) / 2) ≤ 0 := by
  have hij := ne_of_lt_apply h
  have hα₁ : -1 < α := by linarith
  set M := offSum α z / 2 with hMdef
  set O := others i j
  have hK : ∀ k l, curvKernel α (z k) (z l) = kerInt α (z k) (z l) := fun k l ↦
    curvKernel_eq_kerInt hα₁ hα1 (hz k) (hz l)
  have e1 : ∑ k ∈ O, ((4 * M - 4 * curvKernel α (z i) (z k)) * kerD α (z i) (z k) -
      (4 * M - 4 * curvKernel α (z j) (z k)) * kerD α (z j) (z k)) =
      4 * M * ∑ k ∈ O, (kerD α (z i) (z k) - kerD α (z j) (z k)) -
        2 * (2 * ∑ k ∈ O, (curvKernel α (z i) (z k) * kerD α (z i) (z k) -
          curvKernel α (z j) (z k) * kerD α (z j) (z k))) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    exact sum_congr rfl fun k _ ↦ by ring
  have h1 : ∑ k ∈ O, ((4 * M - 4 * curvKernel α (z i) (z k)) * kerD α (z i) (z k) -
      (4 * M - 4 * curvKernel α (z j) (z k)) * kerD α (z j) (z k)) ≤ 0 := by
    refine sum_nonpos fun k hk ↦ ?_
    have hMk : curvKernel α (z i) (z k) ≤ M := by
      have := offSum_ge hα₁ hα1 hz hij hk (α := α)
      have := (curvKernel_pos' hα₁ hα1 hz i j).le
      have := (curvKernel_pos' hα₁ hα1 hz j k).le
      rw [hMdef]
      linarith
    have hKk : curvKernel α (z j) (z k) ≤ curvKernel α (z i) (z k) := by
      rw [hK, hK]; exact kerInt_le_kerInt hα0.le (hz j) h.le (hz k)
    have hD0 : 0 ≤ kerD α (z i) (z k) := kerD_nonneg hα0.le (hz i) (hz k)
    have hDk := kerD_le_kerD hα0.le hα1 (hz j) h.le (hz k)
    have : (4 * M - 4 * curvKernel α (z i) (z k)) * kerD α (z i) (z k) ≤
        (4 * M - 4 * curvKernel α (z j) (z k)) * kerD α (z j) (z k) :=
      mul_le_mul (by linarith) hDk hD0 (by linarith)
    linarith
  have hMab : curvKernel α (z i) (z j) ≤ M := by
    have := offSum_ge_pair hα₁ hα1 hz hij (α := α); rw [hMdef]; linarith
  have h2 : (4 * M - 4 * curvKernel α (z i) (z j)) *
      (kerD α (z i) (z j) - kerD α (z j) (z i)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith)
      (by have := kerD_le_kerD_swap hα0.le hα1 (hz j) h.le; linarith)
  rw [offGrad_sub_offGrad hij, offGradSq_sub_offGradSq hij]
  linarith

/-- **`H₁ < 0`** for `0 < α ≤ 1`. -/
theorem H1_neg :
    (1 + α) / 2 * (powSum z (1 + α) ^ 2 * (α * z i ^ (α - 1) - α * z j ^ (α - 1)) -
      powSum z (1 + α) * ((1 + 2 * α) * (z i ^ α) ^ 2 - (1 + 2 * α) * (z j ^ α) ^ 2) +
      ((1 + α) * z i ^ α - (1 + α) * z j ^ α) *
        (2 * powSum z (1 + 2 * α) - powSum z (1 + α) * powSum z α)) +
      powSum z (1 + α) ^ 2 * ((offGrad α z i - offGrad α z j) / 2) < 0 := by
  have hij := ne_of_lt_apply h
  have ha := hz i
  have hb := hz j
  set O := others i j
  set A := z i ^ α with hAdef
  set B := z j ^ α with hBdef
  have hB : 0 < B := Real.rpow_pos_of_pos hb α
  have hAB : B < A := Real.rpow_lt_rpow hb.le h hα0
  have hc0 : 0 < (1 + α) / 2 := by linarith
  have hdW : 0 ≤ (1 + α) * A - (1 + α) * B := by nlinarith
  have hdR : 0 ≤ (1 + 2 * α) * A ^ 2 - (1 + 2 * α) * B ^ 2 := by
    have := pow_le_pow_left₀ hB.le hAB.le 2
    nlinarith
  have hφ : ∀ k, kerD α (z i) (z k) - kerD α (z j) (z k) ≤ 0 := fun k ↦ by
    have := kerD_le_kerD hα0.le hα1 hb h.le (hz k); linarith
  have hpos : ∀ k (s : ℝ), 0 ≤ z k ^ s := fun k s ↦ (Real.rpow_pos_of_pos (hz k) s).le
  refine H1_neg_aux (a := z i) (b := z j) (S := ∑ k ∈ O, z k ^ (1 + α))
    (Pi' := ∑ k ∈ O, z k ^ α) (Ry := ∑ k ∈ O, z k ^ (1 + 2 * α))
    (Φ := ∑ k ∈ O, (kerD α (z i) (z k) - kerD α (z j) (z k)))
    (Ψ2 := ∑ k ∈ O, (z k ^ (1 + α)) ^ 2 * (kerD α (z i) (z k) - kerD α (z j) (z k)))
    (κ := kerD α (z i) (z j) - kerD α (z j) (z i)) ?_ ?_ ?_ (offGrad_sub_offGrad hij) hc0.le ?_ ?_
    hdW (by positivity) (sum_nonneg fun k _ ↦ hpos k _) ?_ ?_ ?_ (H0_neg hc0 hα0 hb h hB hAB)
  · rw [powSum, sum_univ_eq_add_sum_others hij, rpow_one_add_eq ha, rpow_one_add_eq hb]
  · rw [powSum, sum_univ_eq_add_sum_others hij]
  · rw [powSum, sum_univ_eq_add_sum_others hij, rpow_one_add_two_mul_eq ha,
      rpow_one_add_two_mul_eq hb]
  · have := Real.rpow_le_rpow_of_nonpos hb h.le (by linarith : α - 1 ≤ 0)
    nlinarith
  · have := kerD_le_kerD_swap hα0.le hα1 hb h.le; linarith
  · rw [Finset.mul_sum]
    refine sum_le_sum fun k hk ↦ mul_le_mul_of_nonpos_right ?_ (hφ k)
    have h1 : z k ^ (1 + α) ≤ powSum z (1 + α) :=
      single_le_sum (f := fun k ↦ z k ^ (1 + α)) (fun k _ ↦ hpos k _) (mem_univ k)
    have h2 := hpos k (1 + α)
    nlinarith
  · have := sum_mul_le_sum_mul_sum (O := O) (f := fun k ↦ z k ^ (1 + α)) (g := fun k ↦ z k ^ α)
      (fun k _ ↦ hpos k _) (fun k _ ↦ hpos k _)
    refine le_trans (le_of_eq (sum_congr rfl fun k _ ↦ ?_)) this
    rw [← Real.rpow_add (hz k)]
    ring_nf
  · -- the per-point brackets
    set c := (1 + α) / 2 with hc
    set dR := (1 + 2 * α) * A ^ 2 - (1 + 2 * α) * B ^ 2 with hdRdef
    set dW := (1 + α) * A - (1 + α) * B with hdWdef
    have e : ∀ k ∈ O, z k ^ (1 + α) * (-(c * dR) + c * dW * (z k ^ α - (A + B)) +
        z k ^ (1 + α) * (kerD α (z i) (z k) - kerD α (z j) (z k))) =
        -(c * dR) * z k ^ (1 + α) + c * dW * z k ^ (1 + 2 * α) -
          c * dW * (A + B) * z k ^ (1 + α) +
          (z k ^ (1 + α)) ^ 2 * (kerD α (z i) (z k) - kerD α (z j) (z k)) := fun k _ ↦ by
      have : z k ^ (1 + 2 * α) = z k ^ (1 + α) * z k ^ α := by
        rw [← Real.rpow_add (hz k)]; ring_nf
      rw [this]
      ring
    have hsum : ∑ k ∈ O, z k ^ (1 + α) * (-(c * dR) + c * dW * (z k ^ α - (A + B)) +
        z k ^ (1 + α) * (kerD α (z i) (z k) - kerD α (z j) (z k))) ≤ 0 := by
      refine sum_nonpos fun k _ ↦ mul_nonpos_of_nonneg_of_nonpos (hpos k _) ?_
      rcases le_or_gt (z k) (z i) with hk | hk
      · have h1 : z k ^ α ≤ A := Real.rpow_le_rpow (hz k).le hk hα0.le
        have h2 : c * dW * (z k ^ α - (A + B)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc0.le hdW) (by linarith)
        have h3 : z k ^ (1 + α) * (kerD α (z i) (z k) - kerD α (z j) (z k)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (hpos k _) (hφ k)
        have h4 : 0 ≤ c * dR := mul_nonneg hc0.le hdR
        linarith
      · have hG := kerG_nonpos hα0 hα1 hb h.le hk.le
        have e2 : -(c * dR) + c * dW * (z k ^ α - (A + B)) +
            z k ^ (1 + α) * (kerD α (z i) (z k) - kerD α (z j) (z k)) =
            (1 + α) / 2 * (1 + α) * (z i ^ α - z j ^ α) * (z k ^ α - z i ^ α - z j ^ α) -
              (1 + α) / 2 * (1 + 2 * α) * ((z i ^ α) ^ 2 - (z j ^ α) ^ 2) +
            z k ^ (1 + α) * (kerD α (z i) (z k) - kerD α (z j) (z k)) := by
          rw [hdRdef, hdWdef, hc, hAdef, hBdef]
          ring
        rw [e2]
        exact hG
    rw [sum_congr rfl e, sum_add_distrib, sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum,
      ← mul_sum] at hsum
    linarith

/-- **The strict sign for `p > 2`**: for `0 < α ≤ 1`, the gradient of the quantum excess is
strictly smaller at a strictly larger entry. -/
theorem excessGrad_lt_excessGrad : excessGrad α z i < excessGrad α z j := by
  have hij := ne_of_lt_apply h
  have hα₁ : -1 < α := by linarith
  have : Nonempty d := ⟨i⟩
  have hW := powSum_pos hz (1 + α)
  have key := excessGrad_sub_excessGrad (α := α) hz i j
  rw [exGradF_eq _ _ _ _ _ _ _ _ _ _ _ hW.ne'] at key
  rw [← sub_neg, key]
  refine div_neg_of_neg_of_pos ?_ (pow_pos hW 3)
  rw [rpow_one_add_two_mul_sub_one (hz i), rpow_one_add_two_mul_sub_one (hz j),
    rpow_one_add_sub_one, rpow_one_add_sub_one]
  have hM0 : 0 < offSum α z / 2 := by
    have := offSum_ge_pair hα₁ hα1 hz hij (α := α)
    have := curvKernel_pos' hα₁ hα1 hz i j
    linarith
  have hQ : 0 ≤ 2 * (offSum α z / 2) ^ 2 - offSumSq α z / 2 := by
    have := offSumSq_le hα₁ hα1 hz (α := α); nlinarith
  have hT : 0 ≤ powSum z α * powSum z (1 + α) - powSum z (1 + 2 * α) := by
    have := powSum_le_mul (α := α) hz; linarith
  have hdW : 0 ≤ (1 + α) * z i ^ α - (1 + α) * z j ^ α := by
    have := Real.rpow_le_rpow (hz j).le h.le hα0.le
    nlinarith
  exact Z_neg (by linarith) hW hM0 hT (offGrad_sub_nonpos hα0 hα1 hz h)
    (offGrad_bracket_nonpos hα0 hα1 hz h) hdW hQ (H1_neg hα0 hα1 hz h)

end Positive

/-! ### `-1 < α < 0` -/

section Negative

variable {z : d → ℝ} {i j : d}

omit [DecidableEq d] in
/-- `x^(1+2α) + y^(1+2α) ≤ xᵅ y^(1+α) + yᵅ x^(1+α)` for `-1 ≤ α ≤ 0`. -/
theorem rpow_pair_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hα₁ : -1 ≤ α) (hα : α ≤ 0) :
    x ^ (1 + 2 * α) + y ^ (1 + 2 * α) ≤ x ^ α * y ^ (1 + α) + y ^ α * x ^ (1 + α) := by
  have ex : x ^ (1 + 2 * α) = x ^ (1 + α) * x ^ α := by rw [← Real.rpow_add hx]; ring_nf
  have ey : y ^ (1 + 2 * α) = y ^ (1 + α) * y ^ α := by rw [← Real.rpow_add hy]; ring_nf
  have key : (x ^ (1 + α) - y ^ (1 + α)) * (x ^ α - y ^ α) ≤ 0 := by
    rcases le_total x y with hxy | hxy
    · exact mul_nonpos_of_nonpos_of_nonneg
        (by have := Real.rpow_le_rpow hx.le hxy (by linarith : 0 ≤ 1 + α); linarith)
        (by have := Real.rpow_le_rpow_of_nonpos hx hxy hα; linarith)
    · exact mul_nonpos_of_nonneg_of_nonpos
        (by have := Real.rpow_le_rpow hy.le hxy (by linarith : 0 ≤ 1 + α); linarith)
        (by have := Real.rpow_le_rpow_of_nonpos hy hxy hα; linarith)
  rw [ex, ey]
  nlinarith

omit [DecidableEq d] in
/-- `card · P(1+2α) ≤ P(α) P(1+α)` for `-1 ≤ α ≤ 0`. -/
theorem card_mul_powSum_le (hα₁ : -1 ≤ α) (hα : α ≤ 0) (hz : ∀ k, 0 < z k) :
    (Fintype.card d : ℝ) * powSum z (1 + 2 * α) ≤ powSum z α * powSum z (1 + α) := by
  have h1 : powSum z α * powSum z (1 + α) = ∑ k, ∑ l, z k ^ α * z l ^ (1 + α) := by
    rw [powSum, powSum, Finset.sum_mul_sum]
  have h2 : powSum z α * powSum z (1 + α) = ∑ k, ∑ l, z l ^ α * z k ^ (1 + α) := by
    rw [h1, Finset.sum_comm]
  have h3 : ∑ k, ∑ l, (z k ^ (1 + 2 * α) + z l ^ (1 + 2 * α)) ≤
      ∑ k, ∑ l, (z k ^ α * z l ^ (1 + α) + z l ^ α * z k ^ (1 + α)) :=
    sum_le_sum fun k _ ↦ sum_le_sum fun l _ ↦ rpow_pair_le (hz k) (hz l) hα₁ hα |>.trans_eq
      (by ring)
  have h4 : ∑ k, ∑ l, (z k ^ (1 + 2 * α) + z l ^ (1 + 2 * α)) =
      2 * ((Fintype.card d : ℝ) * powSum z (1 + 2 * α)) := by
    simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, powSum, ← mul_sum]
    ring
  have h5 : ∑ k, ∑ l, (z k ^ α * z l ^ (1 + α) + z l ^ α * z k ^ (1 + α)) =
      2 * (powSum z α * powSum z (1 + α)) := by
    simp only [sum_add_distrib]
    rw [← h1, ← h2]
    ring
  linarith

variable (hα₁ : -1 < α) (hα0 : α < 0) (hz : ∀ k, 0 < z k) (h : z j < z i)
include hα₁ hα0 hz h

/-- `∂M ≥ 0` for `-1 < α < 0`. -/
theorem offGrad_sub_nonneg : 0 ≤ (offGrad α z i - offGrad α z j) / 2 := by
  rw [offGrad_sub_offGrad (ne_of_lt_apply h)]
  have h1 := kerD_swap_le_kerD hα₁ hα0 (hz j) h.le
  have h2 : 0 ≤ ∑ k ∈ others i j, (kerD α (z i) (z k) - kerD α (z j) (z k)) :=
    sum_nonneg fun k _ ↦ by
      have := kerD_le_kerD_of_neg hα₁ hα0.le (hz j) h.le (hz k); linarith
  linarith

/-- `8M ∂M - 2 ∂Q ≥ 0` for `-1 < α < 0`, by log-convexity of the kernel. -/
theorem offGrad_bracket_nonneg :
    0 ≤ 8 * (offSum α z / 2) * ((offGrad α z i - offGrad α z j) / 2) -
      2 * ((offGradSq α z i - offGradSq α z j) / 2) := by
  have hij := ne_of_lt_apply h
  have hα1 : α ≤ 1 := by linarith
  set M := offSum α z / 2 with hMdef
  set O := others i j
  have hK : ∀ k l, curvKernel α (z k) (z l) = kerInt α (z k) (z l) := fun k l ↦
    curvKernel_eq_kerInt hα₁ hα1 (hz k) (hz l)
  have e1 : ∑ k ∈ O, ((8 * M - 4 * curvKernel α (z i) (z k)) * kerD α (z i) (z k) -
      (8 * M - 4 * curvKernel α (z j) (z k)) * kerD α (z j) (z k)) =
      8 * M * ∑ k ∈ O, (kerD α (z i) (z k) - kerD α (z j) (z k)) -
        2 * (2 * ∑ k ∈ O, (curvKernel α (z i) (z k) * kerD α (z i) (z k) -
          curvKernel α (z j) (z k) * kerD α (z j) (z k))) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    exact sum_congr rfl fun k _ ↦ by ring
  have h1 : 0 ≤ ∑ k ∈ O, ((8 * M - 4 * curvKernel α (z i) (z k)) * kerD α (z i) (z k) -
      (8 * M - 4 * curvKernel α (z j) (z k)) * kerD α (z j) (z k)) := by
    refine sum_nonneg fun k hk ↦ ?_
    have hMk : curvKernel α (z i) (z k) + curvKernel α (z j) (z k) ≤ M := by
      have := offSum_ge hα₁ hα1 hz hij hk (α := α)
      have := (curvKernel_pos' hα₁ hα1 hz i j).le
      rw [hMdef]
      linarith
    have hKk : curvKernel α (z i) (z k) ≤ curvKernel α (z j) (z k) := by
      rw [hK, hK]; exact kerInt_le_kerInt_of_neg hα₁ hα0.le (hz j) h.le (hz k)
    have hKa := (curvKernel_pos' hα₁ hα1 hz i k).le
    have hDb : kerD α (z j) (z k) ≤ 0 := kerD_nonpos hα₁ hα0.le (hz j) (hz k)
    have hφ := kerD_le_kerD_of_neg hα₁ hα0.le (hz j) h.le (hz k)
    have hK4 := kerD_mul_kerInt_le hα₁ hα0.le (hz j) h.le (hz k)
    rw [← hK, ← hK] at hK4
    have h5 : 4 * curvKernel α (z j) (z k) * (kerD α (z i) (z k) - kerD α (z j) (z k)) ≤
        (8 * M - 4 * curvKernel α (z i) (z k)) * (kerD α (z i) (z k) - kerD α (z j) (z k)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  have hMab : curvKernel α (z i) (z j) ≤ M := by
    have := offSum_ge_pair hα₁ hα1 hz hij (α := α); rw [hMdef]; linarith
  have h2 : 0 ≤ (8 * M - 4 * curvKernel α (z i) (z j)) *
      (kerD α (z i) (z j) - kerD α (z j) (z i)) :=
    mul_nonneg (by have := (curvKernel_pos' hα₁ hα1 hz i j).le; linarith)
      (by have := kerD_swap_le_kerD hα₁ hα0 (hz j) h.le; linarith)
  rw [offGrad_sub_offGrad hij, offGradSq_sub_offGradSq hij]
  linarith

omit [DecidableEq d] in
/-- **`X > 0`** for `-1 < α < 0`: `X = W(W ∂P(α) - ∂P(1+2α)) - ∂W (W P(α) - 2P(1+2α))`. -/
theorem X_pos :
    0 < powSum z (1 + α) ^ 2 * (α * z i ^ (α - 1) - α * z j ^ (α - 1)) -
      powSum z (1 + α) * ((1 + 2 * α) * (z i ^ α) ^ 2 - (1 + 2 * α) * (z j ^ α) ^ 2) +
      ((1 + α) * z i ^ α - (1 + α) * z j ^ α) *
        (2 * powSum z (1 + 2 * α) - powSum z (1 + α) * powSum z α) := by
  classical
  have hij := ne_of_lt_apply h
  have : Nonempty d := ⟨i⟩
  have ha := hz i
  have hb := hz j
  set A := z i ^ α with hAdef
  set B := z j ^ α with hBdef
  have hA : 0 < A := Real.rpow_pos_of_pos ha α
  have hAB : A < B := Real.rpow_lt_rpow_of_neg hb h hα0
  have hW := powSum_pos hz (1 + α)
  set W := powSum z (1 + α) with hWdef
  -- `W ≥ w`
  have hw : z i * A + z j * B ≤ W := by
    have hS : 0 ≤ ∑ k ∈ others i j, z k ^ (1 + α) :=
      sum_nonneg fun k _ ↦ (Real.rpow_pos_of_pos (hz k) _).le
    have : W = z i * A + z j * B + ∑ k ∈ others i j, z k ^ (1 + α) := by
      rw [hWdef, powSum, sum_univ_eq_add_sum_others hij, rpow_one_add_eq ha, rpow_one_add_eq hb]
    linarith
  -- `∂P(α) > 0`
  have hdP : 0 < α * z i ^ (α - 1) - α * z j ^ (α - 1) := by
    have := Real.rpow_lt_rpow_of_neg hb h (by linarith : α - 1 < 0)
    nlinarith
  -- `w ∂P(α) - ∂P(1+2α) > 0`
  have hwP : 0 < (z i * A + z j * B) * (α * z i ^ (α - 1) - α * z j ^ (α - 1)) -
      ((1 + 2 * α) * A ^ 2 - (1 + 2 * α) * B ^ 2) := by
    have e : (z i * A + z j * B) * (α * z i ^ (α - 1) - α * z j ^ (α - 1)) -
        ((1 + 2 * α) * A ^ 2 - (1 + 2 * α) * B ^ 2) =
        (1 + α) * (B ^ 2 - A ^ 2) + (-α) * (A * B) * (z i / z j - z j / z i) := by
      rw [Real.rpow_sub_one ha.ne', Real.rpow_sub_one hb.ne']
      field_simp
      ring
    rw [e]
    have h1 : 0 < (1 + α) * (B ^ 2 - A ^ 2) := mul_pos (by linarith) (by nlinarith)
    have h2 : 0 ≤ z i / z j - z j / z i := by
      rw [sub_nonneg, div_le_div_iff₀ ha hb]
      nlinarith
    have h3 : 0 ≤ (-α) * (A * B) * (z i / z j - z j / z i) := by
      have : 0 < B := lt_trans hA hAB
      exact mul_nonneg (mul_nonneg (by linarith) (by positivity)) h2
    linarith
  have hWP : 0 < W * (α * z i ^ (α - 1) - α * z j ^ (α - 1)) -
      ((1 + 2 * α) * A ^ 2 - (1 + 2 * α) * B ^ 2) := by nlinarith
  -- `W P(α) ≥ 2 P(1+2α)`
  have hcard : (2 : ℝ) ≤ Fintype.card d := by
    have := Finset.card_le_univ ({i, j} : Finset d)
    rw [Finset.card_pair hij] at this
    exact_mod_cast this
  have hR := powSum_pos hz (1 + 2 * α)
  have hPW := card_mul_powSum_le hα₁.le hα0.le hz
  have hdW : (1 + α) * A - (1 + α) * B < 0 := by nlinarith
  have e : W ^ 2 * (α * z i ^ (α - 1) - α * z j ^ (α - 1)) -
      W * ((1 + 2 * α) * A ^ 2 - (1 + 2 * α) * B ^ 2) +
      ((1 + α) * A - (1 + α) * B) * (2 * powSum z (1 + 2 * α) - W * powSum z α) =
      W * (W * (α * z i ^ (α - 1) - α * z j ^ (α - 1)) -
        ((1 + 2 * α) * A ^ 2 - (1 + 2 * α) * B ^ 2)) +
      (-((1 + α) * A - (1 + α) * B)) * (powSum z α * W - 2 * powSum z (1 + 2 * α)) := by ring
  rw [e]
  have h1 : 0 < W * (W * (α * z i ^ (α - 1) - α * z j ^ (α - 1)) -
      ((1 + 2 * α) * A ^ 2 - (1 + 2 * α) * B ^ 2)) := mul_pos hW hWP
  have h2 : 0 ≤ (-((1 + α) * A - (1 + α) * B)) * (powSum z α * W - 2 * powSum z (1 + 2 * α)) :=
    mul_nonneg (by linarith) (by nlinarith)
  linarith

/-- **The strict sign for `1 < p < 2`**: for `-1 < α < 0`, the gradient of the quantum excess is
strictly larger at a strictly larger entry. -/
theorem excessGrad_lt_excessGrad_of_neg : excessGrad α z j < excessGrad α z i := by
  have hij := ne_of_lt_apply h
  have hα1 : α ≤ 1 := by linarith
  have : Nonempty d := ⟨i⟩
  have hW := powSum_pos hz (1 + α)
  have key := excessGrad_sub_excessGrad (α := α) hz i j
  rw [exGradF_eq _ _ _ _ _ _ _ _ _ _ _ hW.ne'] at key
  rw [← sub_pos, key]
  refine div_pos ?_ (pow_pos hW 3)
  rw [rpow_one_add_two_mul_sub_one (hz i), rpow_one_add_two_mul_sub_one (hz j),
    rpow_one_add_sub_one, rpow_one_add_sub_one]
  have hM0 : 0 < offSum α z / 2 := by
    have := offSum_ge_pair hα₁ hα1 hz hij (α := α)
    have := curvKernel_pos' hα₁ hα1 hz i j
    linarith
  have hQ : 0 ≤ 2 * (offSum α z / 2) ^ 2 - offSumSq α z / 2 := by
    have := offSumSq_le hα₁ hα1 hz (α := α); nlinarith
  have hT : 0 ≤ powSum z α * powSum z (1 + α) - powSum z (1 + 2 * α) := by
    have := powSum_le_mul (α := α) hz; linarith
  have hdW : (1 + α) * z i ^ α - (1 + α) * z j ^ α ≤ 0 := by
    have := Real.rpow_le_rpow_of_nonpos (hz j) h.le hα0.le
    nlinarith
  have hMQ := offGrad_bracket_nonneg hα₁ hα0 hz h
  exact Z_pos (by linarith) hW hM0 hT (offGrad_sub_nonneg hα₁ hα0 hz h) hMQ hdW hQ
    (X_pos hα₁ hα0 hz h)

end Negative

end AlphaCurvature.Quantum
