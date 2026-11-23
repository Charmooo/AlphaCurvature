/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import AlphaCurvature.Quantum.Kernel

/-!
# Inequalities for the curvature kernel

From the power-mean representation `K(a, b) = c ∫₀¹ (t aᵉ + (1 - t) bᵉ)^β dt` (`kerInt`), with
partial derivatives `K₁ = kerD` and `K₁₁ = kerDD` in the first argument. Write `a ≥ b > 0`.

* **`0 < α ≤ 1`** (`p > 2`): `K₁ ≥ 0`, `K₁₁ ≤ 0`, so `K` increases and `K₁` decreases in each
  argument (`kerInt_le_kerInt`, `kerD_le_kerD`); `K₁(a, b) ≤ K₁(b, a)`
  (`kerD_le_kerD_swap`), pointwise in the integrand; and the bound
  `K₁₁(s, y) ≤ -c² α y^(α-1)/(6 s)` for `s ≤ y` (`kerDD_le`), whose consequence is the
  monotonicity of `g(s) = c(1+α) yᵅ sᵅ - c(2+3α) s²ᵅ + y¹⁺ᵅ K₁(s, y)` on `(0, y]`
  (`kerG_nonpos`).
* **`-1 < α < 0`** (`1 < p < 2`): the mirror facts `K₁ ≤ 0`, `K₁₁ ≥ 0` (`kerInt_le_kerInt_of_neg`,
  `kerD_le_kerD_of_neg`); `K₁(b, a) ≤ K₁(a, b)` (`kerD_swap_le_kerD`), by pairing `t` with
  `1 - t`; and **log-convexity in the first argument**, `K₁(b, y) K(a, y) ≤ K₁(a, y) K(b, y)`
  (`kerD_mul_kerInt_le`): the integrand is log-convex, `F₁² ≤ F F₁₁`, so by the discriminant of
  `λ ↦ ∫ (λ² F + 2λ F₁ + F₁₁) ≥ 0` also `K₁² ≤ K K₁₁`, and `K₁/K` increases.
-/

open Set Filter MeasureTheory
open scoped Topology Interval

namespace AlphaCurvature.Quantum

variable {α t a b : ℝ}

/-! ### Exponent bookkeeping -/

section Exponents

theorem kerExp_mul (hα : α ≠ 1) : (1 - α) / 2 * (2 * α / (1 - α)) = α := by
  have : 1 - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  field_simp

theorem rpow_kerExp_sub_one {x : ℝ} (hα : α ≠ 1) (hx : 0 < x) :
    (x ^ ((1 - α) / 2)) ^ (2 * α / (1 - α) - 1) = x ^ (α - (1 - α) / 2) := by
  rw [← Real.rpow_mul hx.le, mul_sub, kerExp_mul hα, mul_one]

theorem rpow_kerExp_sub_two {x : ℝ} (hα : α ≠ 1) (hx : 0 < x) :
    (x ^ ((1 - α) / 2)) ^ (2 * α / (1 - α) - 2) = x ^ (α - 2 * ((1 - α) / 2)) := by
  rw [← Real.rpow_mul hx.le, mul_sub, kerExp_mul hα]
  ring_nf

/-- `kerF₁ = α t a^(e-1) m^(β-1)`. -/
theorem kerF₁_eq_rpow (hα : α ≠ 1) (ht : t ∈ Icc (0 : ℝ) 1) (ha : 0 < a) (hb : 0 < b) :
    kerF₁ α t a b = α * t * (a ^ ((1 - α) / 2 - 1) * kerMix α t a b ^ (2 * α / (1 - α) - 1)) := by
  have hm := kerMix_pos (α := α) ht ha hb
  rw [kerF₁_of_ne hα, kerF_of_ne hα, Real.rpow_sub_one ha.ne', Real.rpow_sub_one hm.ne']
  field_simp

theorem kerMix_le (hα : α < 1) (ht : t ∈ Icc (0 : ℝ) 1) (hb : 0 < b) (hab : b ≤ a) :
    kerMix α t a b ≤ a ^ ((1 - α) / 2) := by
  have := Real.rpow_le_rpow hb.le hab (by linarith : 0 ≤ (1 - α) / 2)
  unfold kerMix
  nlinarith [ht.1, ht.2]

theorem le_kerMix (hα : α < 1) (ht : t ∈ Icc (0 : ℝ) 1) (hb : 0 < b) (hab : b ≤ a) :
    b ^ ((1 - α) / 2) ≤ kerMix α t a b := by
  have := Real.rpow_le_rpow hb.le hab (by linarith : 0 ≤ (1 - α) / 2)
  unfold kerMix
  nlinarith [ht.1, ht.2]

theorem kerMix_le' (hα : α < 1) (ht : t ∈ Icc (0 : ℝ) 1) (hb : 0 < b) (hab : b ≤ a) :
    kerMix α t b a ≤ a ^ ((1 - α) / 2) := by
  rw [← kerMix_symm]
  exact kerMix_le hα ⟨by linarith [ht.2], by linarith [ht.1]⟩ hb hab

theorem le_kerMix' (hα : α < 1) (ht : t ∈ Icc (0 : ℝ) 1) (hb : 0 < b) (hab : b ≤ a) :
    b ^ ((1 - α) / 2) ≤ kerMix α t b a := by
  rw [← kerMix_symm]
  exact le_kerMix hα ⟨by linarith [ht.2], by linarith [ht.1]⟩ hb hab

end Exponents

/-! ### Pointwise facts about the integrand -/

section Pointwise

variable (ht : t ∈ Icc (0 : ℝ) 1) (ha : 0 < a) (hb : 0 < b)
include ht ha hb

theorem kerF₁_nonneg (hα : 0 ≤ α) : 0 ≤ kerF₁ α t a b := by
  have hF := kerF_pos (α := α) ht ha hb
  by_cases h : α = 1
  · subst h
    rw [kerF₁_one]
    exact div_nonneg (mul_nonneg ht.1 hF.le) ha.le
  · rw [kerF₁_of_ne h]
    have := Real.rpow_pos_of_pos ha ((1 - α) / 2)
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hα ht.1) this.le) hF.le)
      (mul_pos ha (kerMix_pos ht ha hb)).le

theorem kerF₁_nonpos (hα : α ≤ 0) : kerF₁ α t a b ≤ 0 := by
  have h : α ≠ 1 := by linarith
  have hF := kerF_pos (α := α) ht ha hb
  have hm := kerMix_pos (α := α) ht ha hb
  have := Real.rpow_pos_of_pos ha ((1 - α) / 2)
  have e : kerF₁ α t a b =
      α * (t * a ^ ((1 - α) / 2) * kerF α t a b / (a * kerMix α t a b)) := by
    rw [kerF₁_of_ne h]
    ring
  rw [e]
  exact mul_nonpos_of_nonpos_of_nonneg hα
    (div_nonneg (mul_nonneg (mul_nonneg ht.1 this.le) hF.le) (mul_pos ha hm).le)

omit ht ha hb in
/-- `kerF₁₁ = (α t aᵉ F/(a² m²)) · (t aᵉ (α - 1) - c (1 - t) bᵉ)`, with a nonpositive bracket. -/
theorem kerF₁₁_eq (h : α ≠ 1) :
    kerF₁₁ α t a b = α * (t * a ^ ((1 - α) / 2) * kerF α t a b / (a ^ 2 * kerMix α t a b ^ 2)) *
      (t * a ^ ((1 - α) / 2) * (α - 1) - (1 + α) / 2 * (1 - t) * b ^ ((1 - α) / 2)) := by
  rw [kerF₁₁_of_ne h]
  ring

theorem kerF₁₁_bracket_nonpos (hα₁ : -1 ≤ α) (hα : α ≤ 1) :
    t * a ^ ((1 - α) / 2) * (α - 1) - (1 + α) / 2 * (1 - t) * b ^ ((1 - α) / 2) ≤ 0 := by
  have h1 := Real.rpow_pos_of_pos ha ((1 - α) / 2)
  have h2 := Real.rpow_pos_of_pos hb ((1 - α) / 2)
  have h3 : 0 ≤ t * a ^ ((1 - α) / 2) := mul_nonneg ht.1 h1.le
  have h4 : 0 ≤ (1 + α) / 2 * (1 - t) := mul_nonneg (by linarith) (by linarith [ht.2])
  nlinarith

theorem kerF₁₁_nonpos (hα₀ : 0 ≤ α) (hα : α ≤ 1) : kerF₁₁ α t a b ≤ 0 := by
  have hF := kerF_pos (α := α) ht ha hb
  by_cases h : α = 1
  · subst h
    rw [kerF₁₁_one]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos ht.1 (by linarith [ht.2]))
        hF.le) (sq_nonneg a)
  · rw [kerF₁₁_eq h]
    have := Real.rpow_pos_of_pos ha ((1 - α) / 2)
    refine mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hα₀ ?_)
      (kerF₁₁_bracket_nonpos ht ha hb (by linarith) hα)
    exact div_nonneg (mul_nonneg (mul_nonneg ht.1 this.le) hF.le) (by positivity)

theorem kerF₁₁_nonneg (hα₁ : -1 ≤ α) (hα : α ≤ 0) : 0 ≤ kerF₁₁ α t a b := by
  have h : α ≠ 1 := by linarith
  have hF := kerF_pos (α := α) ht ha hb
  rw [kerF₁₁_eq h]
  have := Real.rpow_pos_of_pos ha ((1 - α) / 2)
  refine mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hα ?_)
    (kerF₁₁_bracket_nonpos ht ha hb hα₁ (by linarith))
  exact div_nonneg (mul_nonneg (mul_nonneg ht.1 this.le) hF.le) (by positivity)

/-- **Log-convexity of the integrand** for `α ≤ 0`: `F₁² ≤ F F₁₁`. -/
theorem kerF₁_sq_le (hα₁ : -1 ≤ α) (hα : α ≤ 0) :
    kerF₁ α t a b ^ 2 ≤ kerF α t a b * kerF₁₁ α t a b := by
  have h : α ≠ 1 := by linarith
  have hF := kerF_pos (α := α) ht ha hb
  have hm := kerMix_pos (α := α) ht ha hb
  have hu := Real.rpow_pos_of_pos ha ((1 - α) / 2)
  have hv := Real.rpow_pos_of_pos hb ((1 - α) / 2)
  have e : kerF α t a b * kerF₁₁ α t a b - kerF₁ α t a b ^ 2 =
      (α * (t * a ^ ((1 - α) / 2) * kerF α t a b ^ 2 / (a ^ 2 * kerMix α t a b ^ 2))) *
        (-(t * a ^ ((1 - α) / 2)) - (1 + α) / 2 * (1 - t) * b ^ ((1 - α) / 2)) := by
    rw [kerF₁₁_of_ne h, kerF₁_of_ne h]
    field_simp
    ring
  have h1 : α * (t * a ^ ((1 - α) / 2) * kerF α t a b ^ 2 / (a ^ 2 * kerMix α t a b ^ 2)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hα (by have := ht.1; positivity)
  have h2 : -(t * a ^ ((1 - α) / 2)) - (1 + α) / 2 * (1 - t) * b ^ ((1 - α) / 2) ≤ 0 := by
    have h3 : 0 ≤ t * a ^ ((1 - α) / 2) := mul_nonneg ht.1 hu.le
    have h4 : 0 ≤ (1 + α) / 2 * (1 - t) := mul_nonneg (by linarith) (by linarith [ht.2])
    nlinarith
  nlinarith [mul_nonneg_of_nonpos_of_nonpos h1 h2]

omit ha in
/-- The `κ`-inequality for `0 ≤ α ≤ 1`, pointwise: `F₁(t; a, b) ≤ F₁(t; b, a)` for `a ≥ b`. -/
theorem kerF₁_le_kerF₁_swap (hα₀ : 0 ≤ α) (hα : α ≤ 1) (hab : b ≤ a) :
    kerF₁ α t a b ≤ kerF₁ α t b a := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  by_cases h : α = 1
  · subst h
    have e : ∀ x y : ℝ, 0 < x → 0 < y → kerF₁ 1 t x y = t * (y / x) ^ (1 - t) := by
      intro x y hx hy
      rw [kerF₁_one, kerF_one, Real.div_rpow hy.le hx.le, Real.rpow_sub hx, Real.rpow_one]
      have := Real.rpow_pos_of_pos hx t
      field_simp
    rw [e a b ha hb, e b a hb ha]
    refine mul_le_mul_of_nonneg_left ?_ ht.1
    have h1 : b / a ≤ 1 := (div_le_one ha).2 hab
    have h2 : 1 ≤ a / b := (one_le_div hb).2 hab
    calc (b / a) ^ (1 - t) ≤ 1 := Real.rpow_le_one (by positivity) h1 (by linarith [ht.2])
      _ ≤ (a / b) ^ (1 - t) := Real.one_le_rpow h2 (by linarith [ht.2])
  have hα1 : α < 1 := lt_of_le_of_ne hα h
  have ht' := ht
  rw [kerF₁_eq_rpow h ht ha hb, kerF₁_eq_rpow h ht hb ha]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hα₀ ht.1)
  have hA := le_kerMix hα1 ht hb hab
  have hA' := kerMix_le hα1 ht hb hab
  have hB := le_kerMix' hα1 ht hb hab
  have hB' := kerMix_le' hα1 ht hb hab
  have hm1 := kerMix_pos (α := α) ht ha hb
  have hm2 := kerMix_pos (α := α) ht hb ha
  have hpa := Real.rpow_pos_of_pos ha ((1 - α) / 2)
  have hpb := Real.rpow_pos_of_pos hb ((1 - α) / 2)
  have hea := Real.rpow_pos_of_pos ha ((1 - α) / 2 - 1)
  have heb := Real.rpow_pos_of_pos hb ((1 - α) / 2 - 1)
  rcases le_or_gt 1 (2 * α / (1 - α)) with hβ | hβ
  · -- `β ≥ 1`: both sides are bounded by `x^(α-1)`
    have h1 : kerMix α t a b ^ (2 * α / (1 - α) - 1) ≤
        (a ^ ((1 - α) / 2)) ^ (2 * α / (1 - α) - 1) :=
      Real.rpow_le_rpow hm1.le hA' (by linarith)
    have h2 : (b ^ ((1 - α) / 2)) ^ (2 * α / (1 - α) - 1) ≤
        kerMix α t b a ^ (2 * α / (1 - α) - 1) :=
      Real.rpow_le_rpow hpb.le hB (by linarith)
    rw [rpow_kerExp_sub_one h ha] at h1
    rw [rpow_kerExp_sub_one h hb] at h2
    have e : ∀ x : ℝ, 0 < x → x ^ ((1 - α) / 2 - 1) * x ^ (α - (1 - α) / 2) = x ^ (α - 1) :=
      fun x hx ↦ by rw [← Real.rpow_add hx]; ring_nf
    have h3 : a ^ (α - 1) ≤ b ^ (α - 1) := Real.rpow_le_rpow_of_nonpos hb hab (by linarith)
    calc a ^ ((1 - α) / 2 - 1) * kerMix α t a b ^ (2 * α / (1 - α) - 1)
        ≤ a ^ ((1 - α) / 2 - 1) * a ^ (α - (1 - α) / 2) := mul_le_mul_of_nonneg_left h1 hea.le
      _ = a ^ (α - 1) := e a ha
      _ ≤ b ^ (α - 1) := h3
      _ = b ^ ((1 - α) / 2 - 1) * b ^ (α - (1 - α) / 2) := (e b hb).symm
      _ ≤ b ^ ((1 - α) / 2 - 1) * kerMix α t b a ^ (2 * α / (1 - α) - 1) :=
        mul_le_mul_of_nonneg_left h2 heb.le
  · -- `0 ≤ β < 1`
    have h1 : kerMix α t a b ^ (2 * α / (1 - α) - 1) ≤
        (b ^ ((1 - α) / 2)) ^ (2 * α / (1 - α) - 1) :=
      Real.rpow_le_rpow_of_nonpos hpb hA (by linarith)
    have h2 : (a ^ ((1 - α) / 2)) ^ (2 * α / (1 - α) - 1) ≤
        kerMix α t b a ^ (2 * α / (1 - α) - 1) :=
      Real.rpow_le_rpow_of_nonpos hm2 hB' (by linarith)
    rw [rpow_kerExp_sub_one h hb] at h1
    rw [rpow_kerExp_sub_one h ha] at h2
    have e : ∀ x : ℝ, 0 < x → x ^ ((1 - α) / 2 - 1) = x ^ (-2 * α) * x ^ (α - (1 - α) / 2) :=
      fun x hx ↦ by rw [← Real.rpow_add hx]; ring_nf
    have h3 : a ^ (-2 * α) ≤ b ^ (-2 * α) := Real.rpow_le_rpow_of_nonpos hb hab (by linarith)
    have hxa := Real.rpow_pos_of_pos ha (α - (1 - α) / 2)
    have hxb := Real.rpow_pos_of_pos hb (α - (1 - α) / 2)
    calc a ^ ((1 - α) / 2 - 1) * kerMix α t a b ^ (2 * α / (1 - α) - 1)
        ≤ a ^ ((1 - α) / 2 - 1) * b ^ (α - (1 - α) / 2) := mul_le_mul_of_nonneg_left h1 hea.le
      _ = a ^ (-2 * α) * (a ^ (α - (1 - α) / 2) * b ^ (α - (1 - α) / 2)) := by rw [e a ha]; ring
      _ ≤ b ^ (-2 * α) * (a ^ (α - (1 - α) / 2) * b ^ (α - (1 - α) / 2)) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = b ^ ((1 - α) / 2 - 1) * a ^ (α - (1 - α) / 2) := by rw [e b hb]; ring
      _ ≤ b ^ ((1 - α) / 2 - 1) * kerMix α t b a ^ (2 * α / (1 - α) - 1) :=
        mul_le_mul_of_nonneg_left h2 heb.le

omit ha in
/-- The `κ`-inequality for `α < 0`, pointwise after pairing `t` with `1 - t`. -/
theorem kerF₁_swap_pair_nonneg (hα₁ : -1 < α) (hα : α < 0) (hab : b ≤ a) :
    0 ≤ (kerF₁ α t a b - kerF₁ α t b a) + (kerF₁ α (1 - t) a b - kerF₁ α (1 - t) b a) := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have h : α ≠ 1 := by linarith
  have ht1 : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [kerF₁_eq_rpow h ht ha hb, kerF₁_eq_rpow h ht hb ha, kerF₁_eq_rpow h ht1 ha hb,
    kerF₁_eq_rpow h ht1 hb ha, kerMix_symm, kerMix_symm]
  set P := kerMix α t a b ^ (2 * α / (1 - α) - 1)
  set Q := kerMix α t b a ^ (2 * α / (1 - α) - 1)
  set A' := a ^ ((1 - α) / 2 - 1)
  set B' := b ^ ((1 - α) / 2 - 1)
  have hP : 0 < P := Real.rpow_pos_of_pos (kerMix_pos ht ha hb) _
  have hQ : 0 < Q := Real.rpow_pos_of_pos (kerMix_pos ht hb ha) _
  have hAB : A' ≤ B' := Real.rpow_le_rpow_of_nonpos hb hab (by linarith)
  have hB0 : 0 < B' := Real.rpow_pos_of_pos hb _
  have hβ : 2 * α / (1 - α) - 1 ≤ 0 := by
    have : 2 * α / (1 - α) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  have hpa := Real.rpow_le_rpow hb.le hab (by linarith : 0 ≤ (1 - α) / 2)
  have hpb := Real.rpow_pos_of_pos hb ((1 - α) / 2)
  suffices hS : P * (t * A' - (1 - t) * B') + Q * ((1 - t) * A' - t * B') ≤ 0 by
    have e : α * t * (A' * P) - α * t * (B' * Q) + (α * (1 - t) * (A' * Q) - α * (1 - t) * (B' * P))
        = α * (P * (t * A' - (1 - t) * B') + Q * ((1 - t) * A' - t * B')) := by ring
    rw [e]
    exact mul_nonneg_of_nonpos_of_nonpos hα.le hS
  rcases le_total (1 / 2) t with h2 | h2
  · -- `t ≥ 1/2`: the mean at `t` is the larger, so `P ≤ Q`
    have hm : kerMix α t b a ≤ kerMix α t a b := by unfold kerMix; nlinarith
    have hPQ : P ≤ Q := Real.rpow_le_rpow_of_nonpos (kerMix_pos ht hb ha) hm hβ
    have hY : (1 - t) * A' - t * B' ≤ 0 := by nlinarith [ht.2]
    rcases le_total 0 (t * A' - (1 - t) * B') with hX | hX
    · nlinarith
    · nlinarith
  · have hm : kerMix α t a b ≤ kerMix α t b a := by unfold kerMix; nlinarith
    have hPQ : Q ≤ P := Real.rpow_le_rpow_of_nonpos (kerMix_pos ht ha hb) hm hβ
    have hX : t * A' - (1 - t) * B' ≤ 0 := by nlinarith [ht.1]
    rcases le_total 0 ((1 - t) * A' - t * B') with hY | hY
    · nlinarith
    · nlinarith

omit ha hb in
/-- **The pointwise form of L1**: `F₁₁(t; s, y) ≤ -c α t(1 - t) y^(α-1)/s` for `0 < s ≤ y`. -/
theorem kerF₁₁_le (hα₀ : 0 < α) (hα : α ≤ 1) {s y : ℝ} (hs : 0 < s) (hsy : s ≤ y) :
    kerF₁₁ α t s y ≤ -((1 + α) / 2 * α * (t * (1 - t)) * y ^ (α - 1) / s) := by
  have hy : 0 < y := lt_of_lt_of_le hs hsy
  have htt : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (by linarith [ht.2])
  by_cases h : α = 1
  · subst h
    rw [kerF₁₁_one, kerF_one]
    have hX : s ≤ s ^ t * y ^ (1 - t) := by
      have h1 : s ^ (1 - t) ≤ y ^ (1 - t) := Real.rpow_le_rpow hs.le hsy (by linarith [ht.2])
      have h2 : s = s ^ t * s ^ (1 - t) := by
        rw [← Real.rpow_add hs, add_sub_cancel, Real.rpow_one]
      calc s = s ^ t * s ^ (1 - t) := h2
        _ ≤ s ^ t * y ^ (1 - t) := mul_le_mul_of_nonneg_left h1 (by positivity)
    have h1 : 1 / s ≤ s ^ t * y ^ (1 - t) / s ^ 2 := by
      rw [div_le_div_iff₀ hs (by positivity)]
      nlinarith
    calc t * (t - 1) * (s ^ t * y ^ (1 - t)) / s ^ 2
        = -(t * (1 - t)) * (s ^ t * y ^ (1 - t) / s ^ 2) := by ring
      _ ≤ -(t * (1 - t)) * (1 / s) := mul_le_mul_of_nonpos_left h1 (neg_nonpos.2 htt)
      _ = _ := by norm_num [div_eq_mul_inv]
  have hα1 : α < 1 := lt_of_le_of_ne hα h
  have hm := kerMix_pos (α := α) ht hs hy
  have hu := Real.rpow_pos_of_pos hs ((1 - α) / 2)
  have hv := Real.rpow_pos_of_pos hy ((1 - α) / 2)
  have hF := kerF_pos (α := α) ht hs hy
  -- the key bound `y^(α-1) ≤ s^(e-1) m^(β-2) yᵉ`
  have key : y ^ (α - 1) ≤
      s ^ ((1 - α) / 2 - 1) * kerMix α t s y ^ (2 * α / (1 - α) - 2) * y ^ ((1 - α) / 2) := by
    have hmu := le_kerMix' hα1 ht hs hsy
    have hmv := kerMix_le' hα1 ht hs hsy
    have hs1 : y ^ ((1 - α) / 2 - 1) ≤ s ^ ((1 - α) / 2 - 1) :=
      Real.rpow_le_rpow_of_nonpos hs hsy (by linarith)
    rcases le_total (2 * α / (1 - α)) 2 with hβ | hβ
    · have h1 : (y ^ ((1 - α) / 2)) ^ (2 * α / (1 - α) - 2) ≤
          kerMix α t s y ^ (2 * α / (1 - α) - 2) :=
        Real.rpow_le_rpow_of_nonpos hm hmv (by linarith)
      rw [rpow_kerExp_sub_two h hy] at h1
      calc y ^ (α - 1) = y ^ ((1 - α) / 2 - 1) * y ^ (α - 2 * ((1 - α) / 2)) *
            y ^ ((1 - α) / 2) := by rw [← Real.rpow_add hy, ← Real.rpow_add hy]; ring_nf
        _ ≤ _ := by gcongr
    · have h1 : (s ^ ((1 - α) / 2)) ^ (2 * α / (1 - α) - 2) ≤
          kerMix α t s y ^ (2 * α / (1 - α) - 2) :=
        Real.rpow_le_rpow hu.le hmu (by linarith)
      rw [rpow_kerExp_sub_two h hs] at h1
      have h2 : y ^ (α - (1 - α) / 2 - 1) ≤ s ^ (α - (1 - α) / 2 - 1) :=
        Real.rpow_le_rpow_of_nonpos hs hsy (by linarith)
      calc y ^ (α - 1) = y ^ (α - (1 - α) / 2 - 1) * y ^ ((1 - α) / 2) := by
            rw [← Real.rpow_add hy]; ring_nf
        _ ≤ s ^ (α - (1 - α) / 2 - 1) * y ^ ((1 - α) / 2) := by gcongr
        _ = s ^ ((1 - α) / 2 - 1) * s ^ (α - 2 * ((1 - α) / 2)) * y ^ ((1 - α) / 2) := by
            rw [← Real.rpow_add hs]; ring_nf
        _ ≤ _ := by gcongr
  have e2 : s ^ ((1 - α) / 2 - 1) * kerMix α t s y ^ (2 * α / (1 - α) - 2) =
      s ^ ((1 - α) / 2) * kerF α t s y / (s * kerMix α t s y ^ 2) := by
    rw [kerF_of_ne h, Real.rpow_sub_one hs.ne', Real.rpow_sub hm, Real.rpow_two]
    field_simp
  rw [e2] at key
  rw [kerF₁₁_eq h]
  have hG : 0 ≤ α * (t * s ^ ((1 - α) / 2) * kerF α t s y / (s ^ 2 * kerMix α t s y ^ 2)) := by
    have := ht.1
    positivity
  have hbr : t * s ^ ((1 - α) / 2) * (α - 1) - (1 + α) / 2 * (1 - t) * y ^ ((1 - α) / 2) ≤
      -((1 + α) / 2 * (1 - t) * y ^ ((1 - α) / 2)) := by
    have : 0 ≤ t * s ^ ((1 - α) / 2) := mul_nonneg ht.1 hu.le
    nlinarith
  calc α * (t * s ^ ((1 - α) / 2) * kerF α t s y / (s ^ 2 * kerMix α t s y ^ 2)) *
        (t * s ^ ((1 - α) / 2) * (α - 1) - (1 + α) / 2 * (1 - t) * y ^ ((1 - α) / 2))
      ≤ α * (t * s ^ ((1 - α) / 2) * kerF α t s y / (s ^ 2 * kerMix α t s y ^ 2)) *
        -((1 + α) / 2 * (1 - t) * y ^ ((1 - α) / 2)) := mul_le_mul_of_nonneg_left hbr hG
    _ = -((1 + α) / 2 * α * (t * (1 - t)) / s *
        (s ^ ((1 - α) / 2) * kerF α t s y / (s * kerMix α t s y ^ 2) * y ^ ((1 - α) / 2))) := by
        field_simp
    _ ≤ -((1 + α) / 2 * α * (t * (1 - t)) / s * y ^ (α - 1)) := by
        refine neg_le_neg (mul_le_mul_of_nonneg_left key ?_)
        have : 0 ≤ 1 + α := by linarith
        positivity
    _ = _ := by ring

end Pointwise

/-! ### Integrated facts -/

section Integrated

variable {y : ℝ}

theorem continuousOn_kerF (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (fun t ↦ kerF α t a b) (Icc 0 1) := fun t ht ↦
  ((contDiffAt_kerF (α := α) (fa := fun _ ↦ a) (fb := fun _ ↦ b) (z := ((0 : ℝ), t))
    contDiffAt_const contDiffAt_const ha hb ht).continuousAt.comp
    (f := fun s : ℝ ↦ ((0 : ℝ), s))
    (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt

theorem continuousOn_kerF₁₁ (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (fun t ↦ kerF₁₁ α t a b) (Icc 0 1) := by
  have hF := continuousOn_kerF (α := α) ha hb
  by_cases h : α = 1
  · subst h
    simp only [kerF₁₁_one]
    exact (((continuousOn_id.mul (continuousOn_id.sub continuousOn_const)).mul hF).div_const _)
  · have e : (fun t ↦ kerF₁₁ α t a b) = fun t ↦ α * t * a ^ ((1 - α) / 2) * kerF α t a b *
        (t * a ^ ((1 - α) / 2) * (α - 1) - (1 + α) / 2 * (1 - t) * b ^ ((1 - α) / 2)) /
          (a ^ 2 * (t * a ^ ((1 - α) / 2) + (1 - t) * b ^ ((1 - α) / 2)) ^ 2) :=
      funext fun t ↦ kerF₁₁_of_ne h
    rw [e]
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht ↦ ?_
    have := kerMix_pos (α := α) ht ha hb
    unfold kerMix at this
    positivity

theorem intervalIntegrable_kerF (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t ↦ kerF α t a b) volume 0 1 :=
  (continuousOn_kerF ha hb).intervalIntegrable_of_Icc zero_le_one

theorem intervalIntegrable_kerF₁ (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t ↦ kerF₁ α t a b) volume 0 1 :=
  (continuousOn_kerF₁ ha hb).intervalIntegrable_of_Icc zero_le_one

theorem intervalIntegrable_kerF₁₁ (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t ↦ kerF₁₁ α t a b) volume 0 1 :=
  (continuousOn_kerF₁₁ ha hb).intervalIntegrable_of_Icc zero_le_one

theorem kerInt_pos (hα₁ : -1 < α) (ha : 0 < a) (hb : 0 < b) : 0 < kerInt α a b :=
  mul_pos (by linarith) (intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_kerF ha hb) (fun t ht ↦ kerF_pos (Ioo_subset_Icc_self ht) ha hb)
    zero_lt_one)

theorem kerInt_comm (a b : ℝ) : kerInt α a b = kerInt α b a := by
  rw [kerInt, kerInt]
  congr 1
  simpa [kerF_symm] using intervalIntegral.integral_comp_sub_left (a := 0) (b := 1)
    (fun t ↦ kerF α t b a) (1 : ℝ)

theorem kerD_nonneg (hα₀ : 0 ≤ α) (ha : 0 < a) (hb : 0 < b) : 0 ≤ kerD α a b :=
  mul_nonneg (by linarith) (intervalIntegral.integral_nonneg zero_le_one fun _ ht ↦
    kerF₁_nonneg ht ha hb hα₀)

/-- An integral over `[0, 1]` of a nonpositive continuous function is nonpositive. -/
theorem integral_nonpos_of_le {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, f t ≤ 0) : ∫ t in (0 : ℝ)..1, f t ≤ 0 := by
  have := intervalIntegral.integral_mono_on zero_le_one hf intervalIntegrable_const h
  simpa using this

theorem kerD_nonpos (hα₁ : -1 < α) (hα : α ≤ 0) (ha : 0 < a) (hb : 0 < b) : kerD α a b ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (by linarith) (integral_nonpos_of_le
    (intervalIntegrable_kerF₁ ha hb) fun _ ht ↦ kerF₁_nonpos ht ha hb hα)

theorem kerDD_nonpos (hα₀ : 0 ≤ α) (hα : α ≤ 1) (ha : 0 < a) (hb : 0 < b) : kerDD α a b ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (by linarith) (integral_nonpos_of_le
    (intervalIntegrable_kerF₁₁ ha hb) fun _ ht ↦ kerF₁₁_nonpos ht ha hb hα₀ hα)

theorem kerDD_nonneg (hα₁ : -1 < α) (hα : α ≤ 0) (ha : 0 < a) (hb : 0 < b) : 0 ≤ kerDD α a b :=
  mul_nonneg (by linarith) (intervalIntegral.integral_nonneg zero_le_one fun _ ht ↦
    kerF₁₁_nonneg ht ha hb hα₁.le hα)

/-- A function with a nonnegative derivative on `(0, ∞)` is monotone there. -/
theorem monotoneOn_Ioi_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (h : ∀ x, 0 < x → 0 ≤ f' x) : MonotoneOn f (Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    (fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt) ?_ ?_
  · rw [interior_Ioi]
    exact fun x hx ↦ (hf x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro x hx
    rw [(hf x hx).deriv]
    exact h x hx

/-- A function with a nonpositive derivative on `(0, ∞)` is antitone there. -/
theorem antitoneOn_Ioi_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (h : ∀ x, 0 < x → f' x ≤ 0) : AntitoneOn f (Ioi 0) := by
  have := monotoneOn_Ioi_of_hasDerivAt (f := fun x ↦ -f x) (f' := fun x ↦ -f' x)
    (fun x hx ↦ (hf x hx).neg) fun x hx ↦ neg_nonneg.2 (h x hx)
  exact fun x hx z hz hxz ↦ neg_le_neg_iff.1 (this hx hz hxz)

theorem kerInt_le_kerInt (hα₀ : 0 ≤ α) (hb : 0 < b) (hab : b ≤ a) (hy : 0 < y) :
    kerInt α b y ≤ kerInt α a y :=
  monotoneOn_Ioi_of_hasDerivAt (fun _ hx ↦ hasDerivAt_kerInt hx hy)
    (fun _ hx ↦ kerD_nonneg hα₀ hx hy) hb (lt_of_lt_of_le hb hab) hab

theorem kerInt_le_kerInt_of_neg (hα₁ : -1 < α) (hα : α ≤ 0) (hb : 0 < b) (hab : b ≤ a)
    (hy : 0 < y) : kerInt α a y ≤ kerInt α b y :=
  antitoneOn_Ioi_of_hasDerivAt (fun _ hx ↦ hasDerivAt_kerInt hx hy)
    (fun _ hx ↦ kerD_nonpos hα₁ hα hx hy) hb (lt_of_lt_of_le hb hab) hab

theorem kerD_le_kerD (hα₀ : 0 ≤ α) (hα : α ≤ 1) (hb : 0 < b) (hab : b ≤ a) (hy : 0 < y) :
    kerD α a y ≤ kerD α b y :=
  antitoneOn_Ioi_of_hasDerivAt (fun _ hx ↦ hasDerivAt_kerD hx hy)
    (fun _ hx ↦ kerDD_nonpos hα₀ hα hx hy) hb (lt_of_lt_of_le hb hab) hab

theorem kerD_le_kerD_of_neg (hα₁ : -1 < α) (hα : α ≤ 0) (hb : 0 < b) (hab : b ≤ a)
    (hy : 0 < y) : kerD α b y ≤ kerD α a y :=
  monotoneOn_Ioi_of_hasDerivAt (fun _ hx ↦ hasDerivAt_kerD hx hy)
    (fun _ hx ↦ kerDD_nonneg hα₁ hα hx hy) hb (lt_of_lt_of_le hb hab) hab

/-- **The swap inequality for `0 ≤ α ≤ 1`**: `K₁(a, b) ≤ K₁(b, a)` for `a ≥ b`. -/
theorem kerD_le_kerD_swap (hα₀ : 0 ≤ α) (hα : α ≤ 1) (hb : 0 < b) (hab : b ≤ a) :
    kerD α a b ≤ kerD α b a := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  exact mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_on zero_le_one
    (intervalIntegrable_kerF₁ ha hb) (intervalIntegrable_kerF₁ hb ha)
    fun t ht ↦ kerF₁_le_kerF₁_swap ht hb hα₀ hα hab) (by linarith)

/-- **The swap inequality for `-1 < α < 0`**: `K₁(b, a) ≤ K₁(a, b)` for `a ≥ b`. -/
theorem kerD_swap_le_kerD (hα₁ : -1 < α) (hα : α < 0) (hb : 0 < b) (hab : b ≤ a) :
    kerD α b a ≤ kerD α a b := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  set φ : ℝ → ℝ := fun t ↦ kerF₁ α t a b - kerF₁ α t b a
  have hφ : IntervalIntegrable φ volume 0 1 :=
    (intervalIntegrable_kerF₁ ha hb).sub (intervalIntegrable_kerF₁ hb ha)
  have hφ' : IntervalIntegrable (fun t ↦ φ (1 - t)) volume 0 1 :=
    hφ.comp_sub_left 1 |>.mono_set (by simp)
  have e1 : ∫ t in (0 : ℝ)..1, φ (1 - t) = ∫ t in (0 : ℝ)..1, φ t := by
    simp
  have h2 : 0 ≤ ∫ t in (0 : ℝ)..1, (φ t + φ (1 - t)) :=
    intervalIntegral.integral_nonneg zero_le_one fun t ht ↦
      kerF₁_swap_pair_nonneg ht hb hα₁ hα hab
  rw [intervalIntegral.integral_add hφ hφ', e1] at h2
  have h3 : 0 ≤ ∫ t in (0 : ℝ)..1, φ t := by linarith
  rw [intervalIntegral.integral_sub (intervalIntegrable_kerF₁ ha hb)
    (intervalIntegrable_kerF₁ hb ha)] at h3
  exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

/-- `K₁² ≤ K K₁₁` for `-1 < α ≤ 0`, by the discriminant. -/
theorem kerD_sq_le (hα₁ : -1 < α) (hα : α ≤ 0) (ha : 0 < a) (hb : 0 < b) :
    kerD α a b ^ 2 ≤ kerInt α a b * kerDD α a b := by
  have hq : ∀ l : ℝ, 0 ≤ kerInt α a b * (l * l) + 2 * kerD α a b * l + kerDD α a b := by
    intro l
    have hpt : ∀ t ∈ Icc (0 : ℝ) 1,
        0 ≤ l * l * kerF α t a b + 2 * l * kerF₁ α t a b + kerF₁₁ α t a b := by
      intro t ht
      have hF := kerF_pos (α := α) ht ha hb
      have h := kerF₁_sq_le ht ha hb hα₁.le hα
      have : 0 ≤ kerF α t a b * (l * l * kerF α t a b + 2 * l * kerF₁ α t a b + kerF₁₁ α t a b) :=
        by nlinarith [sq_nonneg (l * kerF α t a b + kerF₁ α t a b)]
      exact nonneg_of_mul_nonneg_right (by linarith) hF
    have hi := intervalIntegral.integral_nonneg (μ := volume) zero_le_one hpt
    rw [intervalIntegral.integral_add (((intervalIntegrable_kerF ha hb).const_mul _).add
        ((intervalIntegrable_kerF₁ ha hb).const_mul _)) (intervalIntegrable_kerF₁₁ ha hb),
      intervalIntegral.integral_add ((intervalIntegrable_kerF ha hb).const_mul _)
        ((intervalIntegrable_kerF₁ ha hb).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
    have hc : 0 ≤ (1 + α) / 2 := by linarith
    have := mul_nonneg hc hi
    simp only [kerInt, kerD, kerDD]
    nlinarith
  have := discrim_le_zero hq
  rw [discrim] at this
  nlinarith

/-- **Log-convexity of the kernel** for `-1 < α < 0`: `K₁(b, y) K(a, y) ≤ K₁(a, y) K(b, y)` for
`a ≥ b`, i.e. `K₁/K` increases in the first argument. -/
theorem kerD_mul_kerInt_le (hα₁ : -1 < α) (hα : α ≤ 0) (hb : 0 < b) (hab : b ≤ a)
    (hy : 0 < y) : kerD α b y * kerInt α a y ≤ kerD α a y * kerInt α b y := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have hmono : MonotoneOn (fun x ↦ kerD α x y / kerInt α x y) (Ioi 0) := by
    refine monotoneOn_Ioi_of_hasDerivAt (f' := fun x ↦
      (kerDD α x y * kerInt α x y - kerD α x y * kerD α x y) / kerInt α x y ^ 2)
      (fun x hx ↦ (hasDerivAt_kerD hx hy).div (hasDerivAt_kerInt hx hy)
        (kerInt_pos hα₁ hx hy).ne') fun x hx ↦ ?_
    have := kerD_sq_le hα₁ hα hx hy
    exact div_nonneg (by nlinarith) (sq_nonneg _)
  have h := hmono hb ha hab
  simp only at h
  rwa [div_le_div_iff₀ (kerInt_pos hα₁ hb hy) (kerInt_pos hα₁ ha hy)] at h

theorem integral_mul_one_sub : ∫ t in (0 : ℝ)..1, t * (1 - t) = 1 / 6 := by
  have e : (fun t : ℝ ↦ t * (1 - t)) = fun t ↦ t - t ^ 2 := funext fun t ↦ by ring
  rw [e, intervalIntegral.integral_sub (f := fun t : ℝ ↦ t) (g := fun t : ℝ ↦ t ^ 2)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), integral_id, integral_pow]
  norm_num

/-- **Lemma L1**: `K₁₁(s, y) ≤ -c (c α y^(α-1)/s)/6` for `0 < s ≤ y` and `0 < α ≤ 1`. -/
theorem kerDD_le (hα₀ : 0 < α) (hα : α ≤ 1) {s : ℝ} (hs : 0 < s) (hsy : s ≤ y) :
    kerDD α s y ≤ -((1 + α) / 2 * ((1 + α) / 2 * α * y ^ (α - 1) / s) / 6) := by
  have hy : 0 < y := lt_of_lt_of_le hs hsy
  have hI : IntervalIntegrable
      (fun t : ℝ ↦ -((1 + α) / 2 * α * y ^ (α - 1) / s) * (t * (1 - t))) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_mono_on zero_le_one (intervalIntegrable_kerF₁₁ hs hy) hI
    fun t ht ↦ (kerF₁₁_le ht hα₀ hα hs hsy).trans_eq (by ring)
  rw [intervalIntegral.integral_const_mul, integral_mul_one_sub] at h
  have hc : 0 ≤ (1 + α) / 2 := by linarith
  have := mul_le_mul_of_nonneg_left h hc
  simp only [kerDD]
  linarith

/-- **The monotonicity behind `Ψ_H ≤ 0`**: for `0 < α ≤ 1` and `0 < b ≤ a ≤ y`,
`c(1+α)(aᵅ - bᵅ)(yᵅ - aᵅ - bᵅ) - c(1+2α)(a²ᵅ - b²ᵅ) + y¹⁺ᵅ(K₁(a, y) - K₁(b, y)) ≤ 0`. This is
`g(a) ≤ g(b)` for `g(s) = c(1+α) yᵅ sᵅ - c(2+3α) s²ᵅ + y¹⁺ᵅ K₁(s, y)`, whose derivative is
`≤ (cα/s)((1+α) sᵅ yᵅ - (4+6α) s²ᵅ - (1+α) y²ᵅ/12) ≤ 0` by L1. -/
theorem kerG_nonpos (hα₀ : 0 < α) (hα : α ≤ 1) (hb : 0 < b) (hab : b ≤ a) (hay : a ≤ y) :
    (1 + α) / 2 * (1 + α) * (a ^ α - b ^ α) * (y ^ α - a ^ α - b ^ α) -
        (1 + α) / 2 * (1 + 2 * α) * ((a ^ α) ^ 2 - (b ^ α) ^ 2) +
      y ^ (1 + α) * (kerD α a y - kerD α b y) ≤ 0 := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have hy : 0 < y := lt_of_lt_of_le ha hay
  set c := (1 + α) / 2 with hc
  set g : ℝ → ℝ := fun s ↦ c * (1 + α) * y ^ α * s ^ α - c * (2 + 3 * α) * (s ^ α) ^ 2 +
    y ^ (1 + α) * kerD α s y
  set g' : ℝ → ℝ := fun s ↦ c * (1 + α) * y ^ α * (α * (s ^ α / s)) -
    c * (2 + 3 * α) * (2 * s ^ α * (α * (s ^ α / s))) + y ^ (1 + α) * kerDD α s y
  have hg : ∀ s, 0 < s → HasDerivAt g (g' s) s := fun s hs ↦ by
    have hp := Real.hasDerivAt_rpow_const (p := α) (Or.inl hs.ne')
    rw [Real.rpow_sub_one hs.ne'] at hp
    have := ((hp.const_mul (c * (1 + α) * y ^ α)).sub ((hp.pow 2).const_mul
      (c * (2 + 3 * α)))).add ((hasDerivAt_kerD (α := α) hs hy).const_mul (y ^ (1 + α)))
    convert this using 1
    simp only [g', Nat.cast_ofNat]
    ring
  have hg'le : ∀ s ∈ Ioo 0 y, g' s ≤ 0 := fun s hs ↦ by
    have hD := kerDD_le hα₀ hα hs.1 hs.2.le
    have hX := Real.rpow_pos_of_pos hs.1 α
    have hY := Real.rpow_pos_of_pos hy α
    have hYY : y ^ (1 + α) * y ^ (α - 1) = y ^ α * y ^ α := by
      rw [← Real.rpow_add hy, ← Real.rpow_add hy]
      ring_nf
    have hyp := Real.rpow_pos_of_pos hy (1 + α)
    have h1 : y ^ (1 + α) * kerDD α s y ≤ -(c * (c * α * (y ^ α * y ^ α) / s) / 6) := by
      have := mul_le_mul_of_nonneg_left hD hyp.le
      have e : y ^ (1 + α) * -((1 + α) / 2 * ((1 + α) / 2 * α * y ^ (α - 1) / s) / 6) =
          -(c * (c * α * (y ^ (1 + α) * y ^ (α - 1)) / s) / 6) := by rw [hc]; ring
      rw [e, hYY] at this
      exact this
    have h2 : g' s ≤ c * α / s * ((1 + α) * s ^ α * y ^ α - (4 + 6 * α) * (s ^ α) ^ 2 -
        (1 + α) * (y ^ α) ^ 2 / 12) := by
      simp only [g']
      have e : c * (1 + α) * y ^ α * (α * (s ^ α / s)) -
          c * (2 + 3 * α) * (2 * s ^ α * (α * (s ^ α / s))) -
            (c * (c * α * (y ^ α * y ^ α) / s) / 6)
          = c * α / s * ((1 + α) * s ^ α * y ^ α - (4 + 6 * α) * (s ^ α) ^ 2 -
            (1 + α) * (y ^ α) ^ 2 / 12) := by rw [hc]; field_simp; ring
      linarith
    have h3 : (1 + α) * s ^ α * y ^ α - (4 + 6 * α) * (s ^ α) ^ 2 -
        (1 + α) * (y ^ α) ^ 2 / 12 ≤ 0 := by
      nlinarith [sq_nonneg (y ^ α - 6 * s ^ α), mul_pos hX hX]
    have h4 : 0 ≤ c * α / s := by rw [hc]; have := hs.1; positivity
    nlinarith
  have hanti : AntitoneOn g (Ioc 0 y) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioc 0 y)
      (fun x hx ↦ (hg x hx.1).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Ioc]
      exact fun x hx ↦ (hg x hx.1).differentiableAt.differentiableWithinAt
    · rw [interior_Ioc]
      intro x hx
      rw [(hg x hx.1).deriv]
      exact hg'le x hx
  have h := hanti ⟨hb, hab.trans hay⟩ ⟨ha, hay⟩ hab
  simp only [g] at h
  nlinarith

end Integrated

end AlphaCurvature.Quantum
