/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import AlphaCurvature.ForMathlib.ParametricIntervalIntegral
import AlphaCurvature.Quantum.ClosedForm

/-!
# The curvature kernel as a power-mean integral

With `e = (1 - α)/2 = 1/p`, `β = 2α/(1 - α) = α/e` and `c = (1 + α)/2`, the curvature kernel
`K = curvKernel α` of the quantum α-geometry is, for `a, b > 0` and `-1 < α ≤ 1`,

  `K(a, b) = c ∫₀¹ (t aᵉ + (1 - t) bᵉ)^β dt`  (`α < 1`),  `K(a, b) = ∫₀¹ aᵗ b¹⁻ᵗ dt`  (`α = 1`),

the integral of the `α`-th power of a weighted power mean of order `e` (`curvKernel_eq_kerInt`).
The integrand `kerF` is smooth on the positive quadrant, so differentiation under the integral
sign gives the partial derivative `K₁ = kerD` and the second partial derivative `K₁₁ = kerDD` in
the first argument, with integrands `kerF₁` and `kerF₁₁` written in terms of `kerF` itself, and
the derivative of `K` along every line (`hasDerivAt_kerInt_line`).
-/

open Set Filter MeasureTheory
open scoped Topology Interval

namespace AlphaCurvature.Quantum

variable {α : ℝ}

/-! ### The integrand -/

/-- The weighted arithmetic mean `t aᵉ + (1 - t) bᵉ` of the `e`-th powers, `e = (1 - α)/2`. -/
noncomputable def kerMix (α t a b : ℝ) : ℝ :=
  t * a ^ ((1 - α) / 2) + (1 - t) * b ^ ((1 - α) / 2)

/-- **The integrand of the curvature kernel**: `(t aᵉ + (1 - t) bᵉ)^β`, and `aᵗ b¹⁻ᵗ` at `α = 1`. -/
noncomputable def kerF (α t a b : ℝ) : ℝ :=
  if α = 1 then a ^ t * b ^ (1 - t) else kerMix α t a b ^ (2 * α / (1 - α))

/-- The derivative of `kerF` in `a`. -/
noncomputable def kerF₁ (α t a b : ℝ) : ℝ :=
  if α = 1 then t * kerF α t a b / a
  else α * t * a ^ ((1 - α) / 2) * kerF α t a b / (a * kerMix α t a b)

/-- The second derivative of `kerF` in `a`. -/
noncomputable def kerF₁₁ (α t a b : ℝ) : ℝ :=
  if α = 1 then t * (t - 1) * kerF α t a b / a ^ 2
  else α * t * a ^ ((1 - α) / 2) * kerF α t a b *
      (t * a ^ ((1 - α) / 2) * (α - 1) - (1 + α) / 2 * (1 - t) * b ^ ((1 - α) / 2)) /
    (a ^ 2 * kerMix α t a b ^ 2)

/-- The kernel as an integral, `c ∫₀¹ kerF`. -/
noncomputable def kerInt (α a b : ℝ) : ℝ :=
  (1 + α) / 2 * ∫ t in (0 : ℝ)..1, kerF α t a b

/-- **The partial derivative `K₁`** of the kernel in its first argument. -/
noncomputable def kerD (α a b : ℝ) : ℝ :=
  (1 + α) / 2 * ∫ t in (0 : ℝ)..1, kerF₁ α t a b

/-- The second partial derivative `K₁₁` of the kernel in its first argument. -/
noncomputable def kerDD (α a b : ℝ) : ℝ :=
  (1 + α) / 2 * ∫ t in (0 : ℝ)..1, kerF₁₁ α t a b

section Integrand

variable {t a b : ℝ}

theorem kerF_one : kerF 1 t a b = a ^ t * b ^ (1 - t) := by simp [kerF]

theorem kerF_of_ne (hα : α ≠ 1) : kerF α t a b = kerMix α t a b ^ (2 * α / (1 - α)) := by
  simp [kerF, hα]

theorem kerF₁_one : kerF₁ 1 t a b = t * kerF 1 t a b / a := by simp [kerF₁]

theorem kerF₁_of_ne (hα : α ≠ 1) :
    kerF₁ α t a b = α * t * a ^ ((1 - α) / 2) * kerF α t a b / (a * kerMix α t a b) := by
  simp [kerF₁, hα]

theorem kerF₁₁_one : kerF₁₁ 1 t a b = t * (t - 1) * kerF 1 t a b / a ^ 2 := by simp [kerF₁₁]

theorem kerF₁₁_of_ne (hα : α ≠ 1) :
    kerF₁₁ α t a b = α * t * a ^ ((1 - α) / 2) * kerF α t a b *
      (t * a ^ ((1 - α) / 2) * (α - 1) - (1 + α) / 2 * (1 - t) * b ^ ((1 - α) / 2)) /
        (a ^ 2 * kerMix α t a b ^ 2) := by
  simp [kerF₁₁, hα]

theorem kerMix_pos (ht : t ∈ Icc (0 : ℝ) 1) (ha : 0 < a) (hb : 0 < b) : 0 < kerMix α t a b := by
  have h1 := Real.rpow_pos_of_pos ha ((1 - α) / 2)
  have h2 := Real.rpow_pos_of_pos hb ((1 - α) / 2)
  rcases ht.1.eq_or_lt with rfl | ht0
  · simpa [kerMix] using h2
  · have : 0 ≤ 1 - t := by linarith [ht.2]
    unfold kerMix
    positivity

theorem kerF_pos (ht : t ∈ Icc (0 : ℝ) 1) (ha : 0 < a) (hb : 0 < b) : 0 < kerF α t a b := by
  unfold kerF
  split_ifs
  · positivity
  · exact Real.rpow_pos_of_pos (kerMix_pos ht ha hb) _

theorem kerMix_symm : kerMix α (1 - t) b a = kerMix α t a b := by
  simp only [kerMix]
  ring

/-- The integrand is symmetric under `(t, a, b) ↦ (1 - t, b, a)`. -/
theorem kerF_symm : kerF α (1 - t) b a = kerF α t a b := by
  unfold kerF
  split_ifs
  · rw [sub_sub_cancel, mul_comm]
  · rw [kerMix_symm]

theorem kerF_self (ha : 0 < a) (hα : α ≠ 1) : kerF α t a a = a ^ α := by
  have h1 : 1 - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  simp only [kerF, hα, ↓reduceIte, kerMix, ← add_mul, add_sub_cancel, one_mul]
  rw [← Real.rpow_mul ha.le]
  congr 1
  field_simp

theorem kerF_self_one (ha : 0 < a) : kerF 1 t a a = a := by
  simp only [kerF, ↓reduceIte, ← Real.rpow_add ha, add_sub_cancel, Real.rpow_one]

end Integrand

/-! ### The representation -/

section Representation

variable {a b : ℝ}

theorem amariKernel_one : amariKernel 1 a b = logKernel a b := by simp [amariKernel]

/-- The power-mean integral at `α < 1`: `∫₀¹ (t A + (1 - t) B)^β dt` with `A = aᵉ ≠ B = bᵉ`. -/
theorem integral_kerF_of_ne (hα₁ : -1 < α) (hα : α < 1) (ha : 0 < a) (hb : 0 < b)
    (hab : a ^ ((1 - α) / 2) ≠ b ^ ((1 - α) / 2)) :
    ∫ t in (0 : ℝ)..1, kerF α t a b =
      (a ^ ((1 + α) / 2) - b ^ ((1 + α) / 2)) /
        ((1 + α) / (1 - α) * (a ^ ((1 - α) / 2) - b ^ ((1 - α) / 2))) := by
  set A := a ^ ((1 - α) / 2)
  set B := b ^ ((1 - α) / 2)
  have hA : 0 < A := Real.rpow_pos_of_pos ha _
  have hB : 0 < B := Real.rpow_pos_of_pos hb _
  have h1 : 1 - α ≠ 0 := by linarith
  have hβ : 2 * α / (1 - α) + 1 = (1 + α) / (1 - α) := by field_simp; ring
  have hβ0 : (1 + α) / (1 - α) ≠ 0 := div_ne_zero (by linarith) h1
  have hAB : A - B ≠ 0 := sub_ne_zero.2 hab
  have hm : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < t * A + (1 - t) * B := fun t ht ↦ by
    rw [uIcc_of_le zero_le_one] at ht
    exact kerMix_pos (α := α) ht ha hb
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun t ↦ (t * A + (1 - t) * B) ^ ((1 + α) / (1 - α)) / ((1 + α) / (1 - α) * (A - B)))
      (kerF α t a b) t := fun t ht ↦ by
    have hl : HasDerivAt (fun t ↦ t * A + (1 - t) * B) (A - B) t := by
      have := ((hasDerivAt_id' t).const_mul (A - B)).add_const B
      convert this using 1
      · ext s
        ring
      · ring
    have := (hl.rpow_const (p := (1 + α) / (1 - α)) (Or.inl (hm t ht).ne')).div_const
      ((1 + α) / (1 - α) * (A - B))
    convert this using 1
    rw [show kerF α t a b = (t * A + (1 - t) * B) ^ (2 * α / (1 - α)) by
      simp only [kerF, hα.ne, ↓reduceIte, kerMix]; rfl, ← hβ, add_sub_cancel_right]
    have h2 : 2 * α + (1 - α) ≠ 0 := by linarith
    field_simp
  have hcont : ContinuousOn (fun t ↦ kerF α t a b) (uIcc 0 1) := by
    have : ∀ t ∈ uIcc (0 : ℝ) 1, kerF α t a b = (t * A + (1 - t) * B) ^ (2 * α / (1 - α)) :=
      fun t _ ↦ by simp only [kerF, hα.ne, ↓reduceIte, kerMix]; rfl
    refine ContinuousOn.congr ?_ this
    exact ContinuousOn.rpow_const (by fun_prop) fun t ht ↦ Or.inl (hm t ht).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [one_mul, sub_self, zero_mul, add_zero, zero_add, sub_zero, ← sub_div]
  have e : ∀ x : ℝ, 0 < x → (x ^ ((1 - α) / 2)) ^ ((1 + α) / (1 - α)) = x ^ ((1 + α) / 2) :=
    fun x hx ↦ by
      rw [← Real.rpow_mul hx.le]
      congr 1
      field_simp
  rw [e a ha, e b hb]

/-- The logarithmic-mean integral at `α = 1`: `∫₀¹ aᵗ b¹⁻ᵗ dt = (a - b)/(log a - log b)`. -/
theorem integral_kerF_one_of_ne (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    ∫ t in (0 : ℝ)..1, kerF 1 t a b = (a - b) / (Real.log a - Real.log b) := by
  have hl : Real.log a - Real.log b ≠ 0 :=
    sub_ne_zero.2 fun e ↦ hab (Real.log_injOn_pos ha hb e)
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun t ↦ a ^ t * b ^ (1 - t) / (Real.log a - Real.log b)) (kerF 1 t a b) t := fun t _ ↦ by
    have h1 := (Real.hasStrictDerivAt_const_rpow ha t).hasDerivAt
    have h2 := (Real.hasStrictDerivAt_const_rpow hb (1 - t)).hasDerivAt.comp t
      ((hasDerivAt_id t).const_sub 1)
    have := (h1.mul h2).div_const (Real.log a - Real.log b)
    convert this using 1
    · funext x
      simp
    · simp only [kerF_one, Function.comp_apply]
      field_simp
      ring
  have hcont : ContinuousOn (fun t ↦ kerF 1 t a b) (uIcc 0 1) := by
    simp only [kerF_one]
    exact ((continuous_const.rpow continuous_id fun _ ↦ Or.inl ha.ne').mul
      (continuous_const.rpow (continuous_const.sub continuous_id)
        fun _ ↦ Or.inl hb.ne')).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [Real.rpow_one, sub_zero, Real.rpow_zero, mul_one, sub_self, one_mul]
  rw [← sub_div]

/-- **The power-mean representation of the curvature kernel**: for `a, b > 0` and `-1 < α ≤ 1`,
`curvKernel α a b = c ∫₀¹ (t aᵉ + (1 - t) bᵉ)^β dt`. -/
theorem curvKernel_eq_kerInt (hα₁ : -1 < α) (hα : α ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    curvKernel α a b = kerInt α a b := by
  rcases eq_or_ne a b with rfl | hab
  · rw [curvKernel_self ha, kerInt]
    congr 1
    rcases hα.eq_or_lt with rfl | hα
    · simp only [kerF_self_one ha, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
        one_mul, Real.rpow_one]
    · simp only [kerF_self ha hα.ne, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
        one_mul]
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  rcases hα.eq_or_lt with rfl | hα
  · rw [kerInt, integral_kerF_one_of_ne ha hb hab, curvKernel, amariKernel_one,
      powKernel_of_ne hab, logKernel_of_ne hab]
    simp only [Real.rpow_one, show (1 + 1 : ℝ) / 2 = 1 by norm_num, one_mul]
    rw [div_self hab', one_div, inv_div]
  have he : 0 < (1 - α) / 2 := by linarith
  have hne : a ^ ((1 - α) / 2) ≠ b ^ ((1 - α) / 2) := fun e ↦
    hab ((Real.rpow_left_inj ha.le hb.le he.ne').1 e)
  have hne' : a ^ ((1 - α) / 2) - b ^ ((1 - α) / 2) ≠ 0 := sub_ne_zero.2 hne
  have h1 : 1 - α ≠ 0 := by linarith
  have h2 : 1 + α ≠ 0 := by linarith
  rw [kerInt, integral_kerF_of_ne hα₁ hα ha hb hne, curvKernel, amariKernel,
    powKernel_of_ne hab, powKernel_of_ne hab]
  simp only [hα.ne, ↓reduceIte]
  field_simp

end Representation

/-! ### Smoothness of the integrand -/

section Smooth

variable {fa fb : ℝ × ℝ → ℝ} {z : ℝ × ℝ}

theorem contDiffAt_kerMix (hfa : ContDiffAt ℝ 1 fa z) (hfb : ContDiffAt ℝ 1 fb z)
    (ha : 0 < fa z) (hb : 0 < fb z) :
    ContDiffAt ℝ 1 (fun p ↦ kerMix α p.2 (fa p) (fb p)) z := by
  unfold kerMix
  exact (contDiffAt_snd.mul (hfa.rpow_const_of_ne ha.ne')).add
    ((contDiffAt_const.sub contDiffAt_snd).mul (hfb.rpow_const_of_ne hb.ne'))

theorem contDiffAt_kerF (hfa : ContDiffAt ℝ 1 fa z) (hfb : ContDiffAt ℝ 1 fb z)
    (ha : 0 < fa z) (hb : 0 < fb z) (ht : z.2 ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ 1 (fun p ↦ kerF α p.2 (fa p) (fb p)) z := by
  by_cases hα : α = 1
  · subst hα
    simp only [kerF_one]
    exact (hfa.rpow contDiffAt_snd ha.ne').mul (hfb.rpow (contDiffAt_const.sub contDiffAt_snd)
      hb.ne')
  · simp only [kerF_of_ne hα]
    exact (contDiffAt_kerMix hfa hfb ha hb).rpow_const_of_ne (kerMix_pos ht ha hb).ne'

theorem contDiffAt_kerF₁ {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ ↦ kerF₁ α p.2 p.1 b) (a, t) := by
  have hF := contDiffAt_kerF (α := α) (fa := Prod.fst) (fb := fun _ ↦ b) (z := (a, t))
    contDiffAt_fst contDiffAt_const ha hb ht
  by_cases hα : α = 1
  · subst hα
    simp only [kerF₁_one]
    exact (contDiffAt_snd.mul hF).div contDiffAt_fst ha.ne'
  · simp only [kerF₁_of_ne hα]
    exact (((contDiffAt_const.mul contDiffAt_snd).mul
      (contDiffAt_fst.rpow_const_of_ne ha.ne')).mul hF).div
      (contDiffAt_fst.mul (contDiffAt_kerMix (fa := Prod.fst) (fb := fun _ ↦ b)
        contDiffAt_fst contDiffAt_const ha hb))
      (mul_pos ha (kerMix_pos ht ha hb)).ne'

theorem continuousOn_kerF₁ {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (fun t ↦ kerF₁ α t a b) (Icc 0 1) := fun _ ht ↦
  ((contDiffAt_kerF₁ (α := α) ha hb ht).continuousAt.comp
    (f := fun s : ℝ ↦ (a, s))
    (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt

end Smooth

/-! ### Derivatives of the integrand -/

section Deriv

variable {t a b : ℝ}

theorem hasDerivAt_kerMix (ha : 0 < a) :
    HasDerivAt (fun x ↦ kerMix α t x b) (t * ((1 - α) / 2 * (a ^ ((1 - α) / 2) / a))) a := by
  have := ((Real.hasDerivAt_rpow_const (p := (1 - α) / 2) (Or.inl ha.ne')).const_mul t).add_const
    ((1 - t) * b ^ ((1 - α) / 2))
  rw [Real.rpow_sub_one ha.ne'] at this
  exact this

/-- `∂ₐ kerF = kerF₁`. -/
theorem hasDerivAt_kerF (ht : t ∈ Icc (0 : ℝ) 1) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun x ↦ kerF α t x b) (kerF₁ α t a b) a := by
  by_cases hα : α = 1
  · subst hα
    simp only [kerF_one, kerF₁_one]
    have := (Real.hasDerivAt_rpow_const (p := t) (Or.inl ha.ne')).mul_const (b ^ (1 - t))
    convert this using 1
    rw [Real.rpow_sub_one ha.ne']
    field_simp
  · simp only [kerF_of_ne hα, kerF₁_of_ne hα]
    have hm := kerMix_pos (α := α) ht ha hb
    have h1 : 1 - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
    have := (hasDerivAt_kerMix (α := α) (t := t) (b := b) ha).rpow_const
      (p := 2 * α / (1 - α)) (Or.inl hm.ne')
    convert this using 1
    rw [Real.rpow_sub_one hm.ne']
    field_simp

/-- `∂ₐ kerF₁ = kerF₁₁`. -/
theorem hasDerivAt_kerF₁ (ht : t ∈ Icc (0 : ℝ) 1) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun x ↦ kerF₁ α t x b) (kerF₁₁ α t a b) a := by
  have hF := hasDerivAt_kerF (α := α) ht ha hb
  by_cases hα : α = 1
  · subst hα
    simp only [kerF₁_one, kerF₁₁_one] at hF ⊢
    have := (hF.const_mul t).div (hasDerivAt_id a) ha.ne'
    convert this using 1
    · funext x
      simp only [Pi.div_apply, id_eq]
    · simp only [id_eq]
      field_simp
  · simp only [kerF₁_of_ne hα, kerF₁₁_of_ne hα] at hF ⊢
    have hm := kerMix_pos (α := α) ht ha hb
    have h1 : 1 - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
    have hu := Real.hasDerivAt_rpow_const (p := (1 - α) / 2) (Or.inl ha.ne')
    rw [Real.rpow_sub_one ha.ne'] at hu
    have := ((hu.const_mul (α * t)).mul hF).div
      ((hasDerivAt_id a).mul (hasDerivAt_kerMix (α := α) (t := t) (b := b) ha))
      (mul_pos ha hm).ne'
    convert this using 1
    · funext x
      simp only [Pi.mul_apply, Pi.div_apply, id_eq]
    · simp only [Pi.mul_apply, id_eq, kerMix]
      simp only [kerMix] at hm
      field_simp
      ring

/-- The derivative of the integrand along a line through `(a, b)`. -/
theorem hasDerivAt_kerF_line (ht : t ∈ Icc (0 : ℝ) 1) (ha : 0 < a) (hb : 0 < b) (va vb : ℝ) :
    HasDerivAt (fun s ↦ kerF α t (a + s * va) (b + s * vb))
      (va * kerF₁ α t a b + vb * kerF₁ α (1 - t) b a) 0 := by
  have hla : HasDerivAt (fun s ↦ a + s * va) va 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const va).const_add a
  have hlb : HasDerivAt (fun s ↦ b + s * vb) vb 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const vb).const_add b
  have ha' : a + 0 * va ≠ 0 := by simpa using ha.ne'
  have hb' : b + 0 * vb ≠ 0 := by simpa using hb.ne'
  by_cases hα : α = 1
  · subst hα
    simp only [kerF_one, kerF₁_one, sub_sub_cancel]
    have := (hla.rpow_const (p := t) (Or.inl ha')).mul (hlb.rpow_const (p := 1 - t) (Or.inl hb'))
    convert this using 1
    simp only [zero_mul, add_zero]
    rw [Real.rpow_sub_one ha.ne', show 1 - t - 1 = -t by ring, Real.rpow_neg hb.le,
      show b ^ (1 - t) = b / b ^ t by rw [Real.rpow_sub hb, Real.rpow_one] ]
    have := Real.rpow_pos_of_pos hb t
    field_simp
  · simp only [kerF_of_ne hα, kerF₁_of_ne hα, kerMix_symm]
    have hm := kerMix_pos (α := α) ht ha hb
    have h1 : 1 - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
    have hM : HasDerivAt (fun s ↦ kerMix α t (a + s * va) (b + s * vb))
        (t * (va * ((1 - α) / 2) * (a ^ ((1 - α) / 2) / a)) +
          (1 - t) * (vb * ((1 - α) / 2) * (b ^ ((1 - α) / 2) / b))) 0 := by
      have h := ((hla.rpow_const (p := (1 - α) / 2) (Or.inl ha')).const_mul t).add
        ((hlb.rpow_const (p := (1 - α) / 2) (Or.inl hb')).const_mul (1 - t))
      simp only [zero_mul, add_zero, Real.rpow_sub_one ha.ne', Real.rpow_sub_one hb.ne'] at h
      exact h
    have hm' : kerMix α t (a + 0 * va) (b + 0 * vb) ≠ 0 := by simpa using hm.ne'
    have := hM.rpow_const (p := 2 * α / (1 - α)) (Or.inl hm')
    convert this using 1
    simp only [zero_mul, add_zero]
    rw [Real.rpow_sub_one hm.ne']
    field_simp

end Deriv

/-! ### Differentiation under the integral sign -/

section Integral

/-- Differentiation under the integral sign over `[0, 1]`, for a scalar parameter. -/
theorem hasDerivAt_integral_of_contDiffAt {f : ℝ × ℝ → ℝ} {f' : ℝ → ℝ} {x : ℝ}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 f (x, t))
    (hf' : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun y ↦ f (y, t)) (f' t) x) :
    HasDerivAt (fun y ↦ ∫ t in (0 : ℝ)..1, f (y, t)) (∫ t in (0 : ℝ)..1, f' t) x := by
  have hf2 : ∀ t ∈ [[(0 : ℝ), 1]], ContDiffAt ℝ 1 f (x, t) := by
    rw [uIcc_of_le zero_le_one]
    exact hf
  have hD := hasFDerivAt_intervalIntegral_of_contDiffAt hf2
  have e := fderiv_intervalIntegral_apply_of_contDiffAt hf2 1
  rw [hD.fderiv] at e
  convert hD.hasDerivAt using 1
  rw [e]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp [(hf' t ht).hasFDerivAt.fderiv]

variable {a b : ℝ}

/-- `∂ₐ K = K₁`. -/
theorem hasDerivAt_kerInt (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun x ↦ kerInt α x b) (kerD α a b) a := by
  have h := hasDerivAt_integral_of_contDiffAt (f := fun p : ℝ × ℝ ↦ kerF α p.2 p.1 b)
    (f' := fun t ↦ kerF₁ α t a b) (x := a)
    (fun t ht ↦ contDiffAt_kerF (fa := Prod.fst) (fb := fun _ ↦ b) contDiffAt_fst
      contDiffAt_const ha hb ht)
    (fun t ht ↦ hasDerivAt_kerF ht ha hb)
  exact h.const_mul _

/-- `∂ₐ K₁ = K₁₁`. -/
theorem hasDerivAt_kerD (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun x ↦ kerD α x b) (kerDD α a b) a := by
  have h := hasDerivAt_integral_of_contDiffAt (f := fun p : ℝ × ℝ ↦ kerF₁ α p.2 p.1 b)
    (f' := fun t ↦ kerF₁₁ α t a b) (x := a) (fun t ht ↦ contDiffAt_kerF₁ ha hb ht)
    (fun t ht ↦ hasDerivAt_kerF₁ ht ha hb)
  exact h.const_mul _

/-- **The derivative of the kernel along a line**: `d/ds K(a + s vₐ, b + s v_b) = vₐ K₁(a, b) +
v_b K₁(b, a)` at `s = 0`. -/
theorem hasDerivAt_kerInt_line (ha : 0 < a) (hb : 0 < b) (va vb : ℝ) :
    HasDerivAt (fun s ↦ kerInt α (a + s * va) (b + s * vb))
      (va * kerD α a b + vb * kerD α b a) 0 := by
  have h := hasDerivAt_integral_of_contDiffAt
    (f := fun p : ℝ × ℝ ↦ kerF α p.2 (a + p.1 * va) (b + p.1 * vb))
    (f' := fun t ↦ va * kerF₁ α t a b + vb * kerF₁ α (1 - t) b a) (x := 0)
    (fun t ht ↦ contDiffAt_kerF (fa := fun p ↦ a + p.1 * va) (fb := fun p ↦ b + p.1 * vb)
      (by fun_prop) (by fun_prop) (by simpa using ha) (by simpa using hb) ht)
    (fun t ht ↦ hasDerivAt_kerF_line ht ha hb va vb)
  convert h.const_mul ((1 + α) / 2) using 1
  · rfl
  have i1 := ((continuousOn_kerF₁ (α := α) ha hb).mono
    (uIcc_of_le zero_le_one).subset).intervalIntegrable (μ := volume)
  have i2 := ((continuousOn_kerF₁ (α := α) hb ha).mono
    (uIcc_of_le zero_le_one).subset).intervalIntegrable (μ := volume)
  have e : ∫ t in (0 : ℝ)..1, kerF₁ α (1 - t) b a = ∫ t in (0 : ℝ)..1, kerF₁ α t b a := by
    simpa using intervalIntegral.integral_comp_sub_left (a := 0) (b := 1)
      (fun t ↦ kerF₁ α t b a) (1 : ℝ)
  rw [intervalIntegral.integral_add (i1.const_mul va)
    ((i2.comp_sub_left 1).const_mul vb |>.mono_set (by simp)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, e, kerD, kerD]
  ring

end Integral

end AlphaCurvature.Quantum
