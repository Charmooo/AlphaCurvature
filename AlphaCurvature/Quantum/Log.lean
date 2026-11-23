/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import AlphaCurvature.ForMathlib.ParametricIntervalIntegral

/-!
# The matrix logarithm as an integral

For a complex `d × d` matrix `x`, `matLog x = ∫₀¹ (x - 1) ((1 - s) x + s)⁻¹ ds`. At a positive
number `x` the integrand is `(x - 1)/((1 - s) x + s)`, with antiderivative `-log((1 - s) x + s)`,
so `matLog` is the logarithm on positive definite matrices (`matLog_diagonal` at a diagonal; any
positive definite Hermitian matrix is a unitary conjugate of one, and `matLog_conj`).

The integrand is smooth wherever the path `(1 - s) x + s` is invertible, for every `s ∈ [0, 1]`,
which holds near every positive definite matrix, so `matLog` is smooth there
(`contDiffAt_matLog`). Its derivative is `D matLog_x [B] = ∫₀¹ R B R ds` with
`R = ((1 - s) x + s)⁻¹` (`fderiv_matLog_apply`): differentiating the integrand gives
`B R - (1 - s)(x - 1) R B R`, and `((1 - s) x + s) - (1 - s)(x - 1) = 1`. At a diagonal matrix
this is the Daleckii–Krein formula for the logarithm,
`(D matLog [B])ᵢⱼ = (log λᵢ - log λⱼ)/(λᵢ - λⱼ) Bᵢⱼ` (`fderiv_matLog_diagonal_apply`).

The construction follows the Bogoliubov–Kubo–Mori form of the PetzCurvature library, whose
integrand is the derivative of this one.

## Main definitions

* `AlphaCurvature.Quantum.logPath`: the path `(1 - s) x + s`.
* `AlphaCurvature.Quantum.matLog`: the integral.
* `AlphaCurvature.Quantum.logKernel`: the first divided difference of `log`.

## Main statements

* `AlphaCurvature.Quantum.contDiffAt_matLog`: smoothness near a positive definite matrix.
* `AlphaCurvature.Quantum.fderiv_matLog_apply`: the derivative as an integral.
* `AlphaCurvature.Quantum.matLog_diagonal`, `AlphaCurvature.Quantum.fderiv_matLog_diagonal_apply`:
  the value and the derivative at a positive diagonal matrix.
* `AlphaCurvature.Quantum.matLog_conj`: equivariance under unitary conjugation.
-/

open scoped Matrix.Norms.L2Operator Topology Interval ComplexOrder
open Matrix ContinuousLinearMap Filter Set

namespace AlphaCurvature.Quantum

/-! ### The scalar integrals -/

section Scalar

variable {x y : ℝ}

theorem pathScalar_pos (hx : 0 < x) {s : ℝ} (hs : s ∈ uIcc (0 : ℝ) 1) : 0 < (1 - s) * x + s := by
  rw [uIcc_of_le zero_le_one] at hs
  rcases eq_or_lt_of_le hs.1 with rfl | h
  · simpa using hx
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith [hs.2]) hx.le) h

theorem hasDerivAt_pathScalar (x s : ℝ) : HasDerivAt (fun s : ℝ ↦ (1 - s) * x + s) (1 - x) s :=
  ((((hasDerivAt_id' s).const_sub 1).mul_const x).add (hasDerivAt_id' s)).congr_deriv (by ring)

theorem continuousOn_pathScalar_inv (hx : 0 < x) :
    ContinuousOn (fun s : ℝ ↦ ((1 - s) * x + s)⁻¹) (uIcc 0 1) :=
  (((continuous_const.sub continuous_id).mul continuous_const).add
    continuous_id).continuousOn.inv₀ fun _ hs ↦ (pathScalar_pos hx hs).ne'

/-- The **logarithm as an integral**: `∫₀¹ (x - 1)/((1 - s) x + s) ds = log x` for `x > 0`. -/
theorem integral_log (hx : 0 < x) :
    ∫ s in (0 : ℝ)..1, (x - 1) * ((1 - s) * x + s)⁻¹ = Real.log x := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s ↦ -Real.log ((1 - s) * x + s))
      ((x - 1) * ((1 - s) * x + s)⁻¹) s := by
    intro s hs
    refine ((hasDerivAt_pathScalar x s).log (pathScalar_pos hx hs).ne').neg.congr_deriv ?_
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (continuousOn_const.mul (continuousOn_pathScalar_inv hx)).intervalIntegrable]
  simp

/-- The **logarithmic kernel**, the first divided difference of `log`:
`(log x − log y)/(x − y)`, and `1/x` on the diagonal. -/
noncomputable def logKernel (x y : ℝ) : ℝ :=
  if x = y then x⁻¹ else (Real.log x - Real.log y) / (x - y)

theorem logKernel_self (x : ℝ) : logKernel x x = x⁻¹ := by simp [logKernel]

theorem logKernel_of_ne (h : x ≠ y) : logKernel x y = (Real.log x - Real.log y) / (x - y) := by
  simp [logKernel, h]

/-- The logarithmic kernel as an integral:
`∫₀¹ ds / (((1 - s) x + s) ((1 - s) y + s)) = logKernel x y`. -/
theorem integral_logKernel (hx : 0 < x) (hy : 0 < y) :
    ∫ s in (0 : ℝ)..1, ((1 - s) * x + s)⁻¹ * ((1 - s) * y + s)⁻¹ = logKernel x y := by
  have hc := ((continuousOn_pathScalar_inv hx).mul (continuousOn_pathScalar_inv hy))
  rcases eq_or_ne x y with rfl | hxy
  · have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s ↦ s / (x * ((1 - s) * x + s)))
        (((1 - s) * x + s)⁻¹ * ((1 - s) * x + s)⁻¹) s := by
      intro s hs
      have ha := pathScalar_pos hx hs
      refine ((hasDerivAt_id' s).div ((hasDerivAt_pathScalar x s).const_mul x)
        (mul_pos hx ha).ne').congr_deriv ?_
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable, logKernel_self]
    simp
  · have hyx : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
    have hxy' : x - y ≠ 0 := sub_ne_zero.2 hxy
    have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt
        (fun s ↦ (Real.log ((1 - s) * x + s) - Real.log ((1 - s) * y + s)) / (y - x))
        (((1 - s) * x + s)⁻¹ * ((1 - s) * y + s)⁻¹) s := by
      intro s hs
      have ha := pathScalar_pos hx hs
      have hb := pathScalar_pos hy hs
      refine ((((hasDerivAt_pathScalar x s).log ha.ne').sub
        ((hasDerivAt_pathScalar y s).log hb.ne')).div_const (y - x)).congr_deriv ?_
      have ha' : x * (1 - s) + s ≠ 0 := by rw [mul_comm]; exact ha.ne'
      have hb' : y * (1 - s) + s ≠ 0 := by rw [mul_comm]; exact hb.ne'
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable,
      logKernel_of_ne hxy]
    simp only [sub_self, zero_mul, zero_add, add_zero, one_mul, Real.log_one, zero_div,
      sub_zero]
    field_simp
    ring

end Scalar

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ### The path and the integral -/

/-- The path `(1 - s) x + s` from `x` (at `s = 0`) to `1` (at `s = 1`). -/
noncomputable def logPath (z : Matrix d d ℂ × ℝ) : Matrix d d ℂ :=
  (1 - z.2) • z.1 + z.2 • (1 : Matrix d d ℂ)

/-- The integrand `(x - 1) ((1 - s) x + s)⁻¹`. -/
noncomputable def logIntegrand (z : Matrix d d ℂ × ℝ) : Matrix d d ℂ :=
  (z.1 - 1) * (logPath z)⁻¹

/-- The **matrix logarithm** as the integral `∫₀¹ (x - 1) ((1 - s) x + s)⁻¹ ds`. -/
noncomputable def matLog (x : Matrix d d ℂ) : Matrix d d ℂ :=
  ∫ s in (0 : ℝ)..1, logIntegrand (x, s)

theorem contDiff_logPath {n : WithTop ℕ∞} : ContDiff ℝ n (logPath : Matrix d d ℂ × ℝ → _) :=
  ((contDiff_const.sub contDiff_snd).smul contDiff_fst).add (contDiff_snd.smul contDiff_const)

omit [Fintype d] in
/-- For positive definite `ρ` the path `(1 - s) ρ + s`, `s ∈ [0, 1]`, is positive definite. -/
theorem posDef_logPath {ρ : Matrix d d ℂ} (hρ : ρ.PosDef) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (logPath (ρ, s)).PosDef := by
  rcases lt_or_eq_of_le hs.2 with h | rfl
  · exact (hρ.smul (sub_pos.2 h)).add_posSemidef (PosSemidef.one.smul hs.1)
  · simpa [logPath] using PosDef.one

/-- For positive definite `ρ` the whole path is invertible. -/
theorem isUnit_logPath_of_posDef {ρ : Matrix d d ℂ} (hρ : ρ.PosDef) :
    ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (logPath (ρ, t)) :=
  fun _ ht ↦ (posDef_logPath hρ ht).isUnit

/-- Invertibility of the whole path is an open condition on `x`. -/
theorem eventually_isUnit_logPath {x : Matrix d d ℂ}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (logPath (x, t))) :
    ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (logPath (y, t)) :=
  isCompact_Icc.eventually_forall_of_forall_eventually fun t ht ↦
    (contDiff_logPath (n := 0)).continuous.continuousAt.eventually (Units.isOpen.mem_nhds (hx t ht))

/-- The integrand is smooth wherever the path is invertible. -/
theorem contDiffAt_logIntegrand {n : WithTop ℕ∞} {z : Matrix d d ℂ × ℝ}
    (hz : IsUnit (logPath z)) : ContDiffAt ℝ n logIntegrand z := by
  have h : (logIntegrand : Matrix d d ℂ × ℝ → _) =
      fun z ↦ (z.1 - 1) * Ring.inverse (logPath z) :=
    funext fun z ↦ by rw [logIntegrand, nonsing_inv_eq_ringInverse]
  rw [h]
  exact (contDiffAt_fst.sub contDiffAt_const).mul
    ((contDiffAt_ringInverse ℝ hz.unit).comp z contDiff_logPath.contDiffAt)

theorem contDiffAt_logIntegrand_of_mem {n : WithTop ℕ∞} {x : Matrix d d ℂ}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (logPath (x, t))) :
    ∀ t ∈ [[(0 : ℝ), 1]], ContDiffAt ℝ n logIntegrand (x, t) := fun t ht ↦
  contDiffAt_logIntegrand (hx t (by rwa [uIcc_of_le zero_le_one] at ht))

/-- `matLog` is smooth wherever the whole path is invertible. -/
theorem contDiffAt_matLog_of_isUnit {x : Matrix d d ℂ}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (logPath (x, t))) (n : ℕ) :
    ContDiffAt ℝ n matLog x :=
  contDiffAt_intervalIntegral_of_contDiffAt n (contDiffAt_logIntegrand_of_mem hx)

/-- **`matLog` is smooth** at a positive definite matrix. -/
theorem contDiffAt_matLog {ρ : Matrix d d ℂ} (hρ : ρ.PosDef) (n : ℕ) :
    ContDiffAt ℝ n matLog ρ :=
  contDiffAt_matLog_of_isUnit (isUnit_logPath_of_posDef hρ) n

theorem intervalIntegrable_logIntegrand {x : Matrix d d ℂ}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (logPath (x, t))) :
    IntervalIntegrable (fun t ↦ logIntegrand (x, t)) MeasureTheory.volume 0 1 :=
  (ContinuousOn.intervalIntegrable fun t ht ↦
    ((contDiffAt_logIntegrand_of_mem (n := 0) hx t ht).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt)

/-! ### The derivative -/

theorem fderiv_logIntegrand_apply {x : Matrix d d ℂ} {t : ℝ} (hz : IsUnit (logPath (x, t)))
    (B : Matrix d d ℂ) :
    fderiv ℝ (fun y ↦ logIntegrand (y, t)) x B =
      (logPath (x, t))⁻¹ * B * (logPath (x, t))⁻¹ := by
  set R := (logPath (x, t))⁻¹ with hR
  have hRi : Ring.inverse (logPath (x, t)) = R := (nonsing_inv_eq_ringInverse _).symm
  have hF : (fun y ↦ logIntegrand (y, t)) =
      fun y : Matrix d d ℂ ↦ (y - 1) * Ring.inverse (logPath (y, t)) :=
    funext fun y ↦ by simp [logIntegrand, nonsing_inv_eq_ringInverse]
  have hd : DifferentiableAt ℝ (fun y ↦ logIntegrand (y, t)) x :=
    ((contDiffAt_logIntegrand (n := 1) hz).comp x
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt one_ne_zero
  have h1 : HasDerivAt (fun ε : ℝ ↦ (fun y ↦ logIntegrand (y, t)) (x + ε • B))
      (fderiv ℝ (fun y ↦ logIntegrand (y, t)) x B) 0 :=
    hd.hasFDerivAt.hasLineDerivAt B
  rw [hF] at h1 ⊢
  have hP : HasDerivAt (fun ε : ℝ ↦ logPath (x + ε • B, t)) ((1 - t) • B) 0 := by
    have := ((((hasDerivAt_id (0 : ℝ)).smul_const B).const_add x).const_smul (1 - t)).add_const
      (t • (1 : Matrix d d ℂ))
    simpa [logPath] using this
  have hP0 : logPath (x + (0 : ℝ) • B, t) = ↑hz.unit := by simp
  have hu : (↑hz.unit⁻¹ : Matrix d d ℂ) = R := by
    rw [hR, nonsing_inv_eq_ringInverse, ← Ring.inverse_unit, IsUnit.unit_spec]
  have hI : HasDerivAt (fun ε : ℝ ↦ Ring.inverse (logPath (x + ε • B, t)))
      (-(R * ((1 - t) • B) * R)) 0 := by
    have h := hasFDerivAt_ringInverse (𝕜 := ℝ) hz.unit
    rw [← hP0] at h
    refine (h.comp_hasDerivAt (0 : ℝ) hP).congr_deriv ?_
    simp only [_root_.neg_apply, mulLeftRight_apply, hu]
  have hI0 : Ring.inverse (logPath (x + (0 : ℝ) • B, t)) = R := by simp [hRi]
  have hL : HasDerivAt (fun ε : ℝ ↦ x + ε • B - 1) B 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const B).const_add x).sub_const 1
  rw [h1.unique (hL.mul hI)]
  have hPR : logPath (x, t) * R = 1 :=
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hz)
  have key : logPath (x, t) - (1 - t) • (x - 1) = 1 := by
    simp only [logPath, smul_sub]
    module
  simp only [zero_smul, add_zero, hRi]
  calc B * R + (x - 1) * -(R * ((1 - t) • B) * R)
      = (logPath (x, t) * R) * B * R - (1 - t) • ((x - 1) * (R * B * R)) := by
        rw [hPR, one_mul, Matrix.mul_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
          ← sub_eq_add_neg]
    _ = (logPath (x, t) - (1 - t) • (x - 1)) * (R * B * R) := by
        simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = R * B * R := by rw [key, Matrix.one_mul]

/-- **The derivative of `matLog`**: `D matLog_x [B] = ∫₀¹ R B R ds`, `R = ((1 - s) x + s)⁻¹`,
wherever the whole path is invertible. -/
theorem fderiv_matLog_apply {x : Matrix d d ℂ}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (logPath (x, t))) (B : Matrix d d ℂ) :
    fderiv ℝ matLog x B =
      ∫ t in (0 : ℝ)..1, (logPath (x, t))⁻¹ * B * (logPath (x, t))⁻¹ := by
  have h3 := fderiv_intervalIntegral_apply_of_contDiffAt (a := 0) (b := 1)
    (f := logIntegrand) (x₀ := x) (contDiffAt_logIntegrand_of_mem hx) B
  rw [show (matLog : Matrix d d ℂ → _) = fun y ↦ ∫ t in (0 : ℝ)..1, logIntegrand (y, t) from rfl]
  refine h3.trans (intervalIntegral.integral_congr fun t ht ↦ ?_)
  exact fderiv_logIntegrand_apply (hx t (by rwa [uIcc_of_le zero_le_one] at ht)) B

/-! ### At a diagonal matrix -/

section Diagonal

variable {l : d → ℝ}

/-- The entry `(i, j)` of an interval integral of matrices. -/
theorem intervalIntegral_matrix_apply {F : ℝ → Matrix d d ℂ}
    (hF : IntervalIntegrable F MeasureTheory.volume 0 1) (i j : d) :
    (∫ t in (0 : ℝ)..1, F t) i j = ∫ t in (0 : ℝ)..1, F t i j :=
  ((LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j :
    Matrix d d ℂ →ₗ[ℝ] ℂ)).intervalIntegral_comp_comm hF).symm

omit [Fintype d] in
theorem logPath_diagonal (l : d → ℝ) (t : ℝ) :
    logPath (Matrix.diagonal (fun i ↦ (l i : ℂ)), t) =
      Matrix.diagonal fun i ↦ (((1 - t) * l i + t : ℝ) : ℂ) := by
  ext i j
  rcases eq_or_ne i j with rfl | h
  · simp [logPath]
  · simp [logPath, h]

omit [Fintype d] in
theorem posDef_diagonal_ofReal (hl : ∀ i, 0 < l i) :
    (Matrix.diagonal fun i ↦ (l i : ℂ)).PosDef :=
  posDef_diagonal_iff.2 fun i ↦ by exact_mod_cast hl i

/-- The inverse of a diagonal matrix with nonzero real entries. -/
theorem inv_diagonal_ofReal {v : d → ℝ} (hv : ∀ i, v i ≠ 0) :
    (Matrix.diagonal fun i ↦ (v i : ℂ))⁻¹ = Matrix.diagonal fun i ↦ (((v i)⁻¹ : ℝ) : ℂ) := by
  refine inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i
  push_cast
  exact inv_mul_cancel₀ (by exact_mod_cast hv i)

theorem inv_logPath_diagonal (hl : ∀ i, 0 < l i) {t : ℝ} (ht : t ∈ uIcc (0 : ℝ) 1) :
    (logPath (Matrix.diagonal (fun i ↦ (l i : ℂ)), t))⁻¹ =
      Matrix.diagonal fun i ↦ ((((1 - t) * l i + t)⁻¹ : ℝ) : ℂ) := by
  rw [logPath_diagonal, inv_diagonal_ofReal fun i ↦ (pathScalar_pos (hl i) ht).ne']

/-- **`matLog` at a positive diagonal matrix** is the diagonal of the logarithms. -/
theorem matLog_diagonal (hl : ∀ i, 0 < l i) :
    matLog (Matrix.diagonal fun i ↦ (l i : ℂ)) =
      Matrix.diagonal fun i ↦ ((Real.log (l i) : ℝ) : ℂ) := by
  have hx := isUnit_logPath_of_posDef (posDef_diagonal_ofReal hl)
  ext i j
  rw [matLog, intervalIntegral_matrix_apply (intervalIntegrable_logIntegrand hx)]
  rw [intervalIntegral.integral_congr (g := fun t ↦ if i = j then
      (((l i - 1) * ((1 - t) * l i + t)⁻¹ : ℝ) : ℂ) else 0) fun t ht ↦ ?_]
  · rcases eq_or_ne i j with rfl | h
    · simp only [↓reduceIte, diagonal_apply_eq]
      rw [intervalIntegral.integral_ofReal, integral_log (hl i)]
    · simp [h]
  · simp only [logIntegrand, inv_logPath_diagonal hl ht]
    rcases eq_or_ne i j with rfl | h
    · simp [sub_mul]
    · simp [h]

/-- **The Daleckii–Krein formula for `matLog`**: at a positive diagonal matrix,
`(D matLog [B])ᵢⱼ = logKernel λᵢ λⱼ · Bᵢⱼ`. -/
theorem fderiv_matLog_diagonal_apply (hl : ∀ i, 0 < l i) (B : Matrix d d ℂ) (i j : d) :
    fderiv ℝ matLog (Matrix.diagonal fun i ↦ (l i : ℂ)) B i j =
      (logKernel (l i) (l j) : ℂ) * B i j := by
  have hx := isUnit_logPath_of_posDef (posDef_diagonal_ofReal hl)
  have hcont : ContinuousOn (fun t ↦ (logPath (Matrix.diagonal (fun i ↦ (l i : ℂ)), t))⁻¹ * B *
      (logPath (Matrix.diagonal (fun i ↦ (l i : ℂ)), t))⁻¹) (uIcc 0 1) := by
    intro t ht
    have hu := hx t (by rwa [uIcc_of_le zero_le_one] at ht)
    have hc : ContinuousAt (fun t ↦ Ring.inverse (logPath (Matrix.diagonal (fun i ↦ (l i : ℂ)),
        t))) t :=
      (contDiffAt_ringInverse ℝ (n := 0) hu.unit).continuousAt.comp_of_eq
        ((contDiff_logPath (n := 0)).continuous.comp
          (continuous_const.prodMk continuous_id)).continuousAt (by simp)
    simp only [nonsing_inv_eq_ringInverse]
    exact ((hc.mul continuousAt_const).mul hc).continuousWithinAt
  rw [fderiv_matLog_apply hx, intervalIntegral_matrix_apply hcont.intervalIntegrable]
  rw [intervalIntegral.integral_congr (g := fun t ↦
      ((((1 - t) * l i + t)⁻¹ * ((1 - t) * l j + t)⁻¹ : ℝ) : ℂ) * B i j) fun t ht ↦ ?_]
  · rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
      integral_logKernel (hl i) (hl j)]
  · simp only [inv_logPath_diagonal hl ht, diagonal_mul, mul_diagonal]
    push_cast
    ring

end Diagonal

/-! ### Unitary conjugation -/

theorem logPath_conj {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ) (x : Matrix d d ℂ)
    (t : ℝ) : logPath (U * x * star U, t) = U * logPath (x, t) * star U := by
  have hsU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  simp only [logPath, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hsU]

/-- Invertibility of the whole path is invariant under unitary conjugation. -/
theorem isUnit_logPath_conj {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ)
    {x : Matrix d d ℂ} (hx : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (logPath (x, t))) :
    ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (logPath (U * x * star U, t)) := fun t ht ↦ by
  have hunit : IsUnit U := ⟨⟨U, star U, Matrix.mem_unitaryGroup_iff.1 hU,
    Matrix.mem_unitaryGroup_iff'.1 hU⟩, rfl⟩
  have hunit' : IsUnit (star U) := ⟨⟨star U, U, Matrix.mem_unitaryGroup_iff'.1 hU,
    Matrix.mem_unitaryGroup_iff.1 hU⟩, rfl⟩
  rw [logPath_conj hU]
  exact (hunit.mul (hx t ht)).mul hunit'

/-- Conjugation `M ↦ U M U*` by a unitary, as a continuous linear equivalence. -/
noncomputable def unitaryConj {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ) :
    Matrix d d ℂ ≃L[ℝ] Matrix d d ℂ :=
  ContinuousLinearEquiv.equivOfInverse
    (LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℝ U).comp (LinearMap.mulRight ℝ (star U))))
    (LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℝ (star U)).comp (LinearMap.mulRight ℝ U)))
    (fun M ↦ by
      simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
        LinearMap.mulLeft_apply, LinearMap.mulRight_apply, ← Matrix.mul_assoc,
        Matrix.mem_unitaryGroup_iff'.1 hU, Matrix.one_mul]
      rw [Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff'.1 hU, Matrix.mul_one])
    (fun M ↦ by
      simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
        LinearMap.mulLeft_apply, LinearMap.mulRight_apply, ← Matrix.mul_assoc,
        Matrix.mem_unitaryGroup_iff.1 hU, Matrix.one_mul]
      rw [Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff.1 hU, Matrix.mul_one])

@[simp]
theorem unitaryConj_apply {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ)
    (M : Matrix d d ℂ) : unitaryConj hU M = U * M * star U := by
  simp [unitaryConj, ContinuousLinearEquiv.equivOfInverse, Matrix.mul_assoc]

/-- **`matLog` commutes with unitary conjugation**. -/
theorem matLog_conj {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ) (x : Matrix d d ℂ) :
    matLog (U * x * star U) = U * matLog x * star U := by
  have hUs : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hsU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have hinv : ∀ M : Matrix d d ℂ, (U * M * star U)⁻¹ = U * M⁻¹ * star U := fun M ↦ by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_eq_left_inv hsU, inv_eq_left_inv hUs,
      Matrix.mul_assoc]
  have hint : ∀ t, logIntegrand (U * x * star U, t) = U * logIntegrand (x, t) * star U := by
    intro t
    have hp : logPath (U * x * star U, t) = U * logPath (x, t) * star U := by
      simp only [logPath, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, hsU]
    rw [logIntegrand, logIntegrand, hp, hinv]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUs, Matrix.one_mul]
  rw [matLog, matLog, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one,
    ← unitaryConj_apply hU (∫ t in Ioc (0 : ℝ) 1, logIntegrand (x, t)),
    ← (unitaryConj hU).integral_comp_comm]
  simp only [hint, unitaryConj_apply]

end AlphaCurvature.Quantum
