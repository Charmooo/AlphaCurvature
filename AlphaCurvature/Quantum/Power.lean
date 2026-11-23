/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import AlphaCurvature.ForMathlib.ExpDeriv
import AlphaCurvature.Quantum.Log

/-!
# Real powers of a positive definite matrix

`matPow s x = exp (s • matLog x)`. It is smooth near every positive definite matrix
(`contDiffAt_matPow`), is the entrywise power at a positive diagonal matrix (`matPow_diagonal`),
commutes with unitary conjugation (`matPow_conj`), and its derivative at a positive diagonal
matrix is the Daleckii–Krein formula `(D matPow_s [B])ᵢⱼ = powKernel s λᵢ λⱼ · Bᵢⱼ`, with
`powKernel s a b = (aˢ − bˢ)/(a − b)` and `s a^(s−1)` on the diagonal
(`fderiv_matPow_diagonal_apply`).

The derivative is the chain rule: the derivative of `exp` at the diagonal matrix
`s • matLog (diagonal λ) = diagonal (s log λ)` multiplies entry `(i, j)` by the divided difference
of `exp` at `s log λᵢ, s log λⱼ` (`AlphaCurvature.Matrix.expDeriv_diagonal_apply`), and the
derivative of `matLog` multiplies it by `logKernel λᵢ λⱼ`; the product of the two kernels and `s`
is `powKernel s λᵢ λⱼ` (`expKernel_mul_logKernel`).
-/

open scoped Matrix.Norms.L2Operator Topology ComplexOrder
open Matrix ContinuousLinearMap

namespace AlphaCurvature.Quantum

/-! ### The scalar kernels -/

section Scalar

/-- The first divided difference of `Real.exp`. -/
noncomputable def expKernel (x y : ℝ) : ℝ :=
  if x = y then Real.exp x else (Real.exp x - Real.exp y) / (x - y)

/-- The first divided difference of `t ↦ tˢ`: `(aˢ − bˢ)/(a − b)`, and `s a^(s−1)` on the
diagonal. -/
noncomputable def powKernel (s a b : ℝ) : ℝ :=
  if a = b then s * a ^ (s - 1) else (a ^ s - b ^ s) / (a - b)

theorem powKernel_self (s a : ℝ) : powKernel s a a = s * a ^ (s - 1) := by simp [powKernel]

theorem powKernel_of_ne {s a b : ℝ} (h : a ≠ b) :
    powKernel s a b = (a ^ s - b ^ s) / (a - b) := by simp [powKernel, h]

theorem expDividedDiff_ofReal (x y : ℝ) :
    AlphaCurvature.Matrix.expDividedDiff x y = (expKernel x y : ℂ) := by
  rcases eq_or_ne x y with rfl | h
  · simp only [AlphaCurvature.Matrix.expDividedDiff_self, expKernel, ↓reduceIte,
      ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]
  · rw [AlphaCurvature.Matrix.expDividedDiff_of_ne (by exact_mod_cast h)]
    simp only [expKernel, h, ↓reduceIte, ← Complex.exp_eq_exp_ℂ]
    push_cast
    rfl

/-- The chain rule for the kernels: `expKernel (s log a) (s log b) · s · logKernel a b` is
`powKernel s a b`. -/
theorem expKernel_mul_logKernel (s : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    expKernel (s * Real.log a) (s * Real.log b) * s * logKernel a b = powKernel s a b := by
  have hpa : Real.exp (s * Real.log a) = a ^ s := by rw [Real.rpow_def_of_pos ha, mul_comm]
  have hpb : Real.exp (s * Real.log b) = b ^ s := by rw [Real.rpow_def_of_pos hb, mul_comm]
  rcases eq_or_ne a b with rfl | hab
  · rw [expKernel, ite_eq_left_iff.2 fun h ↦ (h rfl).elim, logKernel_self, powKernel_self, hpa,
      Real.rpow_sub_one ha.ne']
    ring
  rcases eq_or_ne s 0 with rfl | hs
  · simp [powKernel_of_ne hab]
  have hlog : Real.log a - Real.log b ≠ 0 :=
    sub_ne_zero.2 fun h ↦ hab (Real.log_injOn_pos ha hb h)
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  have hsl : s * Real.log a - s * Real.log b ≠ 0 := by
    rw [← mul_sub]; exact mul_ne_zero hs hlog
  rw [expKernel, ite_eq_right_iff.2 fun h ↦ (sub_ne_zero.1 hsl h).elim, logKernel_of_ne hab,
    powKernel_of_ne hab, hpa, hpb]
  field_simp

end Scalar

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The **real power** `xˢ = exp (s • matLog x)`. -/
noncomputable def matPow (s : ℝ) (x : Matrix d d ℂ) : Matrix d d ℂ :=
  NormedSpace.exp (s • matLog x)

/-- `matPow s` is smooth wherever the whole path of `matLog` is invertible. -/
theorem contDiffAt_matPow_of_isUnit (s : ℝ) {x : Matrix d d ℂ}
    (hx : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (logPath (x, t))) (n : ℕ) :
    ContDiffAt ℝ n (matPow s) x :=
  (NormedSpace.exp_analytic (𝕂 := ℝ) _).contDiffAt.comp x
    ((contDiffAt_matLog_of_isUnit hx n).const_smul s)

/-- **`matPow s` is smooth** at a positive definite matrix. -/
theorem contDiffAt_matPow (s : ℝ) {ρ : Matrix d d ℂ} (hρ : ρ.PosDef) (n : ℕ) :
    ContDiffAt ℝ n (matPow s) ρ :=
  (NormedSpace.exp_analytic (𝕂 := ℝ) _).contDiffAt.comp ρ ((contDiffAt_matLog hρ n).const_smul s)

theorem smul_matLog_diagonal (s : ℝ) {l : d → ℝ} (hl : ∀ i, 0 < l i) :
    s • matLog (Matrix.diagonal fun i ↦ (l i : ℂ)) =
      Matrix.diagonal fun i ↦ ((s * Real.log (l i) : ℝ) : ℂ) := by
  rw [matLog_diagonal hl, ← diagonal_smul]
  congr 1
  funext i
  simp [Complex.real_smul]

/-- **`matPow s` at a positive diagonal matrix** is the diagonal of the powers. -/
theorem matPow_diagonal (s : ℝ) {l : d → ℝ} (hl : ∀ i, 0 < l i) :
    matPow s (Matrix.diagonal fun i ↦ (l i : ℂ)) =
      Matrix.diagonal fun i ↦ ((l i ^ s : ℝ) : ℂ) := by
  rw [matPow, smul_matLog_diagonal s hl, Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp, Real.rpow_def_of_pos (hl i),
    mul_comm]

/-- **`matPow s` commutes with unitary conjugation**. -/
theorem matPow_conj (s : ℝ) {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ)
    (x : Matrix d d ℂ) :
    matPow s (U * x * star U) = U * matPow s x * star U := by
  have hUs : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hsU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have hunit : IsUnit U := ⟨⟨U, star U, hsU, hUs⟩, rfl⟩
  rw [matPow, matPow, matLog_conj hU x, show s • (U * matLog x * star U) =
    U * (s • matLog x) * star U by rw [Matrix.mul_smul, Matrix.smul_mul],
    ← inv_eq_left_inv hUs, Matrix.exp_conj _ _ hunit]

/-- **The Daleckii–Krein formula for `matPow`**: at a positive diagonal matrix,
`(D matPow_s [B])ᵢⱼ = powKernel s λᵢ λⱼ · Bᵢⱼ`. -/
theorem fderiv_matPow_diagonal_apply (s : ℝ) {l : d → ℝ} (hl : ∀ i, 0 < l i)
    (B : Matrix d d ℂ) (i j : d) :
    fderiv ℝ (matPow s) (Matrix.diagonal fun i ↦ (l i : ℂ)) B i j =
      (powKernel s (l i) (l j) : ℂ) * B i j := by
  set D := Matrix.diagonal fun i ↦ (l i : ℂ)
  have hD : D.PosDef := posDef_diagonal_ofReal hl
  have hlog : HasFDerivAt matLog (fderiv ℝ matLog D) D :=
    ((contDiffAt_matLog hD 1).differentiableAt one_ne_zero).hasFDerivAt
  have hsD := smul_matLog_diagonal s hl
  have hexp := (hasFDerivAt_exp' (𝕂 := ℂ) (s • matLog D)).restrictScalars ℝ
  have h := hexp.comp D (hlog.const_smul s)
  rw [show (matPow s : Matrix d d ℂ → _) = NormedSpace.exp ∘ (s • matLog) from rfl,
    h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, coe_restrictScalars', _root_.smul_apply]
  rw [hsD, AlphaCurvature.Matrix.expDeriv_diagonal_apply, Matrix.smul_apply,
    fderiv_matLog_diagonal_apply hl, expDividedDiff_ofReal, Complex.real_smul,
    ← expKernel_mul_logKernel s (hl i) (hl j)]
  push_cast
  ring

end AlphaCurvature.Quantum
