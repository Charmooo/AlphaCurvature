/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Analysis.Matrix.PosDef
import AlphaCurvature.Curvature.Pullback
import AlphaCurvature.Quantum.Power

/-!
# The quantum Amari embedding and its normal

The quantum Amari embedding is `A(ρ) = p ρ^(1/p)`, `p = 2/(1 - α)`, and `A(ρ) = log ρ` at
`α = 1` (`p = ∞`) (`amari`). It maps the positive definite matrices of trace one onto a level
set of `Y ↦ tr (Y/p)^p` (of `Y ↦ tr exp Y` at `p = ∞`), whose gradient at `A(ρ)` is
`N(ρ) = ρ^((1 + α)/2)` (`amariNormal`). The identity behind this is the **normal identity**

  `tr (N(x) · DA_x[u]) = tr u`

for every positive definite `x` and every `u` (`trace_amariNormal_mul_fderiv_amari`). At a
diagonal `x = diag λ` it is the Daleckii–Krein formula, with `λ^((1+α)/2) · A^[1](λ, λ) = 1`;
in general it follows by unitary diagonalization.

Differentiating it in the affine chart `z ↦ ρ₀ + z` of a space `V` of traceless Hermitian
matrices gives the second fundamental form in first derivatives only:

  `⟨D²φ (v, w), N(ρ₀)⟩ = -⟨DN_ρ₀[v], DA_ρ₀[w]⟩`,  `φ(z) = A(ρ₀ + z)`,

with `⟨X, Y⟩ = Re tr (X Y)` (`hsForm_fderiv_fderiv_amariChart`); and `N(ρ₀)` is normal to the
image of `Dφ` (`hsForm_amariNormal_fderiv_amariChart`).

## Main definitions

* `AlphaCurvature.Quantum.hsForm`: the Hilbert–Schmidt form `Re tr (X Y)`.
* `AlphaCurvature.Quantum.amari`, `AlphaCurvature.Quantum.amariNormal`: `A` and `N`.
* `AlphaCurvature.Quantum.amariKernel`: the divided difference of `A` at the eigenvalues.
-/

open scoped Matrix.Norms.L2Operator Topology ComplexOrder
open Matrix ContinuousLinearMap Filter Set

namespace AlphaCurvature.Quantum

variable {d : Type*} [Fintype d] [DecidableEq d] {α : ℝ}

/-! ### Positive definiteness from the path -/

/-- A Hermitian matrix whose `matLog` path is invertible is positive definite: an eigenvalue
`μ ≤ 0` would make `(1 - t) μ + t` vanish at `t = -μ/(1 - μ) ∈ [0, 1)`. -/
theorem posDef_of_isUnit_logPath {x : Matrix d d ℂ} (hx : x.IsHermitian)
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (logPath (x, t))) : x.PosDef := by
  refine hx.posDef_iff_eigenvalues_pos.2 fun i ↦ ?_
  by_contra hμ
  push Not at hμ
  set μ := hx.eigenvalues i
  set v : d → ℂ := ⇑(hx.eigenvectorBasis i)
  have h1 : 0 < 1 - μ := by linarith
  set t := -μ / (1 - μ)
  have ht : t ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (neg_nonneg.2 hμ) h1.le, (div_le_one h1).2 (by linarith)⟩
  have hv : v ≠ 0 := fun h ↦ (hx.eigenvectorBasis.orthonormal.ne_zero i) (by
    simpa [v] using congrArg (WithLp.toLp 2) h)
  have hzero : logPath (x, t) *ᵥ v = 0 := by
    have hc : (1 - t) * μ + t = 0 := by
      simp only [t]
      field_simp
      ring
    have hxv : x *ᵥ v = μ • v := hx.mulVec_eigenvectorBasis i
    simp only [logPath, Matrix.add_mulVec, Matrix.smul_mulVec, hxv, Matrix.one_mulVec, smul_smul,
      ← add_smul, hc, zero_smul]
  exact hv (Matrix.mulVec_injective_iff_isUnit.2 (hp t ht) (hzero.trans (mulVec_zero _).symm))

/-! ### Unitary conjugation -/

section Conj

variable {U : Matrix d d ℂ}

/-- Conjugation `M ↦ U M U*` as a continuous linear map. -/
noncomputable def conjCLM (U : Matrix d d ℂ) : Matrix d d ℂ →L[ℝ] Matrix d d ℂ :=
  LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℝ U).comp (LinearMap.mulRight ℝ (star U)))

@[simp]
theorem conjCLM_apply (U M : Matrix d d ℂ) : conjCLM U M = U * M * star U := by
  simp [conjCLM, Matrix.mul_assoc]

theorem trace_conj (hU : U ∈ Matrix.unitaryGroup d ℂ) (X : Matrix d d ℂ) :
    trace (U * X * star U) = trace X := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff'.1 hU, Matrix.one_mul]

theorem trace_conj_star (hU : U ∈ Matrix.unitaryGroup d ℂ) (X : Matrix d d ℂ) :
    trace (star U * X * U) = trace X := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff.1 hU, Matrix.one_mul]

omit [DecidableEq d] in
/-- If `f` commutes with a conjugation near `x`, so does its derivative. -/
theorem fderiv_conj_of_eventually {f : Matrix d d ℂ → Matrix d d ℂ} {x : Matrix d d ℂ}
    (hf : ∀ᶠ y in 𝓝 x, f (U * y * star U) = U * f y * star U)
    (hx : DifferentiableAt ℝ f x) (hx' : DifferentiableAt ℝ f (U * x * star U))
    (B : Matrix d d ℂ) :
    fderiv ℝ f (U * x * star U) (U * B * star U) = U * fderiv ℝ f x B * star U := by
  classical
  have hev : f ∘ conjCLM U =ᶠ[𝓝 x] conjCLM U ∘ f := hf.mono fun y hy ↦ by simpa using hy
  have hx'' : DifferentiableAt ℝ f (conjCLM U x) := by simpa using hx'
  have h1 : fderiv ℝ (f ∘ conjCLM U) x = (fderiv ℝ f (conjCLM U x)).comp (conjCLM U) := by
    rw [fderiv_comp x hx'' (conjCLM U).differentiableAt, ContinuousLinearMap.fderiv]
  have h2 : fderiv ℝ (conjCLM U ∘ f) x = (conjCLM U).comp (fderiv ℝ f x) := by
    rw [fderiv_comp x (conjCLM U).differentiableAt hx, ContinuousLinearMap.fderiv]
  have := congrArg (fun L : Matrix d d ℂ →L[ℝ] Matrix d d ℂ ↦ L B) hev.fderiv_eq
  simp only [h1, h2, ContinuousLinearMap.comp_apply, conjCLM_apply] at this
  exact this

end Conj

/-! ### The Hilbert–Schmidt form -/

/-- The real trace `X ↦ Re tr X`. -/
noncomputable def traceRe : Matrix d d ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (Complex.reLm.comp ((Matrix.traceLinearMap d ℂ ℂ).restrictScalars ℝ))

/-- The **Hilbert–Schmidt form** `⟨X, Y⟩ = Re tr (X Y)`. On Hermitian matrices it is the
Hilbert–Schmidt inner product. -/
noncomputable def hsForm : Matrix d d ℂ →L[ℝ] Matrix d d ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Matrix d d ℂ →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun X Y ↦ (trace (X * Y)).re)
        (fun X X' Y ↦ by simp [Matrix.add_mul, Matrix.trace_add])
        (fun c X Y ↦ by simp [Matrix.trace_smul])
        (fun X Y Y' ↦ by simp [Matrix.mul_add, Matrix.trace_add])
        (fun c X Y ↦ by simp [Matrix.trace_smul]))

@[simp]
theorem hsForm_apply (X Y : Matrix d d ℂ) : hsForm X Y = (trace (X * Y)).re :=
  rfl

theorem hsForm_comm (X Y : Matrix d d ℂ) : hsForm X Y = hsForm Y X := by
  simp [trace_mul_comm X Y]

/-! ### The embedding and its normal -/

/-- **The quantum Amari embedding** `x ↦ p x^(1/p)`, `p = 2/(1 - α)`, and `matLog` at `α = 1`. -/
noncomputable def amari (α : ℝ) : Matrix d d ℂ → Matrix d d ℂ :=
  if α = 1 then matLog else fun x ↦ (2 / (1 - α)) • matPow ((1 - α) / 2) x

/-- **The normal** `x ↦ x^((1 + α)/2)`: the gradient of the level-set function at `A(x)`. -/
noncomputable def amariNormal (α : ℝ) (x : Matrix d d ℂ) : Matrix d d ℂ :=
  matPow ((1 + α) / 2) x

/-- The divided difference of the scalar Amari map `t ↦ p t^(1/p)` (`log` at `α = 1`). -/
noncomputable def amariKernel (α a b : ℝ) : ℝ :=
  if α = 1 then logKernel a b else 2 / (1 - α) * powKernel ((1 - α) / 2) a b

theorem contDiffAt_amari_of_isUnit {x : Matrix d d ℂ}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (logPath (x, t))) (n : ℕ) :
    ContDiffAt ℝ n (amari α) x := by
  by_cases h : α = 1
  · simpa [amari, h] using contDiffAt_matLog_of_isUnit hx n
  · simpa [amari, h] using (contDiffAt_matPow_of_isUnit ((1 - α) / 2) hx n).const_smul
      (2 / (1 - α))

theorem contDiffAt_amariNormal_of_isUnit {x : Matrix d d ℂ}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (logPath (x, t))) (n : ℕ) :
    ContDiffAt ℝ n (amariNormal α) x :=
  contDiffAt_matPow_of_isUnit _ hx n

theorem amari_conj {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ) (x : Matrix d d ℂ) :
    amari α (U * x * star U) = U * amari α x * star U := by
  by_cases h : α = 1
  · simpa [amari, h] using matLog_conj hU x
  · simp only [amari, h, ↓reduceIte, matPow_conj _ hU x, Matrix.mul_smul, Matrix.smul_mul]

theorem amariNormal_conj {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ)
    (x : Matrix d d ℂ) : amariNormal α (U * x * star U) = U * amariNormal α x * star U :=
  matPow_conj _ hU x

theorem fderiv_amari_conj {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ)
    {x : Matrix d d ℂ} (hx : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (logPath (x, t))) (B : Matrix d d ℂ) :
    fderiv ℝ (amari α) (U * x * star U) (U * B * star U) = U * fderiv ℝ (amari α) x B * star U :=
  fderiv_conj_of_eventually (Eventually.of_forall fun y ↦ amari_conj hU y)
    ((contDiffAt_amari_of_isUnit hx 1).differentiableAt one_ne_zero)
    ((contDiffAt_amari_of_isUnit (isUnit_logPath_conj hU hx) 1).differentiableAt one_ne_zero) B

/-! ### At a diagonal matrix -/

section Diagonal

variable {l : d → ℝ}

theorem amariNormal_diagonal (hl : ∀ i, 0 < l i) :
    amariNormal α (Matrix.diagonal fun i ↦ (l i : ℂ)) =
      Matrix.diagonal fun i ↦ ((l i ^ ((1 + α) / 2) : ℝ) : ℂ) :=
  matPow_diagonal _ hl

/-- **The Daleckii–Krein formula for `amari`**. -/
theorem fderiv_amari_diagonal_apply (hl : ∀ i, 0 < l i) (B : Matrix d d ℂ) (i j : d) :
    fderiv ℝ (amari α) (Matrix.diagonal fun i ↦ (l i : ℂ)) B i j =
      (amariKernel α (l i) (l j) : ℂ) * B i j := by
  have hD := isUnit_logPath_of_posDef (posDef_diagonal_ofReal hl)
  by_cases h : α = 1
  · simp only [amari, amariKernel, h, ↓reduceIte]
    exact fderiv_matLog_diagonal_apply hl B i j
  · simp only [amari, amariKernel, h, ↓reduceIte]
    rw [show (fun x ↦ (2 / (1 - α)) • matPow ((1 - α) / 2) x) =
      (2 / (1 - α)) • matPow (d := d) ((1 - α) / 2) from rfl,
      fderiv_const_smul ((contDiffAt_matPow_of_isUnit _ hD 1).differentiableAt one_ne_zero),
      _root_.smul_apply, Matrix.smul_apply, fderiv_matPow_diagonal_apply _ hl,
      Complex.real_smul]
    push_cast
    ring

/-- On the diagonal the normal undoes the kernel: `a^((1+α)/2) · A^[1](a, a) = 1`. -/
theorem rpow_mul_amariKernel_self {a : ℝ} (ha : 0 < a) :
    a ^ ((1 + α) / 2) * amariKernel α a a = 1 := by
  by_cases h : α = 1
  · simp [amariKernel, h, logKernel_self, ha.ne']
  · have h1 : 1 - α ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    have e : a ^ ((1 + α) / 2) * a ^ ((1 - α) / 2 - 1) = 1 := by
      rw [← Real.rpow_add ha, show (1 + α) / 2 + ((1 - α) / 2 - 1) = 0 by ring, Real.rpow_zero]
    simp only [amariKernel, h, ↓reduceIte, powKernel_self]
    calc a ^ ((1 + α) / 2) * (2 / (1 - α) * ((1 - α) / 2 * a ^ ((1 - α) / 2 - 1)))
        = 2 / (1 - α) * ((1 - α) / 2) * (a ^ ((1 + α) / 2) * a ^ ((1 - α) / 2 - 1)) := by ring
      _ = 1 := by rw [e]; field_simp

/-- **The normal identity at a diagonal matrix**. -/
theorem trace_amariNormal_mul_fderiv_amari_diagonal (hl : ∀ i, 0 < l i) (B : Matrix d d ℂ) :
    trace (amariNormal α (Matrix.diagonal fun i ↦ (l i : ℂ)) *
      fderiv ℝ (amari α) (Matrix.diagonal fun i ↦ (l i : ℂ)) B) = trace B := by
  rw [amariNormal_diagonal hl]
  simp only [Matrix.trace, diag_apply, diagonal_mul, fderiv_amari_diagonal_apply hl]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← mul_assoc, ← Complex.ofReal_mul, rpow_mul_amariKernel_self (hl i), Complex.ofReal_one,
    one_mul]

end Diagonal

/-! ### The normal identity -/

/-- **The normal identity**: `tr (N(x) · DA_x[B]) = tr B` at every positive definite `x`. -/
theorem trace_amariNormal_mul_fderiv_amari {x : Matrix d d ℂ} (hx : x.PosDef)
    (B : Matrix d d ℂ) : trace (amariNormal α x * fderiv ℝ (amari α) x B) = trace B := by
  set U : Matrix d d ℂ := ((hx.1.eigenvectorUnitary : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ)
  have hU : U ∈ Matrix.unitaryGroup d ℂ := hx.1.eigenvectorUnitary.2
  have hUs : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hsU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  set l := hx.1.eigenvalues
  have hl : ∀ i, 0 < l i := hx.eigenvalues_pos
  set D := Matrix.diagonal fun i ↦ (l i : ℂ)
  have hD := isUnit_logPath_of_posDef (posDef_diagonal_ofReal hl)
  have hxD : x = U * D * star U := by
    conv_lhs => rw [hx.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  have hB : B = U * (star U * B * U) * star U := by
    simp only [← Matrix.mul_assoc, hsU, Matrix.one_mul]
    rw [Matrix.mul_assoc, hsU, Matrix.mul_one]
  rw [hxD, amariNormal_conj hU D]
  conv_lhs => rw [hB, fderiv_amari_conj hU hD]
  have hmul : U * amariNormal α D * star U * (U * fderiv ℝ (amari α) D (star U * B * U) * star U) =
      U * (amariNormal α D * fderiv ℝ (amari α) D (star U * B * U)) * star U := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUs, Matrix.one_mul]
  rw [hmul, trace_conj hU, trace_amariNormal_mul_fderiv_amari_diagonal hl, trace_conj_star hU]

/-! ### The chart and the second fundamental form -/

section Chart

variable (α) (V : Submodule ℝ (Matrix d d ℂ)) (ρ₀ : Matrix d d ℂ)

/-- The quantum Amari embedding in the affine chart `z ↦ ρ₀ + z` of `ρ₀ + V`. -/
noncomputable def amariChart (z : V) : Matrix d d ℂ :=
  amari α (V.subtypeL z + ρ₀)

variable {α V ρ₀}

omit [Fintype d] [DecidableEq d] in
theorem hasFDerivAt_chart [Finite d] (z : V) :
    HasFDerivAt (fun z : V ↦ V.subtypeL z + ρ₀) V.subtypeL z := by
  classical
  have := Fintype.ofFinite d
  exact (V.subtypeL.hasFDerivAt).add_const ρ₀

omit [Fintype d] [DecidableEq d] in
theorem fderiv_comp_chart [Finite d] {f : Matrix d d ℂ → Matrix d d ℂ} {z : V}
    (hf : DifferentiableAt ℝ f (V.subtypeL z + ρ₀)) (u : V) :
    fderiv ℝ (fun z : V ↦ f (V.subtypeL z + ρ₀)) z u = fderiv ℝ f (V.subtypeL z + ρ₀) u := by
  classical
  have := Fintype.ofFinite d
  have h : HasFDerivAt (fun z : V ↦ f (V.subtypeL z + ρ₀))
      ((fderiv ℝ f (V.subtypeL z + ρ₀)).comp V.subtypeL) z :=
    hf.hasFDerivAt.comp z (hasFDerivAt_chart z)
  rw [h.fderiv]
  rfl

theorem fderiv_amariChart {z : V} (hz : DifferentiableAt ℝ (amari α) (V.subtypeL z + ρ₀))
    (u : V) : fderiv ℝ (amariChart α V ρ₀) z u = fderiv ℝ (amari α) (V.subtypeL z + ρ₀) u :=
  fderiv_comp_chart hz u

omit [Fintype d] [DecidableEq d] in
/-- Near `0` the chart stays positive definite. -/
theorem eventually_posDef_chart [Finite d] (hρ : ρ₀.PosDef) (hV : ∀ v ∈ V, v.IsHermitian) :
    ∀ᶠ z in 𝓝 (0 : V), (V.subtypeL z + ρ₀).PosDef := by
  classical
  have := Fintype.ofFinite d
  have hc : Tendsto (fun z : V ↦ V.subtypeL z + ρ₀) (𝓝 0) (𝓝 ρ₀) := by
    simpa using ((hasFDerivAt_chart (ρ₀ := ρ₀) (0 : V)).continuousAt).tendsto
  refine (hc.eventually (eventually_isUnit_logPath (isUnit_logPath_of_posDef hρ))).mono
    fun z hz ↦ posDef_of_isUnit_logPath ((hV z z.2).add hρ.1) hz

theorem contDiffAt_amariChart (hρ : ρ₀.PosDef) (n : ℕ) :
    ContDiffAt ℝ n (amariChart α V ρ₀) 0 := by
  have h0 : V.subtypeL (0 : V) + ρ₀ = ρ₀ := by simp
  have hA := contDiffAt_amari_of_isUnit (α := α) (isUnit_logPath_of_posDef hρ) n
  rw [← h0] at hA
  exact hA.comp (f := fun z : V ↦ V.subtypeL z + ρ₀) (0 : V)
    ((V.subtypeL.contDiff.add (contDiff_const (c := ρ₀))).contDiffAt)

/-- **`N(ρ₀ + z)` is normal** to the image of `Dφ_z`, for `z` near `0`. -/
theorem eventually_hsForm_amariNormal_fderiv_amariChart (hρ : ρ₀.PosDef)
    (hV : ∀ v ∈ V, v.IsHermitian ∧ trace v = 0) (w : V) :
    ∀ᶠ z in 𝓝 (0 : V),
      hsForm (amariNormal α (V.subtypeL z + ρ₀)) (fderiv ℝ (amariChart α V ρ₀) z w) = 0 := by
  refine (eventually_posDef_chart hρ fun v hv ↦ (hV v hv).1).mono fun z hz ↦ ?_
  have hd := (contDiffAt_amari_of_isUnit (α := α) (isUnit_logPath_of_posDef hz) 1).differentiableAt
    one_ne_zero
  rw [fderiv_amariChart hd, hsForm_apply, trace_amariNormal_mul_fderiv_amari hz]
  simp [(hV w w.2).2]

theorem hsForm_amariNormal_fderiv_amariChart (hρ : ρ₀.PosDef)
    (hV : ∀ v ∈ V, v.IsHermitian ∧ trace v = 0) (w : V) :
    hsForm (amariNormal α ρ₀) (fderiv ℝ (amariChart α V ρ₀) 0 w) = 0 := by
  simpa using (eventually_hsForm_amariNormal_fderiv_amariChart (α := α) hρ hV w).self_of_nhds

/-- **The second fundamental form in first derivatives**:
`⟨D²φ (v, w), N(ρ₀)⟩ = -⟨DN_ρ₀[v], DA_ρ₀[w]⟩`. -/
theorem hsForm_fderiv_fderiv_amariChart (hρ : ρ₀.PosDef)
    (hV : ∀ v ∈ V, v.IsHermitian ∧ trace v = 0) (v w : V) :
    hsForm (fderiv ℝ (fderiv ℝ (amariChart α V ρ₀)) 0 v w) (amariNormal α ρ₀) =
      -hsForm (fderiv ℝ (amariNormal α) ρ₀ v) (fderiv ℝ (amari α) ρ₀ w) := by
  have h0 : V.subtypeL (0 : V) + ρ₀ = ρ₀ := by simp
  have hρu := isUnit_logPath_of_posDef hρ
  have hN : DifferentiableAt ℝ (amariNormal α) (V.subtypeL (0 : V) + ρ₀) := by
    rw [h0]; exact (contDiffAt_amariNormal_of_isUnit hρu 1).differentiableAt one_ne_zero
  have hA : DifferentiableAt ℝ (amari α) (V.subtypeL (0 : V) + ρ₀) := by
    rw [h0]; exact (contDiffAt_amari_of_isUnit hρu 1).differentiableAt one_ne_zero
  have hψ : DifferentiableAt ℝ (fun z : V ↦ amariNormal α (V.subtypeL z + ρ₀)) 0 :=
    hN.comp 0 (hasFDerivAt_chart 0).differentiableAt
  have hφ' : DifferentiableAt ℝ (fderiv ℝ (amariChart α V ρ₀)) 0 :=
    ((contDiffAt_amariChart hρ 2).fderiv_right (m := 1) (by norm_num)).differentiableAt
      one_ne_zero
  have hb : DifferentiableAt ℝ (fun z ↦ fderiv ℝ (amariChart α V ρ₀) z w) 0 :=
    hφ'.clm_apply (differentiableAt_const w)
  have hzero : fderiv ℝ (fun z ↦ hsForm (amariNormal α (V.subtypeL z + ρ₀))
      (fderiv ℝ (amariChart α V ρ₀) z w)) 0 v = 0 := by
    have hev : (fun z ↦ hsForm (amariNormal α (V.subtypeL z + ρ₀))
        (fderiv ℝ (amariChart α V ρ₀) z w)) =ᶠ[𝓝 0] fun _ ↦ (0 : ℝ) :=
      eventually_hsForm_amariNormal_fderiv_amariChart hρ hV w
    rw [hev.fderiv_eq]
    simp
  rw [Curvature.fderiv_bilin_apply_apply (c := fun _ ↦ hsForm) (differentiableAt_const _) hψ
    hb] at hzero
  rw [fderiv_comp_chart hN, fderiv_clm_apply hφ' (differentiableAt_const w),
    fderiv_amariChart hA] at hzero
  simp only [fderiv_fun_const, Pi.zero_apply, _root_.zero_apply, zero_add,
    ContinuousLinearMap.comp_zero, flip_apply, h0] at hzero
  rw [hsForm_comm]
  linarith

end Chart

end AlphaCurvature.Quantum
