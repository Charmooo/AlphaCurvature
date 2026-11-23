/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import AlphaCurvature.Quantum.Normal

/-!
# The image of the quantum Amari embedding as a hypersurface

These are the hypotheses of the codimension-one Gauss formula
(`AlphaCurvature.Curvature.scalarCurvature_pullback_const_of_normal`) for the chart
`φ(z) = A(ρ₀ + z)` of the quantum α-geometry, with the Hilbert–Schmidt form `hsForm` on the
Hermitian matrices `hermitian d`:

* `fderiv_amariChart_mem`, `fderiv_fderiv_amariChart_mem`: `Dφ` and `D²φ` take Hermitian
  values, because `A` maps positive definite matrices to Hermitian ones (`isHermitian_amari`).
* At a positive diagonal `ρ₀` and with `V` all traceless Hermitian matrices:
  `exists_eq_smul_amariNormal` (a Hermitian matrix orthogonal to the image of `Dφ` is a multiple
  of the normal `N(ρ₀)`) and `hsForm_amariNormal_self_pos` (`⟨N, N⟩ > 0`).

The normality of `N(ρ₀)` and the second fundamental form are in `AlphaCurvature.Quantum.Normal`.
-/

open scoped Matrix.Norms.L2Operator Topology ComplexOrder
open Matrix ContinuousLinearMap Filter Set

namespace AlphaCurvature.Quantum

variable {d : Type*} [Fintype d] [DecidableEq d] {α : ℝ}

/-! ### The Hermitian matrices as a real subspace -/

/-- The real-linear map `X ↦ X* - X`, whose kernel is the Hermitian matrices. -/
noncomputable def skewPart : Matrix d d ℂ →ₗ[ℝ] Matrix d d ℂ where
  toFun X := star X - X
  map_add' X Y := by simp only [star_add]; abel
  map_smul' r X := by simp [star_smul, smul_sub]

variable (d) in
/-- The Hermitian matrices, as a real subspace. -/
noncomputable def hermitian : Submodule ℝ (Matrix d d ℂ) := LinearMap.ker skewPart

omit [Fintype d] [DecidableEq d] in
theorem mem_hermitian {X : Matrix d d ℂ} : X ∈ hermitian d ↔ X.IsHermitian := by
  simp [hermitian, skewPart, IsHermitian, sub_eq_zero, Matrix.star_eq_conjTranspose]

omit [Fintype d] [DecidableEq d] in
/-- A function that takes Hermitian values near `x` has Hermitian derivatives at `x`. -/
theorem fderiv_mem_hermitian [Finite d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → Matrix d d ℂ} {x : E} (hg : ∀ᶠ y in 𝓝 x, g y ∈ hermitian d)
    (hd : DifferentiableAt ℝ g x) (u : E) : fderiv ℝ g x u ∈ hermitian d := by
  classical
  have := Fintype.ofFinite d
  let T : Matrix d d ℂ →L[ℝ] Matrix d d ℂ := LinearMap.toContinuousLinearMap skewPart
  have h0 : (T ∘ g) =ᶠ[𝓝 x] fun _ ↦ 0 :=
    hg.mono fun y hy ↦ by simpa [T, hermitian] using hy
  have h1 : fderiv ℝ (T ∘ g) x = T.comp (fderiv ℝ g x) := by
    rw [fderiv_comp x T.differentiableAt hd, ContinuousLinearMap.fderiv]
  have h2 := congrArg (fun L : E →L[ℝ] Matrix d d ℂ ↦ L u) (h1.symm.trans h0.fderiv_eq)
  simp only [ContinuousLinearMap.comp_apply, fderiv_fun_const, Pi.zero_apply,
    _root_.zero_apply] at h2
  simpa [hermitian, T] using h2

/-! ### Hermitian values -/

omit [Fintype d] in
theorem isHermitian_diagonal_ofReal (r : d → ℝ) :
    (Matrix.diagonal fun i ↦ (r i : ℂ)).IsHermitian :=
  isHermitian_diagonal_iff.2 fun i ↦ by simp [isSelfAdjoint_iff]

omit [Fintype d] in
theorem isHermitian_single_add (i j : d) (c : ℂ) :
    (single i j c + single j i (star c)).IsHermitian := by
  simp [IsHermitian, conjTranspose_single, add_comm]

omit [Fintype d] in
theorem isHermitian_single_self (i : d) (r : ℝ) : (single i i (r : ℂ)).IsHermitian := by
  simp [IsHermitian, conjTranspose_single]

/-- A positive definite matrix is a unitary conjugate of a positive diagonal matrix. -/
theorem exists_unitary_diagonal_of_posDef {x : Matrix d d ℂ} (hx : x.PosDef) :
    ∃ U ∈ Matrix.unitaryGroup d ℂ, ∃ l : d → ℝ, (∀ i, 0 < l i) ∧
      x = U * Matrix.diagonal (fun i ↦ (l i : ℂ)) * star U := by
  refine ⟨_, hx.1.eigenvectorUnitary.2, hx.1.eigenvalues, hx.eigenvalues_pos, ?_⟩
  conv_lhs => rw [hx.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rfl

/-- A conjugation-equivariant map that is Hermitian at positive diagonal matrices is Hermitian at
every positive definite matrix. -/
theorem isHermitian_of_conj {f : Matrix d d ℂ → Matrix d d ℂ}
    (hconj : ∀ U ∈ Matrix.unitaryGroup d ℂ, ∀ x : Matrix d d ℂ,
      f (U * x * star U) = U * f x * star U)
    (hdiag : ∀ l : d → ℝ, (∀ i, 0 < l i) → (f (Matrix.diagonal fun i ↦ (l i : ℂ))).IsHermitian)
    {x : Matrix d d ℂ} (hx : x.PosDef) : (f x).IsHermitian := by
  obtain ⟨U, hU, l, hl, rfl⟩ := exists_unitary_diagonal_of_posDef hx
  rw [hconj U hU]
  exact isHermitian_mul_mul_conjTranspose U (hdiag l hl)

theorem isHermitian_amari {x : Matrix d d ℂ} (hx : x.PosDef) : (amari α x).IsHermitian := by
  refine isHermitian_of_conj (fun U hU x ↦ amari_conj hU x) (fun l hl ↦ ?_) hx
  by_cases h : α = 1
  · simpa [amari, h, matLog_diagonal hl] using isHermitian_diagonal_ofReal _
  · simp only [amari, h, ↓reduceIte, matPow_diagonal _ hl]
    exact mem_hermitian.1 (Submodule.smul_mem _ _ (mem_hermitian.2
      (isHermitian_diagonal_ofReal _)))

theorem isHermitian_amariNormal {x : Matrix d d ℂ} (hx : x.PosDef) :
    (amariNormal α x).IsHermitian := by
  refine isHermitian_of_conj (fun U hU x ↦ amariNormal_conj hU x) (fun l hl ↦ ?_) hx
  rw [amariNormal_diagonal hl]
  exact isHermitian_diagonal_ofReal _

/-! ### Hermitian derivatives in the chart -/

section Chart

variable {V : Submodule ℝ (Matrix d d ℂ)} {ρ₀ : Matrix d d ℂ}

theorem differentiableAt_amariChart {z : V} (hz : (V.subtypeL z + ρ₀).PosDef) :
    DifferentiableAt ℝ (amariChart α V ρ₀) z :=
  ((contDiffAt_amari_of_isUnit (isUnit_logPath_of_posDef hz) 1).differentiableAt
    one_ne_zero).comp z (hasFDerivAt_chart z).differentiableAt

/-- **`Dφ` is Hermitian.** -/
theorem fderiv_amariChart_mem (hρ : ρ₀.PosDef) (hV : ∀ v ∈ V, v.IsHermitian) (u : V) :
    fderiv ℝ (amariChart α V ρ₀) 0 u ∈ hermitian d :=
  fderiv_mem_hermitian ((eventually_posDef_chart hρ hV).mono fun _ hz ↦
    mem_hermitian.2 (isHermitian_amari hz))
    ((contDiffAt_amariChart hρ 1).differentiableAt one_ne_zero) u

/-- **`D²φ` is Hermitian.** -/
theorem fderiv_fderiv_amariChart_mem (hρ : ρ₀.PosDef) (hV : ∀ v ∈ V, v.IsHermitian) (v w : V) :
    fderiv ℝ (fderiv ℝ (amariChart α V ρ₀)) 0 v w ∈ hermitian d := by
  have hev : ∀ᶠ z in 𝓝 (0 : V), fderiv ℝ (amariChart α V ρ₀) z w ∈ hermitian d :=
    (eventually_posDef_chart hρ hV).eventually_nhds.mono fun z hz ↦
      fderiv_mem_hermitian (hz.mono fun _ hy ↦ mem_hermitian.2 (isHermitian_amari hy))
        (differentiableAt_amariChart hz.self_of_nhds) w
  have hφ' : DifferentiableAt ℝ (fderiv ℝ (amariChart α V ρ₀)) 0 :=
    ((contDiffAt_amariChart hρ 2).fderiv_right (m := 1) (by norm_num)).differentiableAt
      one_ne_zero
  have h := fderiv_mem_hermitian hev (hφ'.clm_apply (differentiableAt_const w)) v
  rw [fderiv_clm_apply hφ' (differentiableAt_const w)] at h
  simpa using h

end Chart

/-! ### At a positive diagonal matrix -/

section Diagonal

variable {l : d → ℝ}

theorem logKernel_comm (a b : ℝ) : logKernel a b = logKernel b a := by
  rcases eq_or_ne a b with rfl | h
  · rfl
  · rw [logKernel_of_ne h, logKernel_of_ne h.symm, ← neg_div_neg_eq, neg_sub, neg_sub]

theorem powKernel_comm (s a b : ℝ) : powKernel s a b = powKernel s b a := by
  rcases eq_or_ne a b with rfl | h
  · rfl
  · rw [powKernel_of_ne h, powKernel_of_ne h.symm, ← neg_div_neg_eq, neg_sub, neg_sub]

theorem amariKernel_comm (a b : ℝ) : amariKernel α a b = amariKernel α b a := by
  simp only [amariKernel, logKernel_comm a b, powKernel_comm _ a b]

/-- The scalar Amari map is injective, so its divided differences do not vanish. -/
theorem amariKernel_ne_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : amariKernel α a b ≠ 0 := by
  rcases eq_or_ne a b with rfl | hab
  · exact right_ne_zero_of_mul_eq_one (rpow_mul_amariKernel_self ha)
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  by_cases h : α = 1
  · simp only [amariKernel, h, ↓reduceIte, logKernel_of_ne hab]
    exact div_ne_zero (sub_ne_zero.2 fun e ↦ hab (Real.log_injOn_pos ha hb e)) hab'
  · have h1 : 1 - α ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    have hs : (1 - α) / 2 ≠ 0 := div_ne_zero h1 two_ne_zero
    simp only [amariKernel, h, ↓reduceIte, powKernel_of_ne hab]
    exact mul_ne_zero (div_ne_zero two_ne_zero h1) (div_ne_zero
      (sub_ne_zero.2 fun e ↦ hab (Real.rpow_left_injOn hs ha.le hb.le e)) hab')

theorem fderiv_amari_diagonal_single (hl : ∀ i, 0 < l i) (i j : d) (c : ℂ) :
    fderiv ℝ (amari α) (Matrix.diagonal fun i ↦ (l i : ℂ)) (single i j c) =
      single i j ((amariKernel α (l i) (l j) : ℂ) * c) := by
  ext a b
  rw [fderiv_amari_diagonal_apply hl]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp [single_apply_of_ne (h := h)]

theorem hsForm_single (m : Matrix d d ℂ) (i j : d) (c : ℂ) :
    hsForm m (single i j c) = (c * m j i).re := by
  rw [hsForm_comm, hsForm_apply, trace_single_mul, smul_eq_mul]

/-- **The orthogonal complement**: at a positive diagonal `ρ₀`, a Hermitian matrix orthogonal to
`DA_ρ₀[u]` for every traceless Hermitian `u` is a real multiple of the normal `N(ρ₀)`. -/
theorem exists_eq_smul_amariNormal (hl : ∀ i, 0 < l i) {m : Matrix d d ℂ}
    (hm : m.IsHermitian)
    (horth : ∀ u : Matrix d d ℂ, u.IsHermitian → trace u = 0 →
      hsForm m (fderiv ℝ (amari α) (Matrix.diagonal fun i ↦ (l i : ℂ)) u) = 0) :
    ∃ t : ℝ, m = t • amariNormal α (Matrix.diagonal fun i ↦ (l i : ℂ)) := by
  set D := Matrix.diagonal fun i ↦ (l i : ℂ)
  set k := fun i j ↦ amariKernel α (l i) (l j)
  have hk : ∀ i j, k i j ≠ 0 := fun i j ↦ amariKernel_ne_zero (hl i) (hl j)
  have hkc : ∀ i j, k i j = k j i := fun i j ↦ amariKernel_comm _ _
  have hS : ∀ i j c,
      hsForm m (fderiv ℝ (amari α) D (single i j c)) = ((k i j : ℂ) * c * m j i).re :=
    fun i j c ↦ by rw [fderiv_amari_diagonal_single hl, hsForm_single]
  have hstar : ∀ i j, star (m j i) = m i j := hm.apply
  have hre : ∀ i j, (m j i).re = (m i j).re := fun i j ↦ by
    rw [← hstar i j, Complex.star_def, Complex.conj_re]
  have him : ∀ i j, (m j i).im = -(m i j).im := fun i j ↦ by
    rw [← hstar i j, Complex.star_def, Complex.conj_im, neg_neg]
  -- the off-diagonal entries vanish
  have hoff : ∀ i j, i ≠ j → m i j = 0 := by
    intro i j hij
    have htr : ∀ c c' : ℂ, trace (single i j c + single j i c') = 0 := fun c c' ↦ by
      rw [trace_add, trace_single_eq_of_ne (h := hij), trace_single_eq_of_ne (h := hij.symm),
        add_zero]
    have h1 := horth _ (by simpa using isHermitian_single_add i j 1) (htr 1 1)
    have h2 := horth _ (isHermitian_single_add i j Complex.I) (htr _ _)
    simp only [map_add, hS, Complex.star_def, Complex.conj_I] at h1 h2
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.neg_re,
      Complex.neg_im, hkc j i, hre i j, him i j] at h1 h2
    ring_nf at h1 h2
    apply Complex.ext
    · have : 2 * k i j * (m i j).re = 0 := by linarith
      simpa [hk i j] using this
    · have : 2 * k i j * (m i j).im = 0 := by linarith
      simpa [hk i j] using this
  -- the diagonal entries are real and proportional to `λᵢ^((1+α)/2)`
  have hdiag_im : ∀ i, (m i i).im = 0 := fun i ↦ by linarith [him i i]
  have hdiag : ∀ i j, k i i * (m i i).re = k j j * (m j j).re := by
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · rfl
    have h := horth (single i i ((1 : ℝ) : ℂ) - single j j ((1 : ℝ) : ℂ))
      ((isHermitian_single_self i 1).sub (isHermitian_single_self j 1))
      (by rw [trace_sub, trace_single_eq_same, trace_single_eq_same, sub_self])
    simp only [map_sub, hS, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, hdiag_im] at h
    linarith
  rcases isEmpty_or_nonempty d with hd | ⟨⟨i₀⟩⟩
  · exact ⟨0, by ext i; exact (IsEmpty.false i).elim⟩
  refine ⟨k i₀ i₀ * (m i₀ i₀).re, ?_⟩
  rw [amariNormal_diagonal hl]
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · have hn := rpow_mul_amariKernel_self (α := α) (hl i)
    rw [Matrix.smul_apply, diagonal_apply_eq, Complex.real_smul, ← Complex.ofReal_mul,
      ← hdiag i i₀]
    apply Complex.ext
    · simp only [Complex.ofReal_re]
      calc (m i i).re = (m i i).re * (l i ^ ((1 + α) / 2) * k i i) := by rw [hn, mul_one]
        _ = k i i * (m i i).re * l i ^ ((1 + α) / 2) := by ring
    · simp [hdiag_im i]
  · simp [hoff i j hij, diagonal_apply_ne _ hij]

/-- **`⟨N, N⟩ > 0`** at a positive diagonal matrix. -/
theorem hsForm_amariNormal_self_pos [Nonempty d] (hl : ∀ i, 0 < l i) :
    0 < hsForm (amariNormal α (Matrix.diagonal fun i ↦ (l i : ℂ)))
      (amariNormal α (Matrix.diagonal fun i ↦ (l i : ℂ))) := by
  rw [amariNormal_diagonal hl, hsForm_apply, diagonal_mul_diagonal, trace_diagonal]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
  exact Finset.sum_pos (fun i _ ↦ mul_pos (Real.rpow_pos_of_pos (hl i) _)
    (Real.rpow_pos_of_pos (hl i) _)) Finset.univ_nonempty

end Diagonal

end AlphaCurvature.Quantum
