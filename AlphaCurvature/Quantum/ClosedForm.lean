/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import AlphaCurvature.Curvature.Gauss
import AlphaCurvature.Metric
import AlphaCurvature.Quantum.Hypersurface

/-!
# The scalar curvature of the quantum α-geometry at a diagonal state

The quantum α-geometry near a positive definite `ρ₀` is the pullback of the Hilbert–Schmidt form
by the chart `φ(z) = A(ρ₀ + z)` of `ρ₀ + {traceless Hermitian}` (`amariChart`). At a positive
diagonal `ρ₀ = diag λ` the metric and the second fundamental form are diagonal in the real
coordinates `Re uᵢⱼ`, `Im uᵢⱼ` of a matrix (`crd`):

  `g(u, v) = ∑ᵢⱼ kᵢⱼ² Re(uᵢⱼ v̄ᵢⱼ)`,  `h(u, v) = ⟨D²φ(u, v), N⟩ = -∑ᵢⱼ nᵢⱼ kᵢⱼ Re(uᵢⱼ v̄ᵢⱼ)`,

with `k = amariKernel` and `n` the divided difference of `t ↦ t^((1+α)/2)`
(`pullback_amariChart_diagonal`, `hsForm_fderiv_fderiv_amariChart_diagonal`). As in the
classical case (`AlphaCurvature.sum_mul_eq_alphaKernel`) the contractions in a `g`-orthonormal
basis only involve the completeness kernel `∑ₐ crd_p(eₐ) crd_q(eₐ) = crd_q(κ_p)`, where `κ_p` is
the vector representing the coordinate `crd_p` on the tangent space (`kappa`). Off the diagonal
`κ_p` is an explicit pair of matrix units; on the diagonal it is the classical kernel
`AlphaCurvature.alphaKernel`.

The Gauss formula then gives **the closed form** (`scalarCurvature_amariChart_diagonal`): with
`Kᵢⱼ = nᵢⱼ / kᵢⱼ` (`curvKernel`), `c = (1 + α)/2`, `P(s) = ∑ᵢ λᵢˢ` and `W = P(1 + α)`,

  `W · S = (∑ K)² - ∑ K² - 2c (∑ K) P(1+2α)/W + 2c² P(1+3α)/W`,

with sums over all ordered pairs `(i, j)`.
-/

open scoped Matrix.Norms.L2Operator Topology ComplexOrder
open Matrix ContinuousLinearMap Filter Set
open AlphaCurvature.Curvature

namespace AlphaCurvature.Quantum

variable {d : Type*} [Fintype d] [DecidableEq d] {α : ℝ}

/-! ### Traceless Hermitian matrices -/

variable (d) in
/-- The traceless Hermitian matrices: the tangent space of the states. -/
noncomputable def tracelessHermitian : Submodule ℝ (Matrix d d ℂ) :=
  hermitian d ⊓ LinearMap.ker ((Matrix.traceLinearMap d ℂ ℂ).restrictScalars ℝ)

omit [DecidableEq d] in
theorem mem_tracelessHermitian {X : Matrix d d ℂ} :
    X ∈ tracelessHermitian d ↔ X.IsHermitian ∧ trace X = 0 := by
  simp [tracelessHermitian, mem_hermitian]

/-! ### Weighted forms and real coordinates -/

/-- The weighted form `∑ᵢⱼ aᵢⱼ Re(Xᵢⱼ Ȳᵢⱼ)`. -/
noncomputable def wform (a : d → d → ℝ) (X Y : Matrix d d ℂ) : ℝ :=
  ∑ i, ∑ j, a i j * (X i j * star (Y i j)).re

/-- A double sum of a function of the entries of a matrix unit. -/
theorem sum_sum_single (f : d → d → ℂ → ℝ) (hf : ∀ i j, f i j 0 = 0) (i j : d) (z : ℂ) :
    ∑ i', ∑ j', f i' j' (single i j z i' j') = f i j z := by
  rw [Finset.sum_eq_single i (fun i' _ hi' ↦ by
    simp [single_apply_of_row_ne (Ne.symm hi'), hf]) (by simp)]
  rw [Finset.sum_eq_single j (fun j' _ hj' ↦ by
    simp [single_apply_of_col_ne _ _ (Ne.symm hj'), hf]) (by simp)]
  simp

omit [DecidableEq d] in
theorem wform_add_left (a : d → d → ℝ) (X X' Y : Matrix d d ℂ) :
    wform a (X + X') Y = wform a X Y + wform a X' Y := by
  simp only [wform, Matrix.add_apply, add_mul, Complex.add_re, mul_add, Finset.sum_add_distrib]

omit [DecidableEq d] in
theorem wform_add_right (a : d → d → ℝ) (X Y Y' : Matrix d d ℂ) :
    wform a X (Y + Y') = wform a X Y + wform a X Y' := by
  simp only [wform, Matrix.add_apply, star_add, mul_add, Complex.add_re, Finset.sum_add_distrib]

omit [DecidableEq d] in
theorem wform_zero_right (a : d → d → ℝ) (X : Matrix d d ℂ) : wform a X 0 = 0 := by
  simp [wform]

theorem wform_single_left (a : d → d → ℝ) (i j : d) (z : ℂ) (Y : Matrix d d ℂ) :
    wform a (single i j z) Y = a i j * (z * star (Y i j)).re :=
  sum_sum_single (fun i' j' x ↦ a i' j' * (x * star (Y i' j')).re) (by simp) i j z

theorem wform_single_right (a : d → d → ℝ) (X : Matrix d d ℂ) (i j : d) (z : ℂ) :
    wform a X (single i j z) = a i j * (X i j * star z).re :=
  sum_sum_single (fun i' j' x ↦ a i' j' * (X i' j' * star x).re) (by simp) i j z

theorem wform_diagonal_right (a : d → d → ℝ) (X : Matrix d d ℂ) (f : d → ℂ) :
    wform a X (Matrix.diagonal f) = ∑ m, a m m * (X m m * star (f m)).re := by
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Finset.sum_eq_single m (fun j _ hj ↦ by simp [diagonal_apply_ne _ (Ne.symm hj)])
    (by simp), diagonal_apply_eq]

/-- The real coordinates of a matrix: the real (`true`) and imaginary (`false`) parts of its
entries. -/
noncomputable def crd (p : d × d × Bool) : Matrix d d ℂ →ₗ[ℝ] ℝ :=
  (if p.2.2 then Complex.reLm else Complex.imLm).comp (Matrix.entryLinearMap ℝ ℂ p.1 p.2.1)

omit [Fintype d] [DecidableEq d] in
@[simp]
theorem crd_true (i j : d) (X : Matrix d d ℂ) : crd (i, j, true) X = (X i j).re := by
  simp [crd]

omit [Fintype d] [DecidableEq d] in
@[simp]
theorem crd_false (i j : d) (X : Matrix d d ℂ) : crd (i, j, false) X = (X i j).im := by
  simp [crd]

omit [DecidableEq d] in
/-- Summing over the coordinates: `∑_p a_p crd_p(X) crd_p(Y) = wform a X Y`. -/
theorem sum_crd_mul (a : d → d → ℝ) (X Y : Matrix d d ℂ) :
    ∑ p : d × d × Bool, a p.1 p.2.1 * (crd p X * crd p Y) = wform a X Y := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Fintype.sum_bool, crd_true, crd_true, crd_false, crd_false, Complex.mul_re,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- The Hilbert–Schmidt form of two Schur multiples, `Xᵢⱼ = aᵢⱼ uᵢⱼ` and `Yᵢⱼ = bᵢⱼ vᵢⱼ`, with `b`
symmetric and `v` Hermitian. -/
theorem hsForm_schur {a b : d → d → ℝ} (hb : ∀ i j, b i j = b j i) {X Y u v : Matrix d d ℂ}
    (hX : ∀ i j, X i j = a i j * u i j) (hY : ∀ i j, Y i j = b i j * v i j)
    (hv : v.IsHermitian) : hsForm X Y = wform (fun i j ↦ a i j * b i j) u v := by
  rw [hsForm_apply, Matrix.trace, wform, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [diag_apply, mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hX, hY, hb j i, ← hv.apply j i,
    show (a i j : ℂ) * u i j * (b i j * star (v i j)) =
      ((a i j * b i j : ℝ) : ℂ) * (u i j * star (v i j)) by push_cast; ring,
    Complex.re_ofReal_mul]

/-! ### The metric and the second fundamental form at a diagonal state -/

section Diagonal

variable {l : d → ℝ}

/-- The kernel of `D A` at `diag λ`. -/
local notation "kk" l => fun i j ↦ amariKernel α (l i) (l j)

theorem amariKernel_self_sq {a : ℝ} (ha : 0 < a) : amariKernel α a a ^ 2 = a ^ (-1 - α) := by
  have h1 := rpow_mul_amariKernel_self (α := α) ha
  have h2 := rpow_neg_one_sub_mul_rpow ha α
  have h3 : amariKernel α a a ^ 2 * a ^ (1 + α) = 1 := by
    have : a ^ (1 + α) = a ^ ((1 + α) / 2) * a ^ ((1 + α) / 2) := by
      rw [← Real.rpow_add ha]; ring_nf
    rw [this]
    linear_combination (amariKernel α a a * a ^ ((1 + α) / 2) + 1) * h1
  have hp : a ^ (1 + α) ≠ 0 := (Real.rpow_pos_of_pos ha _).ne'
  exact mul_right_cancel₀ hp (h3.trans h2.symm)

theorem differentiableAt_amari_diagonal (hl : ∀ i, 0 < l i) :
    DifferentiableAt ℝ (amari α) (Matrix.diagonal fun i ↦ (l i : ℂ)) :=
  (contDiffAt_amari_of_isUnit (isUnit_logPath_of_posDef (posDef_diagonal_ofReal hl))
    1).differentiableAt one_ne_zero

omit [Fintype d] [DecidableEq d] in
theorem chart_zero (V : Submodule ℝ (Matrix d d ℂ)) (ρ₀ : Matrix d d ℂ) :
    V.subtypeL (0 : V) + ρ₀ = ρ₀ := by simp

/-- **The metric at a diagonal state**: `g(u, v) = ∑ᵢⱼ kᵢⱼ² Re(uᵢⱼ v̄ᵢⱼ)`. -/
theorem pullback_amariChart_diagonal (hl : ∀ i, 0 < l i) (u v : tracelessHermitian d) :
    pullback (amariChart α (tracelessHermitian d) (Matrix.diagonal fun i ↦ (l i : ℂ)))
      (fun _ ↦ hsForm) 0 u v =
      wform (fun i j ↦ amariKernel α (l i) (l j) ^ 2) u v := by
  have hd := differentiableAt_amari_diagonal (α := α) hl
  rw [← chart_zero (tracelessHermitian d) (Matrix.diagonal fun i ↦ (l i : ℂ))] at hd
  rw [pullback_apply, fderiv_amariChart hd, fderiv_amariChart hd, chart_zero]
  rw [hsForm_schur (a := kk l) (b := kk l) (fun i j ↦ amariKernel_comm _ _)
    (fderiv_amari_diagonal_apply hl u) (fderiv_amari_diagonal_apply hl v)
    (mem_tracelessHermitian.1 v.2).1]
  simp only [sq]

/-- **The second fundamental form at a diagonal state**:
`⟨D²φ(u, v), N⟩ = -∑ᵢⱼ nᵢⱼ kᵢⱼ Re(uᵢⱼ v̄ᵢⱼ)`. -/
theorem hsForm_fderiv_fderiv_amariChart_diagonal (hl : ∀ i, 0 < l i)
    (u v : tracelessHermitian d) :
    hsForm (fderiv ℝ (fderiv ℝ (amariChart α (tracelessHermitian d)
      (Matrix.diagonal fun i ↦ (l i : ℂ)))) 0 u v)
      (amariNormal α (Matrix.diagonal fun i ↦ (l i : ℂ))) =
      -wform (fun i j ↦ powKernel ((1 + α) / 2) (l i) (l j) * amariKernel α (l i) (l j)) u v := by
  rw [hsForm_fderiv_fderiv_amariChart (posDef_diagonal_ofReal hl)
    (fun v hv ↦ mem_tracelessHermitian.1 hv) u v]
  congr 1
  exact hsForm_schur (fun i j ↦ amariKernel_comm _ _)
    (fderiv_matPow_diagonal_apply _ hl u) (fderiv_amari_diagonal_apply hl v)
    (mem_tracelessHermitian.1 v.2).1

/-- The metric is positive definite on the traceless Hermitian matrices. -/
theorem pullback_amariChart_diagonal_self_pos (hl : ∀ i, 0 < l i) {u : tracelessHermitian d}
    (hu : u ≠ 0) :
    0 < pullback (amariChart α (tracelessHermitian d) (Matrix.diagonal fun i ↦ (l i : ℂ)))
      (fun _ ↦ hsForm) 0 u u := by
  rw [pullback_amariChart_diagonal hl]
  obtain ⟨i, j, hij⟩ : ∃ i j, (u : Matrix d d ℂ) i j ≠ 0 := by
    by_contra! h
    exact hu (Subtype.ext (Matrix.ext h))
  have hterm : ∀ i j, amariKernel α (l i) (l j) ^ 2 *
      ((u : Matrix d d ℂ) i j * star ((u : Matrix d d ℂ) i j)).re =
      amariKernel α (l i) (l j) ^ 2 * Complex.normSq ((u : Matrix d d ℂ) i j) := fun i j ↦ by
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  simp only [wform, hterm]
  have hnn : ∀ i j, 0 ≤ amariKernel α (l i) (l j) ^ 2 *
      Complex.normSq ((u : Matrix d d ℂ) i j) := fun i j ↦
    mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  refine Finset.sum_pos' (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hnn i j)
    ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun j _ ↦ hnn i j) ⟨j, Finset.mem_univ _, ?_⟩⟩
  exact mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2
    (amariKernel_ne_zero (hl i) (hl j)))))
    (Complex.normSq_pos.2 hij)

theorem isInvertible_pullback_amariChart_diagonal (hl : ∀ i, 0 < l i) :
    (pullback (amariChart α (tracelessHermitian d) (Matrix.diagonal fun i ↦ (l i : ℂ)))
      (fun _ ↦ hsForm) 0).IsInvertible :=
  LinearMap.BilinForm.isInvertible_of_pos fun _ hu ↦ pullback_amariChart_diagonal_self_pos hl hu


/-! ### The completeness kernel -/

/-- The kernel of the second fundamental form: `nᵢⱼ kᵢⱼ`. -/
noncomputable def sffKernel (α a b : ℝ) : ℝ :=
  powKernel ((1 + α) / 2) a b * amariKernel α a b

/-- **The curvature kernel** `Kᵢⱼ = nᵢⱼ / kᵢⱼ`: the divided difference of the gradient
`t ↦ t^((1+α)/2)` of the level-set function, per unit of `A`. -/
noncomputable def curvKernel (α a b : ℝ) : ℝ :=
  powKernel ((1 + α) / 2) a b / amariKernel α a b

theorem sffKernel_comm (a b : ℝ) : sffKernel α a b = sffKernel α b a := by
  rw [sffKernel, sffKernel, powKernel_comm, amariKernel_comm]

/-- The coefficient of the off-diagonal kernel vectors: `1/(2k²)`, times `i` for the imaginary
coordinate. -/
noncomputable def kappaCoeff (α : ℝ) (l : d → ℝ) (p : d × d × Bool) : ℂ :=
  (if p.2.2 then 1 else Complex.I) * (((2 * amariKernel α (l p.1) (l p.2.1) ^ 2)⁻¹ : ℝ) : ℂ)

/-- **The kernel vectors**: `κ_p` represents the coordinate `crd_p` on the traceless Hermitian
matrices (`wform_kappa`). Off the diagonal it is a pair of matrix units, on the diagonal the
classical kernel `alphaKernel`. -/
noncomputable def kappa (α : ℝ) (l : d → ℝ) (p : d × d × Bool) : Matrix d d ℂ :=
  if p.1 = p.2.1 then
    (if p.2.2 then Matrix.diagonal fun m ↦ (alphaKernel α l m p.1 : ℂ) else 0)
  else single p.1 p.2.1 (kappaCoeff α l p) + single p.2.1 p.1 (star (kappaCoeff α l p))

theorem kappa_mem (hl : ∀ i, 0 < l i) (p : d × d × Bool) :
    kappa α l p ∈ tracelessHermitian d := by
  obtain ⟨i, j, r⟩ := p
  rw [mem_tracelessHermitian]
  by_cases h : i = j
  · subst h
    cases r
    · simp [kappa]
    · simp only [kappa, ↓reduceIte]
      refine ⟨isHermitian_diagonal_ofReal _, ?_⟩
      rw [trace_diagonal, ← Complex.ofReal_sum, sum_alphaKernel hl i, Complex.ofReal_zero]
  · simp only [kappa, h, ↓reduceIte]
    refine ⟨isHermitian_single_add _ _ _, ?_⟩
    rw [trace_add, trace_single_eq_of_ne (h := h), trace_single_eq_of_ne (h := Ne.symm h),
      add_zero]

/-- `κ_p` represents `crd_p`: `g(v, κ_p) = crd_p(v)` for traceless Hermitian `v`. -/
theorem wform_kappa (hl : ∀ i, 0 < l i) {v : Matrix d d ℂ} (hv : v ∈ tracelessHermitian d)
    (p : d × d × Bool) :
    wform (fun i j ↦ amariKernel α (l i) (l j) ^ 2) v (kappa α l p) = crd p v := by
  obtain ⟨hH, htr⟩ := mem_tracelessHermitian.1 hv
  obtain ⟨i, j, r⟩ := p
  by_cases h : i = j
  · subst h
    cases r
    · simp only [kappa, ↓reduceIte, Bool.false_eq_true, wform_zero_right, crd_false]
      have := congrArg Complex.im (hH.apply i i)
      rw [Complex.star_def, Complex.conj_im] at this
      linarith
    · simp only [kappa, ↓reduceIte, wform_diagonal_right, crd_true]
      have hsum : (fun m ↦ (v m m).re) ∈ simplexTangent d := by
        rw [mem_simplexTangent, ← Complex.re_sum]
        exact congrArg Complex.re htr
      rw [← alphaForm_alphaKernel (α := α) hl hsum i, alphaForm_apply]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [amariKernel_self_sq (hl m), Complex.star_def, Complex.conj_ofReal,
        Complex.re_mul_ofReal]
  · have hk := amariKernel_ne_zero (α := α) (hl i) (hl j)
    simp only [kappa, h, ↓reduceIte, wform_add_right, wform_single_right, star_star]
    rw [← hH.apply j i, amariKernel_comm (l j) (l i)]
    have key : ∀ s : ℂ, amariKernel α (l i) (l j) ^ 2 *
        (v i j * star (s * (((2 * amariKernel α (l i) (l j) ^ 2)⁻¹ : ℝ) : ℂ))).re +
        amariKernel α (l i) (l j) ^ 2 *
        (star (v i j) * (s * (((2 * amariKernel α (l i) (l j) ^ 2)⁻¹ : ℝ) : ℂ))).re =
        (v i j * star s).re := by
      intro s
      simp only [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.mul_re,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
      field_simp
      ring
    cases r
    · simpa [kappaCoeff, Complex.mul_re] using key Complex.I
    · simpa [kappaCoeff] using key 1

/-- **The completeness kernel**: in a `g`-orthonormal basis `e`,
`∑ₐ crd_p(eₐ) crd_q(eₐ) = crd_q(κ_p)`. -/
theorem sum_crd_mul_crd (hl : ∀ i, 0 < l i) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (tracelessHermitian d))
    (hb : ∀ a c, pullback (amariChart α (tracelessHermitian d)
      (Matrix.diagonal fun i ↦ (l i : ℂ))) (fun _ ↦ hsForm) 0 (b a) (b c) =
      if a = c then 1 else 0) (p q : d × d × Bool) :
    ∑ a, crd p (b a : Matrix d d ℂ) * crd q (b a : Matrix d d ℂ) = crd q (kappa α l p) := by
  let κ : tracelessHermitian d := ⟨kappa α l p, kappa_mem hl p⟩
  have hrepr : ∀ a, b.repr κ a = crd p (b a : Matrix d d ℂ) := fun a ↦ by
    rw [repr_eq_of_orthonormal (G := pullback (amariChart α (tracelessHermitian d)
      (Matrix.diagonal fun i ↦ (l i : ℂ))) (fun _ ↦ hsForm)) (x := 0) b hb,
      pullback_amariChart_diagonal hl]
    exact wform_kappa hl (b a).2 p
  have := congrArg (fun y : tracelessHermitian d ↦ crd q (y : Matrix d d ℂ)) (b.sum_repr κ)
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hrepr,
    smul_eq_mul] at this
  exact this

/-! ### The two contractions -/

section Contraction

variable {ι P : Type*} [Fintype ι] [Fintype P] (e : ι → P → ℝ) (K : P → P → ℝ)
  (hK : ∀ p q, ∑ a, e a p * e a q = K p q) (c : P → ℝ)
include hK

omit [Fintype d] [DecidableEq d] in
theorem sum_sum_mul_self_eq : ∑ a, ∑ p, c p * (e a p * e a p) = ∑ p, c p * K p p := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ ↦ by rw [← Finset.mul_sum, hK]

omit [Fintype d] [DecidableEq d] in
theorem sum_sum_sq_sum_eq :
    ∑ a, ∑ b, (∑ p, c p * (e a p * e b p)) ^ 2 = ∑ p, ∑ q, c p * c q * K p q ^ 2 := by
  calc ∑ a, ∑ b, (∑ p, c p * (e a p * e b p)) ^ 2
      = ∑ b, ∑ a, ∑ p, ∑ q, e a p * e a q * (c p * c q * (e b p * e b q)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
        rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by ring
    _ = ∑ b, ∑ p, ∑ q, e b p * e b q * (K p q * (c p * c q)) := by
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        rw [sum_mul_mul_eq e K hK]
        exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by ring
    _ = ∑ p, ∑ q, c p * c q * K p q ^ 2 := by
        rw [sum_mul_mul_eq e K hK]
        exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by ring

end Contraction

/-- **The trace of `h`**: `∑ₐ h(eₐ, eₐ) = -∑_p c_p crd_p(κ_p)`. -/
theorem sum_hsForm_fderiv_fderiv_self (hl : ∀ i, 0 < l i) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℝ (tracelessHermitian d))
    (hb : ∀ a c, pullback (amariChart α (tracelessHermitian d)
      (Matrix.diagonal fun i ↦ (l i : ℂ))) (fun _ ↦ hsForm) 0 (b a) (b c) =
      if a = c then 1 else 0) :
    ∑ a, hsForm (fderiv ℝ (fderiv ℝ (amariChart α (tracelessHermitian d)
      (Matrix.diagonal fun i ↦ (l i : ℂ)))) 0 (b a) (b a))
      (amariNormal α (Matrix.diagonal fun i ↦ (l i : ℂ))) =
      -∑ p : d × d × Bool, sffKernel α (l p.1) (l p.2.1) * crd p (kappa α l p) := by
  simp only [hsForm_fderiv_fderiv_amariChart_diagonal hl, Finset.sum_neg_distrib,
    ← sum_crd_mul (fun i j ↦ powKernel ((1 + α) / 2) (l i) (l j) * amariKernel α (l i) (l j))]
  have h := sum_sum_mul_self_eq (fun a p ↦ crd p (b a : Matrix d d ℂ))
    (fun p q ↦ crd q (kappa α l p)) (sum_crd_mul_crd hl b hb)
    (fun p : d × d × Bool ↦ powKernel ((1 + α) / 2) (l p.1) (l p.2.1) *
      amariKernel α (l p.1) (l p.2.1))
  rw [h]
  rfl

/-- **The square of `h`**: `∑ₐ_b h(eₐ, e_b)² = ∑_p c_p · wform c κ_p κ_p`. -/
theorem sum_sum_hsForm_fderiv_fderiv_sq (hl : ∀ i, 0 < l i) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℝ (tracelessHermitian d))
    (hb : ∀ a c, pullback (amariChart α (tracelessHermitian d)
      (Matrix.diagonal fun i ↦ (l i : ℂ))) (fun _ ↦ hsForm) 0 (b a) (b c) =
      if a = c then 1 else 0) :
    ∑ a, ∑ c, hsForm (fderiv ℝ (fderiv ℝ (amariChart α (tracelessHermitian d)
      (Matrix.diagonal fun i ↦ (l i : ℂ)))) 0 (b a) (b c))
      (amariNormal α (Matrix.diagonal fun i ↦ (l i : ℂ))) ^ 2 =
      ∑ p : d × d × Bool, sffKernel α (l p.1) (l p.2.1) *
        wform (fun i j ↦ sffKernel α (l i) (l j)) (kappa α l p) (kappa α l p) := by
  simp only [hsForm_fderiv_fderiv_amariChart_diagonal hl, neg_sq,
    ← sum_crd_mul (fun i j ↦ powKernel ((1 + α) / 2) (l i) (l j) * amariKernel α (l i) (l j))]
  have h := sum_sum_sq_sum_eq (fun a p ↦ crd p (b a : Matrix d d ℂ))
    (fun p q ↦ crd q (kappa α l p)) (sum_crd_mul_crd hl b hb)
    (fun p : d × d × Bool ↦ powKernel ((1 + α) / 2) (l p.1) (l p.2.1) *
      amariKernel α (l p.1) (l p.2.1))
  rw [h]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [← sum_crd_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ ↦ by simp only [sffKernel]; ring

/-! ### Evaluating the contractions -/

omit [DecidableEq d] in
theorem sum_coords (F : d × d × Bool → ℝ) :
    ∑ p, F p = ∑ i, ∑ j, (F (i, j, true) + F (i, j, false)) := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [Fintype.sum_prod_type]; simp

theorem crd_kappa_self (i j : d) (r : Bool) :
    crd (i, j, r) (kappa α l (i, j, r)) =
      if i = j then (if r then alphaKernel α l i i else 0)
      else (2 * amariKernel α (l i) (l j) ^ 2)⁻¹ := by
  by_cases h : i = j
  · subst h
    cases r <;> simp [kappa]
  · have hji : ¬(j = i ∧ i = j) := fun h' ↦ h h'.2
    cases r <;> simp only [kappa, h, ↓reduceIte, crd_false, crd_true, Matrix.add_apply,
      single_apply_same, single_apply_of_ne (h := hji), add_zero, kappaCoeff,
      Bool.false_eq_true, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, one_mul, mul_zero, zero_add]

theorem wform_kappa_self (i j : d) (r : Bool) :
    wform (fun i j ↦ sffKernel α (l i) (l j)) (kappa α l (i, j, r)) (kappa α l (i, j, r)) =
      if i = j then (if r then ∑ m, sffKernel α (l m) (l m) * alphaKernel α l m i ^ 2 else 0)
      else 2 * sffKernel α (l i) (l j) * ((2 * amariKernel α (l i) (l j) ^ 2)⁻¹) ^ 2 := by
  by_cases h : i = j
  · subst h
    cases r
    · simp [kappa, wform_zero_right]
    · simp only [kappa, ↓reduceIte, wform_diagonal_right, diagonal_apply_eq]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re, sq]
  · have hji : ¬(j = i ∧ i = j) := fun h' ↦ h h'.2
    have hij' : ¬(i = j ∧ j = i) := fun h' ↦ h h'.1
    have hnorm : Complex.normSq (kappaCoeff α l (i, j, r)) =
        ((2 * amariKernel α (l i) (l j) ^ 2)⁻¹) ^ 2 := by
      cases r <;> simp only [kappaCoeff, Complex.normSq_mul, Complex.normSq_ofReal,
        Complex.normSq_one, Complex.normSq_I, Bool.false_eq_true, ↓reduceIte] <;> ring
    simp only [kappa, h, ↓reduceIte, wform_add_left, wform_single_left, Matrix.add_apply,
      single_apply_same, single_apply_of_ne (h := hji), single_apply_of_ne (h := hij'),
      add_zero, zero_add, Complex.star_def, Complex.conj_conj, Complex.mul_conj,
      mul_comm ((starRingEnd ℂ) (kappaCoeff α l (i, j, r))) (kappaCoeff α l (i, j, r)),
      Complex.ofReal_re, hnorm, sffKernel_comm (l j) (l i)]
    ring

/-- The trace of `h`, evaluated: `∑_p c_p crd_p(κ_p)`. -/
theorem sum_sffKernel_crd_kappa (hl : ∀ i, 0 < l i) :
    ∑ p : d × d × Bool, sffKernel α (l p.1) (l p.2.1) * crd p (kappa α l p) =
      ∑ i, ∑ j, (if i = j then sffKernel α (l i) (l i) * alphaKernel α l i i
        else curvKernel α (l i) (l j)) := by
  rw [sum_coords]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [crd_kappa_self]
  by_cases h : i = j
  · subst h; simp
  · have hk := amariKernel_ne_zero (α := α) (hl i) (hl j)
    simp only [h, ↓reduceIte, sffKernel, curvKernel]
    field_simp
    ring

/-- The square of `h`, evaluated: `∑_p c_p · wform c κ_p κ_p`. -/
theorem sum_sffKernel_wform_kappa (hl : ∀ i, 0 < l i) :
    ∑ p : d × d × Bool, sffKernel α (l p.1) (l p.2.1) *
      wform (fun i j ↦ sffKernel α (l i) (l j)) (kappa α l p) (kappa α l p) =
      ∑ i, ∑ j, (if i = j then sffKernel α (l i) (l i) *
          ∑ m, sffKernel α (l m) (l m) * alphaKernel α l m i ^ 2
        else curvKernel α (l i) (l j) ^ 2) := by
  rw [sum_coords]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [wform_kappa_self]
  by_cases h : i = j
  · subst h; simp
  · have hk := amariKernel_ne_zero (α := α) (hl i) (hl j)
    simp only [h, ↓reduceIte, sffKernel, curvKernel]
    field_simp
    ring

/-! ### The diagonal block -/

theorem curvKernel_self {a : ℝ} (ha : 0 < a) : curvKernel α a a = (1 + α) / 2 * a ^ α := by
  have h1 := rpow_mul_amariKernel_self (α := α) ha
  have hk : amariKernel α a a = (a ^ ((1 + α) / 2))⁻¹ :=
    eq_inv_of_mul_eq_one_right h1
  rw [curvKernel, powKernel_self, hk, div_inv_eq_mul, mul_assoc, ← Real.rpow_add ha]
  ring_nf

/-- On the diagonal, `c_ii wᵢ = K_ii` with `wᵢ = λᵢ^(1+α)`. -/
theorem sffKernel_self_mul_rpow {a : ℝ} (ha : 0 < a) :
    sffKernel α a a * a ^ (1 + α) = curvKernel α a a := by
  have hk := amariKernel_ne_zero (α := α) ha ha
  have h2 : amariKernel α a a ^ 2 * a ^ (1 + α) = 1 := by
    rw [amariKernel_self_sq ha, rpow_neg_one_sub_mul_rpow ha]
  rw [sffKernel, curvKernel, eq_div_iff hk]
  linear_combination powKernel ((1 + α) / 2) a a * h2

theorem sum_sum_ite (A : d → ℝ) (B : d → d → ℝ) :
    ∑ i, ∑ j, (if i = j then A i else B i j) = ∑ i, ∑ j, B i j + ∑ i, (A i - B i i) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have : ∀ j, (if i = j then A i else B i j) = B i j + if i = j then A i - B i i else 0 :=
    fun j ↦ by split_ifs with h <;> [subst h; skip] <;> ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The diagonal part of the trace. -/
theorem sum_sffKernel_alphaKernel (hl : ∀ i, 0 < l i) :
    ∑ i, sffKernel α (l i) (l i) * alphaKernel α l i i =
      ∑ i, curvKernel α (l i) (l i) -
        (∑ i, curvKernel α (l i) (l i) * l i ^ (1 + α)) / ∑ i, l i ^ (1 + α) := by
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [alphaKernel, ↓reduceIte, ← sffKernel_self_mul_rpow (hl i)]
  ring

/-- The algebra of the diagonal block: for `aₘᵢ = wₘ δₘᵢ - wₘ wᵢ / W`,
`∑ᵢ cᵢ ∑ₘ cₘ aₘᵢ² = ∑ (cw)² - 2 ∑ (cw)² w / W + (∑ c w²)² / W²`. -/
theorem sum_mul_sum_mul_sq_eq (cc w : d → ℝ) (W : ℝ)
    (aK : d → d → ℝ) (haK : ∀ m i, aK m i = (if m = i then w m else 0) - w m * w i / W) :
    ∑ i, cc i * ∑ m, cc m * aK m i ^ 2 =
      ∑ i, (cc i * w i) ^ 2 - 2 * (∑ i, (cc i * w i) ^ 2 * w i) / W +
        (∑ i, cc i * w i * w i) ^ 2 / W ^ 2 := by
  have hsq : ∀ m i, aK m i ^ 2 =
      (if m = i then w m ^ 2 - 2 * w m ^ 2 * w i / W else 0) + w m ^ 2 * w i ^ 2 / W ^ 2 := by
    intro m i
    rw [haK]
    split_ifs with h
    · subst h; ring
    · ring
  set S2 := ∑ m, cc m * w m ^ 2
  have hin : ∀ i, ∑ m, cc m * aK m i ^ 2 =
      cc i * (w i ^ 2 - 2 * w i ^ 2 * w i / W) + S2 * w i ^ 2 / W ^ 2 := by
    intro i
    simp only [hsq, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, S2, Finset.sum_mul, Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun m _ ↦ by ring
  have e1 : ∀ i, cc i * (cc i * (w i ^ 2 - 2 * w i ^ 2 * w i / W) + S2 * w i ^ 2 / W ^ 2) =
      (cc i * w i) ^ 2 - 2 * ((cc i * w i) ^ 2 * w i) / W + S2 * (cc i * w i ^ 2) / W ^ 2 :=
    fun i ↦ by ring
  have e2 : ∑ i, cc i * w i * w i = S2 := Finset.sum_congr rfl fun i _ ↦ by ring
  simp only [hin, e1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
    ← Finset.mul_sum, e2]
  ring

/-- The diagonal part of the square. -/
theorem sum_sffKernel_sum_alphaKernel_sq (hl : ∀ i, 0 < l i) :
    ∑ i, sffKernel α (l i) (l i) * ∑ m, sffKernel α (l m) (l m) * alphaKernel α l m i ^ 2 =
      ∑ i, curvKernel α (l i) (l i) ^ 2 -
        2 * (∑ i, curvKernel α (l i) (l i) ^ 2 * l i ^ (1 + α)) / ∑ i, l i ^ (1 + α) +
        (∑ i, curvKernel α (l i) (l i) * l i ^ (1 + α)) ^ 2 / (∑ i, l i ^ (1 + α)) ^ 2 := by
  rw [sum_mul_sum_mul_sq_eq (fun i ↦ sffKernel α (l i) (l i)) (fun i ↦ l i ^ (1 + α))
    (∑ i, l i ^ (1 + α)) (alphaKernel α l) fun m i ↦ by rw [alphaKernel]]
  simp only [sffKernel_self_mul_rpow (hl _)]

/-! ### The closed form -/

theorem hsForm_amariNormal_self_diagonal (hl : ∀ i, 0 < l i) :
    hsForm (amariNormal α (Matrix.diagonal fun i ↦ (l i : ℂ)))
      (amariNormal α (Matrix.diagonal fun i ↦ (l i : ℂ))) = ∑ i, l i ^ (1 + α) := by
  rw [amariNormal_diagonal hl, hsForm_apply, diagonal_mul_diagonal, trace_diagonal]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Real.rpow_add (hl i)]
  ring_nf

omit [DecidableEq d] in
theorem sum_curvKernel_self_mul_rpow (hl : ∀ i, 0 < l i) :
    ∑ i, curvKernel α (l i) (l i) * l i ^ (1 + α) =
      (1 + α) / 2 * ∑ i, l i ^ (1 + 2 * α) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [curvKernel_self (hl i), mul_assoc, ← Real.rpow_add (hl i)]
  ring_nf

omit [DecidableEq d] in
theorem sum_curvKernel_self_sq_mul_rpow (hl : ∀ i, 0 < l i) :
    ∑ i, curvKernel α (l i) (l i) ^ 2 * l i ^ (1 + α) =
      ((1 + α) / 2) ^ 2 * ∑ i, l i ^ (1 + 3 * α) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [curvKernel_self (hl i), mul_pow, mul_assoc, ← Real.rpow_mul_natCast (hl i).le,
    ← Real.rpow_add (hl i)]
  push_cast
  ring_nf

/-- **The scalar curvature of the quantum α-geometry at a diagonal state**: with
`Kᵢⱼ = curvKernel α λᵢ λⱼ`, `c = (1 + α)/2`, `P(s) = ∑ᵢ λᵢˢ` and `W = P(1 + α)`,
`S = [(∑ K)² - ∑ K² - 2c (∑ K) P(1+2α)/W + 2c² P(1+3α)/W] / W`, sums over all `(i, j)`. -/
theorem scalarCurvature_amariChart_diagonal [Nonempty d] (hl : ∀ i, 0 < l i) :
    scalarCurvature (pullback (amariChart α (tracelessHermitian d)
      (Matrix.diagonal fun i ↦ (l i : ℂ))) fun _ ↦ hsForm) 0 =
      ((∑ i, ∑ j, curvKernel α (l i) (l j)) ^ 2 - ∑ i, ∑ j, curvKernel α (l i) (l j) ^ 2 -
        2 * ((1 + α) / 2) * (∑ i, ∑ j, curvKernel α (l i) (l j)) *
          (∑ i, l i ^ (1 + 2 * α)) / ∑ i, l i ^ (1 + α) +
        2 * ((1 + α) / 2) ^ 2 * (∑ i, l i ^ (1 + 3 * α)) / ∑ i, l i ^ (1 + α)) /
        ∑ i, l i ^ (1 + α) := by
  set D := Matrix.diagonal fun i ↦ (l i : ℂ)
  have hD : D.PosDef := posDef_diagonal_ofReal hl
  have hV : ∀ v ∈ tracelessHermitian d, v.IsHermitian ∧ trace v = 0 :=
    fun v hv ↦ mem_tracelessHermitian.1 hv
  have hVH : ∀ v ∈ tracelessHermitian d, v.IsHermitian := fun v hv ↦ (hV v hv).1
  obtain ⟨b, hb⟩ := exists_orthonormal_basis
    (pullback (amariChart α (tracelessHermitian d) D) (fun _ ↦ hsForm) 0)
    (fun v w ↦ by simp only [pullback_apply]; exact hsForm_comm _ _)
    (fun v hv ↦ pullback_amariChart_diagonal_self_pos hl hv)
  have hd : DifferentiableAt ℝ (amari α) D := differentiableAt_amari_diagonal hl
  rw [← chart_zero (tracelessHermitian d) D] at hd
  have hperp : ∀ m ∈ hermitian d,
      (∀ u, hsForm m (fderiv ℝ (amariChart α (tracelessHermitian d) D) 0 u) = 0) →
        ∃ t : ℝ, m = t • amariNormal α D := fun m hm h ↦
    exists_eq_smul_amariNormal hl (mem_hermitian.1 hm) fun u hu htr ↦ by
      have := h ⟨u, mem_tracelessHermitian.2 ⟨hu, htr⟩⟩
      rwa [fderiv_amariChart hd, chart_zero] at this
  rw [scalarCurvature_pullback_const_of_normal (contDiffAt_amariChart hD 3) hsForm_comm
    (isInvertible_pullback_amariChart_diagonal hl) (hermitian d) (fderiv_amariChart_mem hD hVH)
    (fderiv_fderiv_amariChart_mem hD hVH) (amariNormal α D)
    (hsForm_amariNormal_fderiv_amariChart hD hV) (hsForm_amariNormal_self_pos hl).ne' hperp b hb]
  rw [sum_hsForm_fderiv_fderiv_self hl b hb, sum_sum_hsForm_fderiv_fderiv_sq hl b hb,
    sum_sffKernel_crd_kappa hl, sum_sffKernel_wform_kappa hl, sum_sum_ite, sum_sum_ite,
    hsForm_amariNormal_self_diagonal hl, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_sffKernel_alphaKernel hl, sum_sffKernel_sum_alphaKernel_sq hl,
    sum_curvKernel_self_mul_rpow hl, sum_curvKernel_self_sq_mul_rpow hl]
  have hW : (∑ i, l i ^ (1 + α)) ≠ 0 :=
    (Finset.sum_pos (fun i _ ↦ Real.rpow_pos_of_pos (hl i) _) Finset.univ_nonempty).ne'
  field_simp
  ring

theorem curvKernel_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : curvKernel 0 a b = 1 / 2 := by
  have hk := amariKernel_ne_zero (α := 0) ha hb
  simp only [amariKernel, zero_ne_one, ↓reduceIte, sub_zero, div_one] at hk
  simp only [curvKernel, amariKernel, zero_ne_one, ↓reduceIte, sub_zero, div_one, add_zero]
  have hp : powKernel (1 / 2) a b ≠ 0 := right_ne_zero_of_mul hk
  field_simp

/-- **At `α = 0`** (`p = 2`, the Wigner–Yanase metric) on states, `S = (n² - 1)(n² - 2)/4`: the
sphere of radius `2` in the `n²`-dimensional real space of Hermitian matrices. -/
theorem scalarCurvature_amariChart_diagonal_zero [Nonempty d] (hl : ∀ i, 0 < l i)
    (h1 : ∑ i, l i = 1) :
    scalarCurvature (pullback (amariChart 0 (tracelessHermitian d)
      (Matrix.diagonal fun i ↦ (l i : ℂ))) fun _ ↦ hsForm) 0 =
      ((Fintype.card d : ℝ) ^ 2 - 1) * ((Fintype.card d : ℝ) ^ 2 - 2) / 4 := by
  rw [scalarCurvature_amariChart_diagonal hl]
  simp only [curvKernel_zero (hl _) (hl _), mul_zero, add_zero, Real.rpow_one, h1,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end Diagonal

end AlphaCurvature.Quantum
