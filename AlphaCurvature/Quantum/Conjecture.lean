/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import AlphaCurvature.Quantum.ExcessSign

/-!
# The quantum α-geometry curvature conjecture

**Gibilisco–Isola, Conjecture 4.2**: the scalar curvature of the quantum α-geometry, the pullback
of the Hilbert–Schmidt form by `ρ ↦ p ρ^(1/p)` (`p = 2/(1 - α)`, and `log` at `p = ∞`), is a
strictly Schur-monotone function of the eigenvalues: Schur-increasing for `p ∈ (2, ∞]`
(`0 < α ≤ 1`) and Schur-decreasing for `p ∈ (1, 2)` (`-1 < α < 0`), on every number of points.

The scalar curvature at a positive definite `ρ` is `S_cl(λ) + E(λ)` in the eigenvalues `λ`
(`scalarCurvature_amariChart_eq_add`): the classical α-curvature plus the quantum excess. The
classical part is Schur-monotone, not strictly on two points (`alphaGrad_le_alphaGrad`), and the
excess is strictly Schur-monotone on every number of points (`excessGrad_lt_excessGrad`), so the
Schur–Ostrowski criterion applies to the sum.

## Main statements

* `scalarCurvature_amariChart_lt`: `0 < α ≤ 1`. If the eigenvalues of `ρ` are majorized by those of
  `σ` (`ρ` is more mixed) and are not a permutation of them, then `S_q(σ) < S_q(ρ)`.
* `scalarCurvature_amariChart_lt_of_neg`: `-1 < α < 0`, `S_q(ρ) < S_q(σ)`.
* `scalarCurvature_amariChart_lt_of_two_lt`, `scalarCurvature_amariChart_lt_of_lt_two`: the
  same in Gibilisco–Isola's parameter `p`, with `α = 1 - 2/p`. The endpoint `p = ∞` is `α = 1`.
* `quantumCurv_lt`, `quantumCurv_lt_of_neg`: the same for the closed form on the positive
  orthant.

## References

* [P. Gibilisco, T. Isola, *On the monotonicity of scalar curvature in classical and quantum
  information geometry*][gibilisco2004], J. Math. Phys. 46 (2005), arXiv math-ph/0407007.
-/

open scoped Matrix.Norms.L2Operator ComplexOrder
open Finset
open AlphaCurvature.Curvature

namespace AlphaCurvature.Quantum

/-! ### Permutation invariance -/

section Perm

variable {d : Type*} [Fintype d] [DecidableEq d] {α : ℝ}

theorem sum_sum_ite_comp (f : d → d → ℝ) (σ : Equiv.Perm d) :
    ∑ i, ∑ j, (if i = j then 0 else f (σ i) (σ j)) = ∑ i, ∑ j, if i = j then 0 else f i j := by
  conv_rhs => rw [← Equiv.sum_comp σ]
  refine sum_congr rfl fun i _ ↦ ?_
  conv_rhs => rw [← Equiv.sum_comp σ]
  simp only [σ.injective.eq_iff]

theorem quantumExcess_comp (z : d → ℝ) (σ : Equiv.Perm d) :
    quantumExcess α (z ∘ σ) = quantumExcess α z := by
  have h1 : offSum α (z ∘ σ) = offSum α z :=
    sum_sum_ite_comp (fun a b ↦ curvKernel α (z a) (z b)) σ
  have h2 : offSumSq α (z ∘ σ) = offSumSq α z :=
    sum_sum_ite_comp (fun a b ↦ curvKernel α (z a) (z b) ^ 2) σ
  rw [quantumExcess_eq, quantumExcess_eq, h1, h2, powSum_comp, powSum_comp, powSum_comp]

/-- On the positive orthant, the quantum closed form is the classical α-curvature plus the
excess. -/
theorem quantumCurv_eq_alphaCurv_add [Nonempty d] {l : d → ℝ} (hl : ∀ i, 0 < l i) :
    quantumCurv α l = alphaCurv α l + quantumExcess α l := by
  rw [quantumCurv_eq_add hl, scalarCurvature_alphaChart_eq_alphaCurv hl]

end Perm

/-! ### The conjecture for the closed form -/

section ClosedForm

variable {n : ℕ} {α : ℝ} {x y : Fin n → ℝ}

theorem hasDerivAt_curv_add [NeZero n] (hα₁ : -1 < α) (hα : α ≤ 1) :
    ∀ z ∈ {z : Fin n → ℝ | ∀ i, 0 < z i}, ∀ v : Fin n → ℝ,
      HasDerivAt (fun t : ℝ ↦ alphaCurv α (z + t • v) + quantumExcess α (z + t • v))
        (∑ a, (alphaGrad α z a + excessGrad α z a) * v a) 0 := fun z hz v ↦ by
  convert (hasDerivAt_alphaCurv hz v).add (hasDerivAt_quantumExcess hα₁ hα hz v) using 1
  simp only [add_mul, sum_add_distrib]

theorem curv_add_comp :
    ∀ z ∈ {z : Fin n → ℝ | ∀ i, 0 < z i}, ∀ σ : Equiv.Perm (Fin n),
      z ∘ σ ∈ {z : Fin n → ℝ | ∀ i, 0 < z i} ∧
        alphaCurv α (z ∘ σ) + quantumExcess α (z ∘ σ) = alphaCurv α z + quantumExcess α z :=
  fun z hz σ ↦ ⟨fun i ↦ hz (σ i), by rw [alphaCurv_comp, quantumExcess_comp]⟩

theorem ne_zero_of_ne_comp (hne : ∀ σ : Equiv.Perm (Fin n), x ∘ σ ≠ y) : NeZero n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd (Subsingleton.elim _ _) (hne 1)
  · exact ⟨hn.ne'⟩

/-- **The quantum conjecture for the closed form, `0 < α ≤ 1`**: if `x` is majorized by `y` and is
not a permutation of it, then `S_q(y) < S_q(x)`. -/
theorem quantumCurv_lt (hα : 0 < α) (hα₁ : α ≤ 1) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hxy : IsMajorizedBy x y) (hne : ∀ σ : Equiv.Perm (Fin n), x ∘ σ ≠ y) :
    quantumCurv α y < quantumCurv α x := by
  have := ne_zero_of_ne_comp hne
  rw [quantumCurv_eq_alphaCurv_add hx, quantumCurv_eq_alphaCurv_add hy]
  refine lt_of_isMajorizedBy (F := fun z ↦ alphaCurv α z + quantumExcess α z)
    (grad := fun z a ↦ alphaGrad α z a + excessGrad α z a) convex_setOf_pos curv_add_comp
    (hasDerivAt_curv_add (by linarith) hα₁) ?_ ?_ hx hy hxy (ne_sortInc hne)
  · intro z hz hmono a b hab
    have h1 := alphaGrad_le_alphaGrad hα hα₁ hz (hmono hab)
    rcases (hmono hab).eq_or_lt with h | h
    · exact add_le_add h1 (excessGrad_eq_excessGrad h.symm).le
    · exact add_le_add h1 (excessGrad_lt_excessGrad hα hα₁ hz h).le
  · intro z hz _ a b hab
    exact add_lt_add_of_le_of_lt (alphaGrad_le_alphaGrad hα hα₁ hz hab.le)
      (excessGrad_lt_excessGrad hα hα₁ hz hab)

/-- **The quantum conjecture for the closed form, `-1 < α < 0`**: if `x` is majorized by `y` and
is not a permutation of it, then `S_q(x) < S_q(y)`. -/
theorem quantumCurv_lt_of_neg (hα₁ : -1 < α) (hα : α < 0) (hx : ∀ i, 0 < x i)
    (hy : ∀ i, 0 < y i) (hxy : IsMajorizedBy x y) (hne : ∀ σ : Equiv.Perm (Fin n), x ∘ σ ≠ y) :
    quantumCurv α x < quantumCurv α y := by
  have := ne_zero_of_ne_comp hne
  rw [quantumCurv_eq_alphaCurv_add hx, quantumCurv_eq_alphaCurv_add hy]
  have h := lt_of_isMajorizedBy (F := fun z ↦ -(alphaCurv α z + quantumExcess α z))
    (grad := fun z a ↦ -(alphaGrad α z a + excessGrad α z a)) convex_setOf_pos
    (fun z hz σ ↦ ⟨(curv_add_comp (α := α) z hz σ).1, by rw [(curv_add_comp (α := α) z hz σ).2]⟩)
    (fun z hz v ↦ by
      convert (hasDerivAt_curv_add hα₁ (by linarith) z hz v).fun_neg using 1
      simp only [neg_mul, sum_neg_distrib])
    (fun z hz hmono a b hab ↦ by
      have h1 := alphaGrad_le_alphaGrad_of_neg hα₁ hα hz (hmono hab)
      rcases (hmono hab).eq_or_lt with h | h
      · exact neg_le_neg (add_le_add h1 (excessGrad_eq_excessGrad h).le)
      · exact neg_le_neg (add_le_add h1 (excessGrad_lt_excessGrad_of_neg hα₁ hα hz h).le))
    (fun z hz _ a b hab ↦ neg_lt_neg (add_lt_add_of_le_of_lt
      (alphaGrad_le_alphaGrad_of_neg hα₁ hα hz hab.le)
      (excessGrad_lt_excessGrad_of_neg hα₁ hα hz hab)))
    hx hy hxy (ne_sortInc hne)
  linarith

end ClosedForm

/-! ### The conjecture -/

section Conjecture

variable {n : ℕ} {α : ℝ} {ρ σ : Matrix (Fin n) (Fin n) ℂ}

/-- **Gibilisco–Isola, Conjecture 4.2, `p ∈ (2, ∞]`** (`0 < α ≤ 1`): the scalar curvature of the
quantum α-geometry is strictly Schur-increasing in the eigenvalues. If the eigenvalues of `ρ` are
majorized by those of `σ` (`ρ` is more mixed) and are not a permutation of them, then
`S_q(σ) < S_q(ρ)`. -/
theorem scalarCurvature_amariChart_lt (hα : 0 < α) (hα₁ : α ≤ 1) (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hmaj : IsMajorizedBy hρ.1.eigenvalues hσ.1.eigenvalues)
    (hne : ∀ π : Equiv.Perm (Fin n), hρ.1.eigenvalues ∘ π ≠ hσ.1.eigenvalues) :
    scalarCurvature (pullback (amariChart α (tracelessHermitian (Fin n)) σ) fun _ ↦ hsForm) 0 <
      scalarCurvature (pullback (amariChart α (tracelessHermitian (Fin n)) ρ)
        fun _ ↦ hsForm) 0 := by
  have := ne_zero_of_ne_comp hne
  rw [scalarCurvature_amariChart hρ, scalarCurvature_amariChart hσ]
  exact quantumCurv_lt hα hα₁ hρ.eigenvalues_pos hσ.eigenvalues_pos hmaj hne

/-- **Gibilisco–Isola, Conjecture 4.2, `p ∈ (1, 2)`** (`-1 < α < 0`): the scalar curvature of the
quantum α-geometry is strictly Schur-decreasing in the eigenvalues. -/
theorem scalarCurvature_amariChart_lt_of_neg (hα₁ : -1 < α) (hα : α < 0) (hρ : ρ.PosDef)
    (hσ : σ.PosDef) (hmaj : IsMajorizedBy hρ.1.eigenvalues hσ.1.eigenvalues)
    (hne : ∀ π : Equiv.Perm (Fin n), hρ.1.eigenvalues ∘ π ≠ hσ.1.eigenvalues) :
    scalarCurvature (pullback (amariChart α (tracelessHermitian (Fin n)) ρ) fun _ ↦ hsForm) 0 <
      scalarCurvature (pullback (amariChart α (tracelessHermitian (Fin n)) σ)
        fun _ ↦ hsForm) 0 := by
  have := ne_zero_of_ne_comp hne
  rw [scalarCurvature_amariChart hρ, scalarCurvature_amariChart hσ]
  exact quantumCurv_lt_of_neg hα₁ hα hρ.eigenvalues_pos hσ.eigenvalues_pos hmaj hne

/-- **Gibilisco–Isola, Conjecture 4.2, `p ∈ (2, ∞)`**, in their parameter: with `α = 1 - 2/p`,
if `ρ` is more mixed than `σ` and their spectra are not permutations of each other, then
`Scal_p(σ) < Scal_p(ρ)`. The endpoint `p = ∞` is the case `α = 1` of
`scalarCurvature_amariChart_lt`. -/
theorem scalarCurvature_amariChart_lt_of_two_lt {p : ℝ} (hp : 2 < p) (hρ : ρ.PosDef)
    (hσ : σ.PosDef) (hmaj : IsMajorizedBy hρ.1.eigenvalues hσ.1.eigenvalues)
    (hne : ∀ π : Equiv.Perm (Fin n), hρ.1.eigenvalues ∘ π ≠ hσ.1.eigenvalues) :
    scalarCurvature (pullback (amariChart (1 - 2 / p) (tracelessHermitian (Fin n)) σ)
        fun _ ↦ hsForm) 0 <
      scalarCurvature (pullback (amariChart (1 - 2 / p) (tracelessHermitian (Fin n)) ρ)
        fun _ ↦ hsForm) 0 := by
  have hp0 : 0 < p := by linarith
  refine scalarCurvature_amariChart_lt ?_ ?_ hρ hσ hmaj hne
  · have : 2 / p < 1 := by rw [div_lt_one hp0]; exact hp
    linarith
  · have : 0 < 2 / p := by positivity
    linarith

/-- **Gibilisco–Isola, Conjecture 4.2, `p ∈ (1, 2)`**, in their parameter: with `α = 1 - 2/p`,
if `ρ` is more mixed than `σ` and their spectra are not permutations of each other, then
`Scal_p(ρ) < Scal_p(σ)`. -/
theorem scalarCurvature_amariChart_lt_of_lt_two {p : ℝ} (hp₁ : 1 < p) (hp : p < 2)
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hmaj : IsMajorizedBy hρ.1.eigenvalues hσ.1.eigenvalues)
    (hne : ∀ π : Equiv.Perm (Fin n), hρ.1.eigenvalues ∘ π ≠ hσ.1.eigenvalues) :
    scalarCurvature (pullback (amariChart (1 - 2 / p) (tracelessHermitian (Fin n)) ρ)
        fun _ ↦ hsForm) 0 <
      scalarCurvature (pullback (amariChart (1 - 2 / p) (tracelessHermitian (Fin n)) σ)
        fun _ ↦ hsForm) 0 := by
  have hp0 : 0 < p := by linarith
  refine scalarCurvature_amariChart_lt_of_neg ?_ ?_ hρ hσ hmaj hne
  · have : 2 / p < 2 := by rw [div_lt_iff₀ hp0]; linarith
    linarith
  · have : 1 < 2 / p := by rw [lt_div_iff₀ hp0]; linarith
    linarith

end Conjecture

end AlphaCurvature.Quantum
