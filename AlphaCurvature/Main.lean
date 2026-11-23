/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import AlphaCurvature.ForMathlib.Majorization
import AlphaCurvature.PerPoint

/-!
# The α-geometry curvature conjecture

**The α-geometry curvature conjecture of Gibilisco and Isola** (Conjecture 4.1 of
Gibilisco–Isola 2004; Conjecture 1 of Gibilisco 2020), for every number of points and every
`p ∈ [1, ∞]`, i.e. `α ∈ [-1, 1]` with `p = 2/(1 - α)`. It is strict on at least three points for
`p ∈ (1, 2)` and `p ∈ (2, ∞]`.

* `p ≥ 2` (`α ≥ 0`): the scalar curvature `S` of the α-geometry of the simplex does not decrease
  under mixing, `x ≺ y ⟹ S(y) ≤ S(x)` (Schur-increasing in Gibilisco–Isola's terms).
* `p ≤ 2` (`α ≤ 0`): it does not increase, `x ≺ y ⟹ S(x) ≤ S(y)` (Schur-decreasing).

**What the statement depends on.** `IsMajorizedBy x y` (`ForMathlib/Majorization.lean`):
`x` is more mixed than `y`, Gibilisco–Isola's `x ≻ y`. `alphaChart α (simplexTangent (Fin n)) x`
(`Metric.lean`): the metric `∑ᵢ xᵢ^(-1-α) dxᵢ²`, which is the Amari pullback
(`pullback_amariEmbed`), in the affine chart `z ↦ x + z` of the hyperplane through `x`.
`scalarCurvature G 0` (`Curvature/Basic.lean`): the scalar curvature at the centre of the chart,
with the convention that the round unit sphere has scalar curvature `2`. At `α = 0` it gives
Gibilisco–Isola's `(n - 1)(n - 2)/4` (`scalarCurvature_alphaChart_zero`).

The proof is the Schur–Ostrowski criterion (`le_of_isMajorizedBy`, `lt_of_isMajorizedBy`) for
`alphaCurv`, the closed form of `S` on the positive orthant (`Gradient.lean`). The gradient
difference `∂ᵢS - ∂ⱼS` is a positive multiple of the gradient numerator `Z`
(`alphaGrad_sub_alphaGrad`), which for `xᵢ > xⱼ` has the sign of `-α`, strictly when a third
point is present (`PerPoint.lean`). So the gradient is antitone in the entry for `α > 0` and
monotone for `α < 0`. On two points the curve is flat, so strictness needs `3 ≤ n`, which is
Gibilisco–Isola's `n > 2`. At `α = 0` (the Fisher metric) `S` depends only on the total, and at
`α = -1` it vanishes.

The statements are for positive vectors of any total, which majorization preserves; density
vectors are the case of total `1`. `scalarCurvature_alphaChart_lt_of_two_lt` and
`scalarCurvature_alphaChart_lt_of_lt_two` restate the conjecture in Gibilisco–Isola's
parametrization `α = 1 - 2/p`. The endpoint `p = +∞`, which Gibilisco–Isola include, is `α = 1`
(the logarithmic embedding).

## Main statements

* `AlphaCurvature.scalarCurvature_alphaChart_le`: `0 ≤ α ≤ 1` (`p ≥ 2`), `S(y) ≤ S(x)`.
* `AlphaCurvature.scalarCurvature_alphaChart_lt`: the strict form, for `0 < α ≤ 1`, at least
  three points and `x` not a permutation of `y`.
* `AlphaCurvature.scalarCurvature_alphaChart_le_of_nonpos`: `-1 ≤ α ≤ 0` (`1 ≤ p ≤ 2`),
  `S(x) ≤ S(y)`.
* `AlphaCurvature.scalarCurvature_alphaChart_lt_of_neg`: the strict form for `-1 < α < 0`.
* `AlphaCurvature.scalarCurvature_alphaChart_lt_of_two_lt`,
  `scalarCurvature_alphaChart_lt_of_lt_two`: Gibilisco–Isola's Conjecture 4.1 in terms of `p`.

## References

* [P. Gibilisco, T. Isola, *On the monotonicity of scalar curvature in classical and quantum
  information geometry*][gibilisco2004], J. Math. Phys. 46 (2005), arXiv math-ph/0407007.
* [P. Gibilisco, *Lp unit spheres and the α-geometries: questions and perspectives*][gibilisco2020],
  Entropy 22 (2020) 1409.
-/

open Finset
open AlphaCurvature.Curvature

namespace AlphaCurvature

variable {α : ℝ}

/-! ### The gradient at two entries -/

section Gradient

variable {d : Type*} [Fintype d] {x : d → ℝ} {i j : d}

/-- The gradient depends on the index only through the entry. -/
theorem alphaGrad_eq_alphaGrad (h : x i = x j) : alphaGrad α x i = alphaGrad α x j := by
  simp only [alphaGrad, alphaBGrad, h]

/-- On at least three points, there is a point other than `i` and `j`. -/
theorem others_nonempty [DecidableEq d] (hd : 3 ≤ Fintype.card d) (hij : i ≠ j) :
    (others i j).Nonempty := by
  rw [← card_pos, others, card_erase_of_mem (mem_erase.2 ⟨hij.symm, mem_univ _⟩),
    card_erase_of_mem (mem_univ _), card_univ]
  omega

/-- The prefactor `(1 + α)²/4 / P(1+α)³` of the gradient difference is positive. -/
theorem alphaGrad_prefactor_pos (hα₁ : -1 < α) (hx : ∀ k, 0 < x k) (i : d) :
    0 < (1 + α) ^ 2 / 4 / powSum x (1 + α) ^ 3 := by
  have : Nonempty d := ⟨i⟩
  have h1 : 0 < 1 + α := by linarith
  have := powSum_pos hx (1 + α)
  positivity

/-- For `0 < α ≤ 1`, the gradient is strictly smaller at a strictly larger entry, when there is
a third point. -/
theorem alphaGrad_lt_alphaGrad (hα : 0 < α) (hα₁ : α ≤ 1) (hx : ∀ k, 0 < x k)
    (h : x j < x i) (hd : 3 ≤ Fintype.card d) : alphaGrad α x i < alphaGrad α x j := by
  classical
  have hij : i ≠ j := fun e ↦ by rw [e] at h; exact lt_irrefl _ h
  have hs := alphaNum_neg hα hα₁ (hx j) h hx (others_nonempty hd hij)
  have hc := alphaGrad_prefactor_pos (α := α) (by linarith) hx i
  have e := alphaGrad_sub_alphaGrad (α := α) hx hij
  rw [mul_div_right_comm] at e
  have := mul_neg_of_pos_of_neg hc hs
  linarith

/-- For `0 < α ≤ 1`, the gradient is antitone in the entry. -/
theorem alphaGrad_le_alphaGrad (hα : 0 < α) (hα₁ : α ≤ 1) (hx : ∀ k, 0 < x k)
    (h : x j ≤ x i) : alphaGrad α x i ≤ alphaGrad α x j := by
  classical
  rcases h.eq_or_lt with h | h
  · exact (alphaGrad_eq_alphaGrad h.symm).le
  have hij : i ≠ j := fun e ↦ by rw [e] at h; exact lt_irrefl _ h
  have hs := alphaNum_nonpos hα hα₁ (hx j) h hx (others i j)
  have hc := alphaGrad_prefactor_pos (α := α) (by linarith) hx i
  have e := alphaGrad_sub_alphaGrad (α := α) hx hij
  rw [mul_div_right_comm] at e
  have := mul_nonpos_of_nonneg_of_nonpos hc.le hs
  linarith

/-- For `-1 < α < 0`, the gradient is strictly larger at a strictly larger entry, when there is
a third point. -/
theorem alphaGrad_lt_alphaGrad_of_neg (hα₁ : -1 < α) (hα : α < 0) (hx : ∀ k, 0 < x k)
    (h : x j < x i) (hd : 3 ≤ Fintype.card d) : alphaGrad α x j < alphaGrad α x i := by
  classical
  have hij : i ≠ j := fun e ↦ by rw [e] at h; exact lt_irrefl _ h
  have hs := alphaNum_pos hα₁ hα (hx j) h hx (others_nonempty hd hij)
  have hc := alphaGrad_prefactor_pos hα₁ hx i
  have e := alphaGrad_sub_alphaGrad (α := α) hx hij
  rw [mul_div_right_comm] at e
  have := mul_pos hc hs
  linarith

/-- For `-1 < α < 0`, the gradient is monotone in the entry. -/
theorem alphaGrad_le_alphaGrad_of_neg (hα₁ : -1 < α) (hα : α < 0) (hx : ∀ k, 0 < x k)
    (h : x j ≤ x i) : alphaGrad α x j ≤ alphaGrad α x i := by
  classical
  rcases h.eq_or_lt with h | h
  · exact (alphaGrad_eq_alphaGrad h).le
  have hij : i ≠ j := fun e ↦ by rw [e] at h; exact lt_irrefl _ h
  have hs := alphaNum_nonneg hα₁ hα (hx j) h hx (others i j)
  have hc := alphaGrad_prefactor_pos hα₁ hx i
  have e := alphaGrad_sub_alphaGrad (α := α) hx hij
  rw [mul_div_right_comm] at e
  have := mul_nonneg hc.le hs
  linarith

end Gradient

/-! ### The conjecture -/

section Conjecture

variable {n : ℕ} {x y : Fin n → ℝ}

/-- Power sums are invariant under permutations. -/
theorem powSum_comp {d : Type*} [Fintype d] (z : d → ℝ) (σ : Equiv.Perm d) (s : ℝ) :
    powSum (z ∘ σ) s = powSum z s :=
  Equiv.sum_comp σ (fun i ↦ z i ^ s)

/-- The α-curvature is invariant under permutations. -/
theorem alphaCurv_comp {d : Type*} [Fintype d] (z : d → ℝ) (σ : Equiv.Perm d) :
    alphaCurv α (z ∘ σ) = alphaCurv α z := by
  simp only [alphaCurv, alphaB, powSum_comp]

/-- The positive orthant is convex. -/
theorem convex_setOf_pos {d : Type*} : Convex ℝ {z : d → ℝ | ∀ i, 0 < z i} := by
  intro z hz w hw a b ha hb hab
  change ∀ i, 0 < (a • z + b • w) i
  intro i
  have := hz i
  have := hw i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases ha.eq_or_lt with rfl | ha
  · rw [zero_add] at hab
    subst hab
    simpa using hw i
  · positivity

/-- Vectors that are not permutations of each other have different rearrangements. -/
theorem ne_sortInc (hne : ∀ σ : Equiv.Perm (Fin n), x ∘ σ ≠ y) :
    Majorization.sortInc x ≠ Majorization.sortInc y := fun h ↦
  let ⟨σ, hσ⟩ := Majorization.exists_comp_eq_of_sortInc_eq h
  hne σ hσ

/-- The derivative hypothesis of the Schur–Ostrowski criterion, on the positive orthant. -/
theorem hasDerivAt_alphaCurv_of_mem [NeZero n] :
    ∀ z ∈ {z : Fin n → ℝ | ∀ i, 0 < z i}, ∀ v : Fin n → ℝ,
      HasDerivAt (fun t : ℝ ↦ alphaCurv α (z + t • v)) (∑ a, alphaGrad α z a * v a) 0 :=
  fun _ hz v ↦ hasDerivAt_alphaCurv hz v

/-- The permutation hypothesis of the Schur–Ostrowski criterion, on the positive orthant. -/
theorem alphaCurv_comp_of_mem :
    ∀ z ∈ {z : Fin n → ℝ | ∀ i, 0 < z i}, ∀ σ : Equiv.Perm (Fin n),
      z ∘ σ ∈ {z : Fin n → ℝ | ∀ i, 0 < z i} ∧ alphaCurv α (z ∘ σ) = alphaCurv α z :=
  fun z hz σ ↦ ⟨fun i ↦ hz (σ i), alphaCurv_comp z σ⟩

/-- **The α-geometry curvature conjecture for `p ≥ 2`** (Gibilisco–Isola, Conjecture 4.1;
`0 ≤ α ≤ 1`, with `α = 1` the case `p = ∞`): the scalar curvature does not decrease under mixing.
If `x` is majorized by `y` (`x` is more mixed), then `S(y) ≤ S(x)`. -/
theorem scalarCurvature_alphaChart_le (hα : 0 ≤ α) (hα₁ : α ≤ 1) (hx : ∀ i, 0 < x i)
    (hy : ∀ i, 0 < y i) (hxy : IsMajorizedBy x y) :
    scalarCurvature (alphaChart α (simplexTangent (Fin n)) y) 0 ≤
      scalarCurvature (alphaChart α (simplexTangent (Fin n)) x) 0 := by
  rcases hα.eq_or_lt with rfl | hα
  · rw [scalarCurvature_alphaChart hx, scalarCurvature_alphaChart hy]
    simp only [mul_zero, add_zero, Real.rpow_zero, Real.rpow_one, hxy.1, le_refl]
  rw [scalarCurvature_alphaChart_eq_alphaCurv hx, scalarCurvature_alphaChart_eq_alphaCurv hy]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Subsingleton.elim x y]
  have : NeZero n := ⟨hn.ne'⟩
  exact le_of_isMajorizedBy convex_setOf_pos alphaCurv_comp_of_mem hasDerivAt_alphaCurv_of_mem
    (fun z hz hmono i j hij ↦ alphaGrad_le_alphaGrad hα hα₁ hz (hmono hij)) hx hy hxy

/-- **The α-geometry curvature conjecture for `p > 2`, strict** (`0 < α ≤ 1`): on at least three
points, if `x` is majorized by `y` and is not a permutation of it, then `S(y) < S(x)`. -/
theorem scalarCurvature_alphaChart_lt (hα : 0 < α) (hα₁ : α ≤ 1) (hn : 3 ≤ n)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hxy : IsMajorizedBy x y)
    (hne : ∀ σ : Equiv.Perm (Fin n), x ∘ σ ≠ y) :
    scalarCurvature (alphaChart α (simplexTangent (Fin n)) y) 0 <
      scalarCurvature (alphaChart α (simplexTangent (Fin n)) x) 0 := by
  rw [scalarCurvature_alphaChart_eq_alphaCurv hx, scalarCurvature_alphaChart_eq_alphaCurv hy]
  have : NeZero n := ⟨by omega⟩
  have hd : 3 ≤ Fintype.card (Fin n) := by simpa using hn
  exact lt_of_isMajorizedBy convex_setOf_pos alphaCurv_comp_of_mem hasDerivAt_alphaCurv_of_mem
    (fun z hz hmono i j hij ↦ alphaGrad_le_alphaGrad hα hα₁ hz (hmono hij))
    (fun z hz _ i j hij ↦ alphaGrad_lt_alphaGrad hα hα₁ hz hij hd) hx hy hxy (ne_sortInc hne)

/-- **The α-geometry curvature conjecture for `1 ≤ p ≤ 2`** (`-1 ≤ α ≤ 0`): the scalar curvature
does not increase under mixing. If `x` is majorized by `y`, then `S(x) ≤ S(y)`. -/
theorem scalarCurvature_alphaChart_le_of_nonpos (hα₁ : -1 ≤ α) (hα : α ≤ 0) (hx : ∀ i, 0 < x i)
    (hy : ∀ i, 0 < y i) (hxy : IsMajorizedBy x y) :
    scalarCurvature (alphaChart α (simplexTangent (Fin n)) x) 0 ≤
      scalarCurvature (alphaChart α (simplexTangent (Fin n)) y) 0 := by
  rcases hα.eq_or_lt with rfl | hα
  · rw [scalarCurvature_alphaChart hx, scalarCurvature_alphaChart hy]
    simp only [mul_zero, add_zero, Real.rpow_zero, Real.rpow_one, hxy.1, le_refl]
  rcases hα₁.eq_or_lt with rfl | hα₁
  · rw [scalarCurvature_alphaChart hx, scalarCurvature_alphaChart hy]
    norm_num
  rw [scalarCurvature_alphaChart_eq_alphaCurv hx, scalarCurvature_alphaChart_eq_alphaCurv hy]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Subsingleton.elim x y]
  have : NeZero n := ⟨hn.ne'⟩
  have h := le_of_isMajorizedBy (F := fun z ↦ -alphaCurv α z)
    (grad := fun z a ↦ -alphaGrad α z a) convex_setOf_pos
    (fun z hz σ ↦ ⟨fun i ↦ hz (σ i), by simp only [alphaCurv_comp]⟩)
    (fun z hz v ↦ by
      convert (hasDerivAt_alphaCurv (α := α) hz v).fun_neg using 1
      simp only [neg_mul, sum_neg_distrib])
    (fun z hz hmono i j hij ↦ neg_le_neg (alphaGrad_le_alphaGrad_of_neg hα₁ hα hz (hmono hij)))
    hx hy hxy
  linarith

/-- **The α-geometry curvature conjecture for `1 < p < 2`, strict** (`-1 < α < 0`): on at least
three points, if `x` is majorized by `y` and is not a permutation of it, then `S(x) < S(y)`. -/
theorem scalarCurvature_alphaChart_lt_of_neg (hα₁ : -1 < α) (hα : α < 0) (hn : 3 ≤ n)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hxy : IsMajorizedBy x y)
    (hne : ∀ σ : Equiv.Perm (Fin n), x ∘ σ ≠ y) :
    scalarCurvature (alphaChart α (simplexTangent (Fin n)) x) 0 <
      scalarCurvature (alphaChart α (simplexTangent (Fin n)) y) 0 := by
  rw [scalarCurvature_alphaChart_eq_alphaCurv hx, scalarCurvature_alphaChart_eq_alphaCurv hy]
  have : NeZero n := ⟨by omega⟩
  have hd : 3 ≤ Fintype.card (Fin n) := by simpa using hn
  have h := lt_of_isMajorizedBy (F := fun z ↦ -alphaCurv α z)
    (grad := fun z a ↦ -alphaGrad α z a) convex_setOf_pos
    (fun z hz σ ↦ ⟨fun i ↦ hz (σ i), by simp only [alphaCurv_comp]⟩)
    (fun z hz v ↦ by
      convert (hasDerivAt_alphaCurv (α := α) hz v).fun_neg using 1
      simp only [neg_mul, sum_neg_distrib])
    (fun z hz hmono i j hij ↦ neg_le_neg (alphaGrad_le_alphaGrad_of_neg hα₁ hα hz (hmono hij)))
    (fun z hz _ i j hij ↦ neg_lt_neg (alphaGrad_lt_alphaGrad_of_neg hα₁ hα hz hij hd))
    hx hy hxy (ne_sortInc hne)
  linarith

/-- **Gibilisco–Isola, Conjecture 4.1, `p ∈ (2, ∞)`**: on at least three points, the scalar
curvature of the α-geometry with `p = 2/(1 - α)`, i.e. `α = 1 - 2/p`, is strictly
Schur-increasing. If `x` is more mixed than `y` (`IsMajorizedBy x y`, G–I's `x ≻ y`) and is not a
permutation of it, then `Scal_p(y) < Scal_p(x)`. The endpoint `p = +∞` is the case `α = 1` of
`scalarCurvature_alphaChart_lt`. -/
theorem scalarCurvature_alphaChart_lt_of_two_lt {p : ℝ} (hp : 2 < p) (hn : 3 ≤ n)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hxy : IsMajorizedBy x y)
    (hne : ∀ σ : Equiv.Perm (Fin n), x ∘ σ ≠ y) :
    scalarCurvature (alphaChart (1 - 2 / p) (simplexTangent (Fin n)) y) 0 <
      scalarCurvature (alphaChart (1 - 2 / p) (simplexTangent (Fin n)) x) 0 := by
  have hp0 : 0 < p := by linarith
  refine scalarCurvature_alphaChart_lt ?_ ?_ hn hx hy hxy hne
  · have : 2 / p < 1 := by rw [div_lt_one hp0]; exact hp
    linarith
  · have : 0 < 2 / p := by positivity
    linarith

/-- **Gibilisco–Isola, Conjecture 4.1, `p ∈ (1, 2)`**: on at least three points, the scalar
curvature of the α-geometry with `α = 1 - 2/p` is strictly Schur-decreasing. If `x` is more mixed
than `y` and is not a permutation of it, then `Scal_p(x) < Scal_p(y)`. -/
theorem scalarCurvature_alphaChart_lt_of_lt_two {p : ℝ} (hp₁ : 1 < p) (hp : p < 2) (hn : 3 ≤ n)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hxy : IsMajorizedBy x y)
    (hne : ∀ σ : Equiv.Perm (Fin n), x ∘ σ ≠ y) :
    scalarCurvature (alphaChart (1 - 2 / p) (simplexTangent (Fin n)) x) 0 <
      scalarCurvature (alphaChart (1 - 2 / p) (simplexTangent (Fin n)) y) 0 := by
  have hp0 : 0 < p := by linarith
  refine scalarCurvature_alphaChart_lt_of_neg ?_ ?_ hn hx hy hxy hne
  · have : 2 / p < 2 := by rw [div_lt_iff₀ hp0]; linarith
    linarith
  · have : 1 < 2 / p := by rw [lt_div_iff₀ hp0]; linarith
    linarith

end Conjecture

end AlphaCurvature
