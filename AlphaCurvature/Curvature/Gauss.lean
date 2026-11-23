/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Algebra.BigOperators.Field
import AlphaCurvature.Curvature.Pullback
import AlphaCurvature.Curvature.Hessian

/-!
# The Gauss equation

For a map `φ : E → F` of real normed spaces and a constant symmetric bilinear form `B` on `F`,
the pullback `G = pullback φ (fun _ ↦ B)` is the metric induced on `E` by `φ`, for instance that
of an immersed submanifold of a Euclidean space. This file computes its curvature from the first
and second derivatives of `φ` alone. Write `A = Dφ x`, `II = D²φ x` and `Γ = christoffel G x`.

* `G(Γ(v, w), u) = B(II(v, w), A u)` (`pullback_const_christoffel`): the Christoffel symbols are
  the tangential part of `II`.
* **The Gauss equation** (`pullback_const_riemann`):
  `G(R(X, Y) Z, W) = B(II(Y, Z), II(X, W)) - B(II(X, Z), II(Y, W)) - G(Γ(X, W), Γ(Y, Z)) +
  G(Γ(Y, W), Γ(X, Z))`. The third derivative of `φ` enters the derivative of `Γ` but cancels,
  because it is symmetric. No orthogonal projection is formed: the `Γ` terms remove the
  tangential part of `II`.
* The scalar curvature in a `G x`-orthonormal basis (`scalarCurvature_pullback_const`).
* **Codimension one** (`scalarCurvature_pullback_const_of_normal`): if, inside a subspace `H` that
  contains the values of `A` and `II`, the vectors `B`-orthogonal to the range of `A` are the
  multiples of one `N` with `B(N, A u) = 0` and `B(N, N) ≠ 0`, then with
  `h(v, w) = B(II(v, w), N)`, `S = ((∑ᵢ h(bᵢ, bᵢ))² - ∑ᵢⱼ h(bᵢ, bⱼ)²) / B(N, N)`.
  For a hypersurface of a Euclidean space, `h / |N|` is the second fundamental form, and this is
  `S = (tr L)² - tr L²` for the shape operator `L`.

## References

* [O'Neill, *Semi-Riemannian Geometry, with Applications to Relativity*][oneill1983]
  (the Gauss equation, Chapter 4).
-/

open Filter ContinuousLinearMap
open scoped Topology

namespace AlphaCurvature.Curvature

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {φ : E → F} {B : F →L[ℝ] F →L[ℝ] ℝ} {x : E}

/-- The Christoffel form of the metric induced by `φ` from a constant symmetric form `B`:
`B(D²φ x v w, Dφ x u)`. -/
theorem christoffelForm_pullback_const (hφ : ContDiffAt ℝ 2 φ x) (hB : ∀ v w, B v w = B w v)
    (v w u : E) :
    christoffelForm (pullback φ fun _ ↦ B) x v w u =
      B (fderiv ℝ (fderiv ℝ φ) x v w) (fderiv ℝ φ x u) := by
  rw [christoffelForm_pullback hφ (differentiableAt_const _) hB]
  simp

/-- The induced metric is symmetric. -/
theorem pullback_const_comm (hB : ∀ v w, B v w = B w v) (y v w : E) :
    pullback φ (fun _ ↦ B) y v w = pullback φ (fun _ ↦ B) y w v := by
  simp [hB]

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **The Christoffel symbols are the tangential part of `D²φ`**: near a point where `φ` is `C³`
and the induced metric `G` is invertible, `G(Γ(v, w), u) = B(D²φ v w, Dφ u)`. -/
theorem eventually_pullback_const_christoffel (hφ : ContDiffAt ℝ 3 φ x)
    (hB : ∀ v w, B v w = B w v) (hx : (pullback φ (fun _ ↦ B) x).IsInvertible) :
    ∀ᶠ y in 𝓝 x, ∀ v w u, pullback φ (fun _ ↦ B) y (christoffel (pullback φ fun _ ↦ B) y v w) u =
      B (fderiv ℝ (fderiv ℝ φ) y v w) (fderiv ℝ φ y u) := by
  have hG : ContDiffAt ℝ 2 (pullback φ fun _ ↦ B) x :=
    contDiffAt_pullback contDiffAt_const (hφ.of_le (by norm_num))
  have hφ2 : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 φ y :=
    (hφ.eventually (by simp)).mono fun y hy ↦ hy.of_le (by norm_num)
  filter_upwards [hφ2, hG.continuousAt.eventually hx.eventually_nhds] with y h₁ h₂ v w u
  rw [christoffel_spec h₂, christoffelForm_pullback_const h₁ hB]

/-- The value of `pullback_const_christoffel` at the point itself. -/
theorem pullback_const_christoffel (hφ : ContDiffAt ℝ 3 φ x) (hB : ∀ v w, B v w = B w v)
    (hx : (pullback φ (fun _ ↦ B) x).IsInvertible) (v w u : E) :
    pullback φ (fun _ ↦ B) x (christoffel (pullback φ fun _ ↦ B) x v w) u =
      B (fderiv ℝ (fderiv ℝ φ) x v w) (fderiv ℝ φ x u) :=
  (eventually_pullback_const_christoffel hφ hB hx).self_of_nhds v w u

/-- **The Gauss equation**, for the metric `G` induced by `φ` from a constant symmetric form `B`,
where `φ` is `C³` and `G` is invertible: with `II = D²φ x` and `Γ = christoffel G x`,
`G(R(X, Y) Z, W) = B(II Y Z, II X W) - B(II X Z, II Y W) - G(Γ X W, Γ Y Z) + G(Γ Y W, Γ X Z)`. -/
theorem pullback_const_riemann (hφ : ContDiffAt ℝ 3 φ x) (hB : ∀ v w, B v w = B w v)
    (hx : (pullback φ (fun _ ↦ B) x).IsInvertible) (X Y Z W : E) :
    pullback φ (fun _ ↦ B) x (riemann (pullback φ fun _ ↦ B) x X Y Z) W =
      B (fderiv ℝ (fderiv ℝ φ) x Y Z) (fderiv ℝ (fderiv ℝ φ) x X W) -
        B (fderiv ℝ (fderiv ℝ φ) x X Z) (fderiv ℝ (fderiv ℝ φ) x Y W) -
        pullback φ (fun _ ↦ B) x (christoffel (pullback φ fun _ ↦ B) x X W)
          (christoffel (pullback φ fun _ ↦ B) x Y Z) +
        pullback φ (fun _ ↦ B) x (christoffel (pullback φ fun _ ↦ B) x Y W)
          (christoffel (pullback φ fun _ ↦ B) x X Z) := by
  set G := pullback φ fun _ ↦ B with hGdef
  have hG2 : ContDiffAt ℝ 2 G x := contDiffAt_pullback contDiffAt_const (hφ.of_le (by norm_num))
  have hGd : DifferentiableAt ℝ G x := hG2.differentiableAt (by simp)
  have hφd : DifferentiableAt ℝ φ x := hφ.differentiableAt (by simp)
  have hDφ2 : ContDiffAt ℝ 2 (fderiv ℝ φ) x := hφ.fderiv_right (by norm_num)
  have hD₁ : DifferentiableAt ℝ (fderiv ℝ φ) x := hDφ2.differentiableAt (by simp)
  have hD₂ : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ φ)) x :=
    (hDφ2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hΓ : DifferentiableAt ℝ (christoffel G) x :=
    (contDiffAt_christoffel (k := 1) (by simpa [one_add_one_eq_two] using hG2) hx).differentiableAt
      one_ne_zero
  have hII := (hφ.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).isSymmSndFDerivAt (by simp)
  have hIII := hDφ2.isSymmSndFDerivAt (by simp)
  have hspec := pullback_const_christoffel hφ hB hx
  -- the derivative of `G` in terms of `D²φ`
  have hDG : ∀ X a b, fderiv ℝ G x X a b =
      B (fderiv ℝ (fderiv ℝ φ) x X a) (fderiv ℝ φ x b) +
        B (fderiv ℝ φ x a) (fderiv ℝ (fderiv ℝ φ) x X b) := by
    intro X a b
    rw [hGdef, fderiv_pullback_apply (differentiableAt_const _) hφd hD₁]
    simp
  -- differentiate `G(Γ(v, w), u) = B(D²φ v w, Dφ u)` at `x`
  have key : ∀ X v w u, G x (fderiv ℝ (christoffel G) x X v w) u =
      B (fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x X v w) (fderiv ℝ φ x u) +
        B (fderiv ℝ (fderiv ℝ φ) x v w) (fderiv ℝ (fderiv ℝ φ) x X u) -
        fderiv ℝ G x X (christoffel G x v w) u := by
    intro X v w u
    have hev : (fun y ↦ G y (christoffel G y v w) u) =ᶠ[𝓝 x]
        fun y ↦ B (fderiv ℝ (fderiv ℝ φ) y v w) (fderiv ℝ φ y u) :=
      (eventually_pullback_const_christoffel hφ hB hx).mono fun y hy ↦ hy v w u
    have hΓvw : DifferentiableAt ℝ (fun y ↦ christoffel G y v w) x :=
      (hΓ.clm_apply (differentiableAt_const v)).clm_apply (differentiableAt_const w)
    have hIIvw : DifferentiableAt ℝ (fun y ↦ fderiv ℝ (fderiv ℝ φ) y v w) x :=
      (hD₂.clm_apply (differentiableAt_const v)).clm_apply (differentiableAt_const w)
    have hAu : DifferentiableAt ℝ (fun y ↦ fderiv ℝ φ y u) x :=
      hD₁.clm_apply (differentiableAt_const u)
    have h := congrArg (fun L : E →L[ℝ] ℝ ↦ L X) hev.fderiv_eq
    rw [fderiv_bilin_apply_apply hGd hΓvw (differentiableAt_const u),
      fderiv_bilin_apply_apply (differentiableAt_const B) hIIvw hAu,
      fderiv_clm_apply_apply_const hΓ, fderiv_clm_apply_apply_const hD₂,
      fderiv_clm_apply_const hD₁] at h
    simp only [Pi.zero_apply, zero_apply, fderiv_fun_const, map_zero, add_zero,
      zero_add] at h
    linarith
  have hsym : ∀ a b, G x a b = G x b a := pullback_const_comm hB x
  simp only [riemann_apply, map_add, map_sub, add_apply, sub_apply]
  rw [key, key, hDG, hDG, hspec X, hspec Y]
  have h3 : fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x X Y Z =
      fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x Y X Z := by rw [hIII X Y]
  have e1 : B (fderiv ℝ φ x (christoffel G x Y Z)) (fderiv ℝ (fderiv ℝ φ) x X W) =
      G x (christoffel G x X W) (christoffel G x Y Z) := by
    rw [hspec, hB]
  have e2 : B (fderiv ℝ φ x (christoffel G x X Z)) (fderiv ℝ (fderiv ℝ φ) x Y W) =
      G x (christoffel G x Y W) (christoffel G x X Z) := by
    rw [hspec, hB]
  rw [h3, e1, e2]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The scalar curvature of an induced metric** in a `G x`-orthonormal basis `b`, by the Gauss
equation: `S = ∑ᵢⱼ (B(II bⱼ bⱼ, II bᵢ bᵢ) - B(II bᵢ bⱼ, II bᵢ bⱼ) - G(Γ bᵢ bᵢ, Γ bⱼ bⱼ) +
G(Γ bᵢ bⱼ, Γ bᵢ bⱼ))`. -/
theorem scalarCurvature_pullback_const (hφ : ContDiffAt ℝ 3 φ x) (hB : ∀ v w, B v w = B w v)
    (hx : (pullback φ (fun _ ↦ B) x).IsInvertible) (b : Module.Basis ι ℝ E)
    (hb : ∀ i j, pullback φ (fun _ ↦ B) x (b i) (b j) = if i = j then 1 else 0) :
    scalarCurvature (pullback φ fun _ ↦ B) x = ∑ j, ∑ i,
      (B (fderiv ℝ (fderiv ℝ φ) x (b j) (b j)) (fderiv ℝ (fderiv ℝ φ) x (b i) (b i)) -
        B (fderiv ℝ (fderiv ℝ φ) x (b i) (b j)) (fderiv ℝ (fderiv ℝ φ) x (b i) (b j)) -
        pullback φ (fun _ ↦ B) x (christoffel (pullback φ fun _ ↦ B) x (b i) (b i))
          (christoffel (pullback φ fun _ ↦ B) x (b j) (b j)) +
        pullback φ (fun _ ↦ B) x (christoffel (pullback φ fun _ ↦ B) x (b i) (b j))
          (christoffel (pullback φ fun _ ↦ B) x (b i) (b j))) := by
  have hII := (hφ.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).isSymmSndFDerivAt (by simp)
  have hGs : ∀ᶠ y in 𝓝 x, ∀ v w, pullback φ (fun _ ↦ B) y v w = pullback φ (fun _ ↦ B) y w v :=
    Eventually.of_forall fun y ↦ pullback_const_comm hB y
  rw [scalarCurvature_eq_sum_of_orthonormal (pullback_const_comm hB x) hx b hb]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [ricci_apply, trace_eq_sum_of_orthonormal b hb]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [flip_apply]
  rw [pullback_const_comm hB x, pullback_const_riemann hφ hB hx, hII (b j) (b i),
    christoffel_comm hGs (b j) (b i)]

/-- **The Gauss equation in codimension one.** Let `φ` be `C³` at `x` with invertible induced
metric `G`, and `H` a subspace containing the values of `Dφ x` and `D²φ x`. Suppose that the
vectors of `H` that are `B`-orthogonal to the range of `Dφ x` are the multiples of one `N`, itself
`B`-orthogonal to that range, with `B N N ≠ 0`. Then in a `G x`-orthonormal basis `b`, with
`h(v, w) = B(D²φ v w, N)`, `S = ((∑ᵢ h(bᵢ, bᵢ))² - ∑ᵢⱼ h(bᵢ, bⱼ)²) / B(N, N)`. -/
theorem scalarCurvature_pullback_const_of_normal (hφ : ContDiffAt ℝ 3 φ x)
    (hB : ∀ v w, B v w = B w v) (hx : (pullback φ (fun _ ↦ B) x).IsInvertible)
    (H : Submodule ℝ F) (hA : ∀ u, fderiv ℝ φ x u ∈ H)
    (hII : ∀ v w, fderiv ℝ (fderiv ℝ φ) x v w ∈ H)
    (N : F) (hN : ∀ u, B N (fderiv ℝ φ x u) = 0) (hNN : B N N ≠ 0)
    (hperp : ∀ m ∈ H, (∀ u, B m (fderiv ℝ φ x u) = 0) → ∃ t : ℝ, m = t • N)
    (b : Module.Basis ι ℝ E)
    (hb : ∀ i j, pullback φ (fun _ ↦ B) x (b i) (b j) = if i = j then 1 else 0) :
    scalarCurvature (pullback φ fun _ ↦ B) x =
      ((∑ i, B (fderiv ℝ (fderiv ℝ φ) x (b i) (b i)) N) ^ 2 -
        ∑ i, ∑ j, B (fderiv ℝ (fderiv ℝ φ) x (b i) (b j)) N ^ 2) / B N N := by
  have hspec : ∀ v w u, B (fderiv ℝ φ x (christoffel (pullback φ fun _ ↦ B) x v w))
      (fderiv ℝ φ x u) = B (fderiv ℝ (fderiv ℝ φ) x v w) (fderiv ℝ φ x u) := fun v w u ↦ by
    simpa using pullback_const_christoffel hφ hB hx v w u
  rw [scalarCurvature_pullback_const hφ hB hx b hb]
  simp only [pullback_apply]
  generalize christoffel (pullback φ fun _ ↦ B) x = Γ at hspec ⊢
  generalize fderiv ℝ (fderiv ℝ φ) x = II at hspec hII ⊢
  generalize fderiv ℝ φ x = A at hspec hA hN hperp ⊢
  -- the normal part of `II v w` is `t(v, w) N`, `t = B(II v w, N) / B(N, N)`
  have hdec : ∀ v w, II v w = A (Γ v w) + (B (II v w) N / B N N) • N := by
    intro v w
    obtain ⟨t, ht⟩ := hperp (II v w - A (Γ v w)) (H.sub_mem (hII v w) (hA _)) fun u ↦ by
      rw [map_sub, sub_apply, hspec, sub_self]
    have hBt : B (II v w) N = t * B N N := by
      have := congrArg (fun m ↦ B m N) ht
      simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul] at this
      rw [hB (A _) N, hN, sub_zero] at this
      exact this
    rw [hBt, mul_div_cancel_right₀ _ hNN, ← ht]
    abel
  have hterm : ∀ a b' c d, B (II a b') (II c d) =
      B (A (Γ a b')) (A (Γ c d)) + B (II a b') N * B (II c d) N / B N N := by
    intro a b' c d
    conv_lhs => rw [hdec a b', hdec c d]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    have hN' : ∀ u, B (A u) N = 0 := fun u ↦ (hB (A u) N).trans (hN u)
    simp only [hN, hN']
    field_simp
    ring
  calc _ = ∑ j, ∑ i, (B (II (b j) (b j)) N * B (II (b i) (b i)) N -
        B (II (b i) (b j)) N ^ 2) / B N N := by
        refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hterm, hterm, hB (A (Γ (b j) (b j)))]
        ring
    _ = (∑ j, ∑ i, B (II (b j) (b j)) N * B (II (b i) (b i)) N -
        ∑ j, ∑ i, B (II (b i) (b j)) N ^ 2) / B N N := by
        simp only [sub_div, Finset.sum_div, Finset.sum_sub_distrib]
    _ = _ := by
        rw [sq (∑ i, _), Finset.sum_mul_sum,
          Finset.sum_comm (f := fun j i ↦ B (II (b i) (b j)) N ^ 2)]

end FiniteDimensional

end AlphaCurvature.Curvature
