/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import AlphaCurvature.Main
import AlphaCurvature.Quantum.Assembly
import AlphaCurvature.Quantum.KernelFacts

/-!
# The gradient of the quantum excess

The quantum excess (`quantumExcess`) is `E = (2 T M + M² - Q)/W` with the ordered off-diagonal
sums `M = ∑_{i ≠ j} Kᵢⱼ` (`offSum`) and `Q = ∑_{i ≠ j} Kᵢⱼ²` (`offSumSq`),
`T = c (P(α) - P(1+2α)/W)` and `W = P(1+α)`. On the positive orthant the kernel is the
power-mean integral `kerInt`, so it is differentiable, with partial derivative `K₁ = kerD`, and

  `∂ᵢ M = 2 ∑_{j ≠ i} K₁(λᵢ, λⱼ)`,  `∂ᵢ Q = 4 ∑_{j ≠ i} Kᵢⱼ K₁(λᵢ, λⱼ)`

(`offGrad`, `offGradSq`). `excessGrad` is the gradient, linear in the gradients of the five
ingredients (`exGradF`), and `hasDerivAt_quantumExcess` is the directional-derivative hypothesis of
the Schur–Ostrowski criterion.

**The gradient difference** (`excessGrad_sub_excessGrad`): with `∂ = ∂ᵢ - ∂ⱼ` and the unordered
`M' = M/2`, `Q' = Q/2`, `W³ ∂E = Z`, where

  `Z = 4M'(cX + W² ∂M') + 4cW T̂ ∂M' + W²(4M' ∂M' - 2 ∂Q') - 2W ∂W (2M'² - Q')`,
  `X = W² ∂P(α) - W ∂P(1+2α) + ∂W (2P(1+2α) - W P(α))`,  `T̂ = P(α) W - P(1+2α)`.
-/

open Finset Filter Set
open scoped Topology

namespace AlphaCurvature.Quantum

variable {d : Type*} [Fintype d] [DecidableEq d] {α : ℝ}

theorem curvKernel_comm (a b : ℝ) : curvKernel α a b = curvKernel α b a := by
  rw [curvKernel, curvKernel, powKernel_comm, amariKernel_comm]

/-- The kernel is differentiable along lines in the positive quadrant. -/
theorem hasDerivAt_curvKernel_line (hα₁ : -1 < α) (hα : α ≤ 1) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (va vb : ℝ) :
    HasDerivAt (fun s ↦ curvKernel α (a + s * va) (b + s * vb))
      (va * kerD α a b + vb * kerD α b a) 0 := by
  have hpos : ∀ {x : ℝ} (v : ℝ), 0 < x → ∀ᶠ s in 𝓝 (0 : ℝ), 0 < x + s * v := fun {x} v hx ↦ by
    have h : Tendsto (fun s : ℝ ↦ x + s * v) (𝓝 0) (𝓝 x) :=
      (by fun_prop : Continuous fun s : ℝ ↦ x + s * v).tendsto' 0 x (by simp)
    exact h.eventually (lt_mem_nhds hx)
  refine (hasDerivAt_kerInt_line ha hb va vb).congr_of_eventuallyEq ?_
  filter_upwards [hpos va ha, hpos vb hb] with s h1 h2
  exact curvKernel_eq_kerInt hα₁ hα h1 h2

/-! ### The off-diagonal sums and their gradients -/

/-- The ordered off-diagonal sum `∑_{i ≠ j} Kᵢⱼ`. -/
noncomputable def offSum (α : ℝ) (l : d → ℝ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else curvKernel α (l i) (l j)

/-- The ordered off-diagonal sum of squares `∑_{i ≠ j} Kᵢⱼ²`. -/
noncomputable def offSumSq (α : ℝ) (l : d → ℝ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else curvKernel α (l i) (l j) ^ 2

/-- `∂ᵢ offSum = 2 ∑_{j ≠ i} K₁(λᵢ, λⱼ)`. -/
noncomputable def offGrad (α : ℝ) (l : d → ℝ) (i : d) : ℝ :=
  2 * ∑ j, if i = j then 0 else kerD α (l i) (l j)

/-- `∂ᵢ offSumSq = 4 ∑_{j ≠ i} Kᵢⱼ K₁(λᵢ, λⱼ)`. -/
noncomputable def offGradSq (α : ℝ) (l : d → ℝ) (i : d) : ℝ :=
  4 * ∑ j, if i = j then 0 else curvKernel α (l i) (l j) * kerD α (l i) (l j)

/-- Collecting a symmetric line derivative of an off-diagonal sum into a gradient. -/
theorem sum_sum_ite_line (g : d → d → ℝ) (v : d → ℝ) :
    ∑ i, ∑ j, (if i = j then 0 else v i * g i j + v j * g j i) =
      ∑ a, (2 * ∑ j, if a = j then 0 else g a j) * v a := by
  have h1 : ∑ i, ∑ j, (if i = j then (0 : ℝ) else v j * g j i) =
      ∑ i, ∑ j, (if i = j then 0 else v i * g i j) := by
    rw [Finset.sum_comm]
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have h2 : ∀ i j, (if i = j then (0 : ℝ) else v i * g i j + v j * g j i) =
      (if i = j then 0 else v i * g i j) + (if i = j then 0 else v j * g j i) := fun i j ↦ by
    split_ifs <;> ring
  have h3 : ∑ i, ∑ j, (if i = j then (0 : ℝ) else v i * g i j) =
      ∑ a, (∑ j, if a = j then 0 else g a j) * v a := by
    refine sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_mul]
    refine sum_congr rfl fun j _ ↦ ?_
    split_ifs <;> ring
  simp only [h2, Finset.sum_add_distrib, h1, h3]
  rw [← two_mul, Finset.mul_sum]
  exact sum_congr rfl fun a _ ↦ by ring

section Deriv

variable {z : d → ℝ} (hα₁ : -1 < α) (hα : α ≤ 1) (hz : ∀ i, 0 < z i) (v : d → ℝ)
include hα₁ hα hz

theorem hasDerivAt_offSum :
    HasDerivAt (fun s : ℝ ↦ offSum α (z + s • v)) (∑ a, offGrad α z a * v a) 0 := by
  have h : ∀ i j, HasDerivAt
      (fun s : ℝ ↦ if i = j then (0 : ℝ) else curvKernel α ((z + s • v) i) ((z + s • v) j))
      (if i = j then 0 else v i * kerD α (z i) (z j) + v j * kerD α (z j) (z i)) 0 :=
    fun i j ↦ by
      split_ifs
      · exact hasDerivAt_const _ _
      · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
          hasDerivAt_curvKernel_line hα₁ hα (hz i) (hz j) (v i) (v j)
  have := HasDerivAt.fun_sum (u := univ) fun i _ ↦ HasDerivAt.fun_sum (u := univ) fun j _ ↦ h i j
  unfold offSum
  convert this using 1
  rw [sum_sum_ite_line]
  rfl

theorem hasDerivAt_offSumSq :
    HasDerivAt (fun s : ℝ ↦ offSumSq α (z + s • v)) (∑ a, offGradSq α z a * v a) 0 := by
  have h : ∀ i j, HasDerivAt
      (fun s : ℝ ↦ if i = j then (0 : ℝ) else curvKernel α ((z + s • v) i) ((z + s • v) j) ^ 2)
      (if i = j then 0 else v i * (2 * (curvKernel α (z i) (z j) * kerD α (z i) (z j))) +
        v j * (2 * (curvKernel α (z j) (z i) * kerD α (z j) (z i)))) 0 :=
    fun i j ↦ by
      split_ifs
      · exact hasDerivAt_const _ _
      · have := (hasDerivAt_curvKernel_line hα₁ hα (hz i) (hz j) (v i) (v j)).pow 2
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        convert this using 1
        simp only [zero_mul, add_zero, Nat.cast_ofNat]
        rw [curvKernel_comm (z j) (z i)]
        ring
  have := HasDerivAt.fun_sum (u := univ) fun i _ ↦ HasDerivAt.fun_sum (u := univ) fun j _ ↦ h i j
  unfold offSumSq
  convert this using 1
  rw [sum_sum_ite_line]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [offGradSq, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> ring

end Deriv

/-! ### The gradient of the excess -/

/-- The derivative of `E = (2 c (P - R/W) M + M² - Q)/W`, linear in the derivatives
`gP, gR, gW, gM, gQ` of `P, R, W, M, Q`. -/
noncomputable def exGradF (c P R W M Q gP gR gW gM gQ : ℝ) : ℝ :=
  2 * c * M / W * gP - 2 * c * M / W ^ 2 * gR +
    (2 * c * M * R / W ^ 3 - (2 * (c * (P - R / W)) * M + M ^ 2 - Q) / W ^ 2) * gW +
    (2 * (c * (P - R / W)) + 2 * M) / W * gM - W⁻¹ * gQ

theorem sum_exGradF {ι : Type*} [Fintype ι] (c P R W M Q : ℝ) (gP gR gW gM gQ v : ι → ℝ) :
    ∑ a, exGradF c P R W M Q (gP a) (gR a) (gW a) (gM a) (gQ a) * v a =
      exGradF c P R W M Q (∑ a, gP a * v a) (∑ a, gR a * v a) (∑ a, gW a * v a)
        (∑ a, gM a * v a) (∑ a, gQ a * v a) := by
  simp only [exGradF, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc,
    Finset.mul_sum]

theorem exGradF_sub (c P R W M Q gP gR gW gM gQ gP' gR' gW' gM' gQ' : ℝ) :
    exGradF c P R W M Q gP gR gW gM gQ - exGradF c P R W M Q gP' gR' gW' gM' gQ' =
      exGradF c P R W M Q (gP - gP') (gR - gR') (gW - gW') (gM - gM') (gQ - gQ') := by
  simp only [exGradF]
  ring

/-- **The gradient difference in unordered sums**: `W³ ∂E = Z`. -/
theorem exGradF_eq (c P R W M Q dP dR dW dM dQ : ℝ) (hW : W ≠ 0) :
    exGradF c P R W (2 * M) (2 * Q) dP dR dW (2 * dM) (2 * dQ) =
      (4 * M * (c * (W ^ 2 * dP - W * dR + dW * (2 * R - W * P)) + W ^ 2 * dM) +
        4 * c * W * (P * W - R) * dM + W ^ 2 * (4 * M * dM - 2 * dQ) -
        2 * W * dW * (2 * M ^ 2 - Q)) / W ^ 3 := by
  simp only [exGradF]
  field_simp
  ring

/-- **The gradient of the quantum excess.** -/
noncomputable def excessGrad (α : ℝ) (z : d → ℝ) (a : d) : ℝ :=
  exGradF ((1 + α) / 2) (powSum z α) (powSum z (1 + 2 * α)) (powSum z (1 + α)) (offSum α z)
    (offSumSq α z) (α * z a ^ (α - 1)) ((1 + 2 * α) * z a ^ (1 + 2 * α - 1))
    ((1 + α) * z a ^ (1 + α - 1)) (offGrad α z a) (offGradSq α z a)

theorem quantumExcess_eq (l : d → ℝ) :
    quantumExcess α l = (2 * ((1 + α) / 2 * (powSum l α - powSum l (1 + 2 * α) /
      powSum l (1 + α))) * offSum α l + offSum α l ^ 2 - offSumSq α l) / powSum l (1 + α) :=
  rfl

/-- **The directional derivative of the quantum excess** is `∑ₐ ∂ₐE vₐ`. -/
theorem hasDerivAt_quantumExcess [Nonempty d] (hα₁ : -1 < α) (hα : α ≤ 1) {z : d → ℝ}
    (hz : ∀ i, 0 < z i) (v : d → ℝ) :
    HasDerivAt (fun s : ℝ ↦ quantumExcess α (z + s • v)) (∑ a, excessGrad α z a * v a) 0 := by
  have hP := hasDerivAt_powSum hz v
  have hM := hasDerivAt_offSum hα₁ hα hz v
  have hQ := hasDerivAt_offSumSq hα₁ hα hz v
  have hW := (powSum_pos hz (1 + α)).ne'
  have hW0 : powSum (z + (0 : ℝ) • v) (1 + α) ≠ 0 := by simpa using hW
  have := (((((hP α).sub ((hP (1 + 2 * α)).div (hP (1 + α)) hW0)).const_mul
    ((1 + α) / 2)).const_mul 2).mul hM |>.add (hM.pow 2) |>.sub hQ).div (hP (1 + α)) hW0
  simp only [quantumExcess_eq]
  convert this using 1
  simp only [excessGrad, Pi.sub_apply, Pi.div_apply, Pi.mul_apply, Pi.add_apply, Pi.pow_apply,
    zero_smul, add_zero, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [sum_exGradF]
  have e : ∀ s : ℝ, ∑ a, s * z a ^ (s - 1) * v a = ∑ a, v a * s * z a ^ (s - 1) :=
    fun s ↦ sum_congr rfl fun a _ ↦ by ring
  rw [e α, e (1 + 2 * α), e (1 + α)]
  simp only [exGradF]
  generalize ∑ a, v a * α * z a ^ (α - 1) = dP
  generalize ∑ a, v a * (1 + 2 * α) * z a ^ (1 + 2 * α - 1) = dR
  generalize ∑ a, v a * (1 + α) * z a ^ (1 + α - 1) = dW
  generalize ∑ a, offGrad α z a * v a = dM
  generalize ∑ a, offGradSq α z a * v a = dQ
  generalize powSum z (1 + α) = W at hW ⊢
  field_simp
  ring

/-- **The gradient difference**: `∂ᵢE - ∂ⱼE` is the `Z`-form of `exGradF_eq` over `W³`, in the
unordered sums `M/2`, `Q/2` and the differences of the ingredient gradients. -/
theorem excessGrad_sub_excessGrad {z : d → ℝ} (hz : ∀ i, 0 < z i) (i j : d) :
    excessGrad α z i - excessGrad α z j =
      exGradF ((1 + α) / 2) (powSum z α) (powSum z (1 + 2 * α)) (powSum z (1 + α))
        (2 * (offSum α z / 2)) (2 * (offSumSq α z / 2))
        (α * z i ^ (α - 1) - α * z j ^ (α - 1))
        ((1 + 2 * α) * z i ^ (1 + 2 * α - 1) - (1 + 2 * α) * z j ^ (1 + 2 * α - 1))
        ((1 + α) * z i ^ (1 + α - 1) - (1 + α) * z j ^ (1 + α - 1))
        (2 * ((offGrad α z i - offGrad α z j) / 2))
        (2 * ((offGradSq α z i - offGradSq α z j) / 2)) := by
  have _ := hz
  simp only [mul_div_cancel₀ _ (two_ne_zero' ℝ)]
  exact exGradF_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end AlphaCurvature.Quantum
