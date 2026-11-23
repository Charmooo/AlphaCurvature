/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import AlphaCurvature.Quantum.ClosedForm

/-!
# The scalar curvature of the quantum α-geometry

The quantum α-geometry near a positive definite `ρ₀` is the pullback of the Hilbert–Schmidt form
by the chart `z ↦ A(ρ₀ + z)` of `ρ₀ + {traceless Hermitian}`, where `A(ρ) = p ρ^(1/p)` with
`p = 2/(1 - α)`, and `A = log` at `α = 1` (`amariChart`, `amari`). The powers and the logarithm
are those of the continuous functional calculus (`matPow_eq_cfc`, `matLog_eq_cfc`).

* `scalarCurvature_amariChart`: **the closed form** at every positive definite `ρ₀`, in the
  eigenvalues of `ρ₀` (`quantumCurv`). Conjugation by a unitary is an isometry between the charts
  at `ρ₀` and at `U* ρ₀ U` (`pullback_amariChart_conj`), so the scalar curvature is unitarily
  invariant (`scalarCurvature_amariChart_conj`), and at a diagonal state it is
  `scalarCurvature_amariChart_diagonal`.
* `scalarCurvature_amariChart_eq_add`: **the split** `S_q(ρ₀) = S_cl(λ) + E(λ)` into the scalar
  curvature of the classical α-geometry at the eigenvalues `λ` (`AlphaCurvature.alphaChart`) and
  the quantum excess `E` (`quantumExcess`), which depends only on the off-diagonal kernel
  `Kᵢⱼ`, `i ≠ j`.
-/

open scoped Matrix.Norms.L2Operator Topology ComplexOrder
open Matrix ContinuousLinearMap Filter Set
open AlphaCurvature.Curvature

namespace AlphaCurvature.Quantum

variable {d : Type*} [Fintype d] [DecidableEq d] {α : ℝ}

/-! ### The closed form and the excess -/

/-- **The closed form** of the scalar curvature in the eigenvalues `λ`: with
`Kᵢⱼ = curvKernel α λᵢ λⱼ`, `c = (1 + α)/2`, `P(s) = ∑ᵢ λᵢˢ` and `W = P(1 + α)`,
`[(∑ K)² - ∑ K² - 2c (∑ K) P(1+2α)/W + 2c² P(1+3α)/W] / W`. -/
noncomputable def quantumCurv (α : ℝ) (l : d → ℝ) : ℝ :=
  ((∑ i, ∑ j, curvKernel α (l i) (l j)) ^ 2 - ∑ i, ∑ j, curvKernel α (l i) (l j) ^ 2 -
    2 * ((1 + α) / 2) * (∑ i, ∑ j, curvKernel α (l i) (l j)) *
      (∑ i, l i ^ (1 + 2 * α)) / ∑ i, l i ^ (1 + α) +
    2 * ((1 + α) / 2) ^ 2 * (∑ i, l i ^ (1 + 3 * α)) / ∑ i, l i ^ (1 + α)) /
    ∑ i, l i ^ (1 + α)

/-- **The quantum excess** `E = (2 T M + M² - Q) / W`, with the off-diagonal sums
`M = ∑_{i ≠ j} Kᵢⱼ` and `Q = ∑_{i ≠ j} Kᵢⱼ²`, and `T = c (P(α) - P(1+2α)/W)`. -/
noncomputable def quantumExcess (α : ℝ) (l : d → ℝ) : ℝ :=
  (2 * ((1 + α) / 2 * (∑ i, l i ^ α - (∑ i, l i ^ (1 + 2 * α)) / ∑ i, l i ^ (1 + α))) *
      (∑ i, ∑ j, if i = j then 0 else curvKernel α (l i) (l j)) +
    (∑ i, ∑ j, if i = j then 0 else curvKernel α (l i) (l j)) ^ 2 -
    ∑ i, ∑ j, (if i = j then 0 else curvKernel α (l i) (l j) ^ 2)) / ∑ i, l i ^ (1 + α)

/-- **The split**: the quantum closed form is the classical one plus the excess. -/
theorem quantumCurv_eq_add [Nonempty d] {l : d → ℝ} (hl : ∀ i, 0 < l i) :
    quantumCurv α l =
      scalarCurvature (alphaChart α (simplexTangent d) l) 0 + quantumExcess α l := by
  rw [scalarCurvature_alphaChart hl, quantumCurv, quantumExcess]
  have hK : ∀ i, curvKernel α (l i) (l i) = (1 + α) / 2 * l i ^ α := fun i ↦ curvKernel_self (hl i)
  have hM : ∑ i, ∑ j, curvKernel α (l i) (l j) =
      (1 + α) / 2 * ∑ i, l i ^ α + ∑ i, ∑ j, if i = j then 0 else curvKernel α (l i) (l j) := by
    rw [sum_sum_ite, Finset.sum_sub_distrib, Finset.sum_const_zero, zero_sub,
      Finset.mul_sum]
    simp only [hK]
    ring
  have hQ : ∑ i, ∑ j, curvKernel α (l i) (l j) ^ 2 = ((1 + α) / 2) ^ 2 * ∑ i, l i ^ (2 * α) +
      ∑ i, ∑ j, (if i = j then 0 else curvKernel α (l i) (l j) ^ 2) := by
    rw [sum_sum_ite, Finset.sum_sub_distrib, Finset.sum_const_zero, zero_sub,
      Finset.mul_sum]
    simp only [hK, mul_pow, ← Real.rpow_mul_natCast (hl _).le]
    push_cast
    ring_nf
  rw [hM, hQ]
  have hW : (∑ i, l i ^ (1 + α)) ≠ 0 :=
    (Finset.sum_pos (fun i _ ↦ Real.rpow_pos_of_pos (hl i) _) Finset.univ_nonempty).ne'
  field_simp
  ring

/-! ### Conjugation on the traceless Hermitian matrices -/

theorem conj_mem_tracelessHermitian {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ)
    {v : Matrix d d ℂ} (hv : v ∈ tracelessHermitian d) : U * v * star U ∈ tracelessHermitian d := by
  obtain ⟨hH, htr⟩ := mem_tracelessHermitian.1 hv
  exact mem_tracelessHermitian.2 ⟨isHermitian_mul_mul_conjTranspose U hH, by
    rw [trace_conj hU, htr]⟩

/-- Conjugation by a unitary restricted to the traceless Hermitian matrices. -/
noncomputable def tracelessConj {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ) :
    tracelessHermitian d ≃L[ℝ] tracelessHermitian d :=
  have hU' : star U ∈ Matrix.unitaryGroup d ℂ := Unitary.star_mem hU
  LinearEquiv.toContinuousLinearEquiv <| LinearEquiv.ofLinearMap
    ((unitaryConj hU).toLinearMap.restrict fun v hv ↦ by
      simpa using conj_mem_tracelessHermitian hU hv)
    ((unitaryConj hU').toLinearMap.restrict fun v hv ↦ by
      simpa using conj_mem_tracelessHermitian hU' hv)
    (LinearMap.ext fun v ↦ Subtype.ext (by
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      simp [← Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff.1 hU]
      simp [Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff.1 hU]))
    (LinearMap.ext fun v ↦ Subtype.ext (by
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      simp [← Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff'.1 hU]
      simp [Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff'.1 hU]))

@[simp]
theorem coe_tracelessConj {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ)
    (v : tracelessHermitian d) : (tracelessConj hU v : Matrix d d ℂ) = U * v * star U := by
  simp [tracelessConj]

theorem hsForm_conj {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ) (X Y : Matrix d d ℂ) :
    hsForm (U * X * star U) (U * Y * star U) = hsForm X Y := by
  have hUs : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  rw [hsForm_apply, hsForm_apply,
    show U * X * star U * (U * Y * star U) = U * (X * Y) * star U by
      simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (star U) U, hUs, Matrix.one_mul],
    trace_conj hU]

/-- **Conjugation intertwines the charts**: the metric at `ρ₀` is the pullback of the metric at
`U* ρ₀ U` by `z ↦ U* z U`. -/
theorem pullback_amariChart_conj {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ)
    (ρ₀ : Matrix d d ℂ) :
    pullback (amariChart α (tracelessHermitian d) ρ₀) (fun _ ↦ hsForm) =
      pullback (tracelessConj (Unitary.star_mem hU))
        (pullback (amariChart α (tracelessHermitian d) (star U * ρ₀ * U)) fun _ ↦ hsForm) := by
  have hU' : star U ∈ Matrix.unitaryGroup d ℂ := Unitary.star_mem hU
  have hUs : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hsU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have hφ : amariChart α (tracelessHermitian d) ρ₀ = unitaryConj hU ∘
      amariChart α (tracelessHermitian d) (star U * ρ₀ * U) ∘ tracelessConj hU' := by
    funext z
    simp only [Function.comp_apply, amariChart, unitaryConj_apply, ← amari_conj hU,
      Submodule.subtypeL_apply, coe_tracelessConj, star_star]
    congr 1
    simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, hsU, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hsU, Matrix.mul_one]
  ext z u w
  rw [pullback_apply, pullback_apply, (tracelessConj hU').fderiv, pullback_apply, hφ,
    (unitaryConj hU).comp_fderiv, (tracelessConj hU').comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, unitaryConj_apply,
    hsForm_conj hU]

/-- **Unitary invariance** of the scalar curvature: at `ρ₀ = U D U*` it equals the scalar
curvature at `D`, for a positive diagonal `D`. -/
theorem scalarCurvature_amariChart_conj_diagonal {U : Matrix d d ℂ}
    (hU : U ∈ Matrix.unitaryGroup d ℂ) {l : d → ℝ} (hl : ∀ i, 0 < l i) :
    scalarCurvature (pullback (amariChart α (tracelessHermitian d)
      (U * Matrix.diagonal (fun i ↦ (l i : ℂ)) * star U)) fun _ ↦ hsForm) 0 =
      scalarCurvature (pullback (amariChart α (tracelessHermitian d)
        (Matrix.diagonal fun i ↦ (l i : ℂ))) fun _ ↦ hsForm) 0 := by
  have hUs : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hD : star U * (U * Matrix.diagonal (fun i ↦ (l i : ℂ)) * star U) * U =
      Matrix.diagonal fun i ↦ (l i : ℂ) := by
    simp only [← Matrix.mul_assoc, hUs, Matrix.one_mul]
    rw [Matrix.mul_assoc, hUs, Matrix.mul_one]
  have hU' : star U ∈ Matrix.unitaryGroup d ℂ := Unitary.star_mem hU
  rw [pullback_amariChart_conj hU, hD]
  have h0 : tracelessConj hU' 0 = 0 := map_zero _
  have hG := contDiffAt_pullback (n := 2) (G := fun _ ↦ (hsForm : Matrix d d ℂ →L[ℝ] _))
    (contDiffAt_const (x := amariChart α (tracelessHermitian d)
      (Matrix.diagonal fun i ↦ (l i : ℂ)) 0))
    (contDiffAt_amariChart (α := α) (V := tracelessHermitian d) (posDef_diagonal_ofReal hl) 3)
  rw [scalarCurvature_pullback (tracelessConj hU').contDiff.contDiffAt
    ⟨tracelessConj hU', (tracelessConj hU').fderiv.symm⟩ (by rw [h0]; exact hG)
    (Eventually.of_forall fun y v w ↦ by simp only [pullback_apply]; exact hsForm_comm _ _)
    (by rw [h0]; exact isInvertible_pullback_amariChart_diagonal hl), h0]

/-- **The scalar curvature of the quantum α-geometry** at a positive definite `ρ₀`, in the
eigenvalues of `ρ₀`. -/
theorem scalarCurvature_amariChart [Nonempty d] {ρ₀ : Matrix d d ℂ} (hρ : ρ₀.PosDef) :
    scalarCurvature (pullback (amariChart α (tracelessHermitian d) ρ₀) fun _ ↦ hsForm) 0 =
      quantumCurv α hρ.1.eigenvalues := by
  have hxD : ρ₀ = (hρ.1.eigenvectorUnitary : Matrix d d ℂ) *
      Matrix.diagonal (fun i ↦ (hρ.1.eigenvalues i : ℂ)) *
      star (hρ.1.eigenvectorUnitary : Matrix d d ℂ) := by
    conv_lhs => rw [hρ.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  have key := scalarCurvature_amariChart_conj_diagonal (α := α) hρ.1.eigenvectorUnitary.2
    hρ.eigenvalues_pos
  rw [← hxD] at key
  rw [key, scalarCurvature_amariChart_diagonal hρ.eigenvalues_pos]
  rfl

/-- **The split** at a positive definite `ρ₀` with eigenvalues `λ`:
`S_q(ρ₀) = S_cl(λ) + E(λ)`, the classical α-geometry of the simplex at `λ` plus the quantum
excess. -/
theorem scalarCurvature_amariChart_eq_add [Nonempty d] {ρ₀ : Matrix d d ℂ} (hρ : ρ₀.PosDef) :
    scalarCurvature (pullback (amariChart α (tracelessHermitian d) ρ₀) fun _ ↦ hsForm) 0 =
      scalarCurvature (alphaChart α (simplexTangent d) hρ.1.eigenvalues) 0 +
        quantumExcess α hρ.1.eigenvalues := by
  rw [scalarCurvature_amariChart hρ, quantumCurv_eq_add hρ.eigenvalues_pos]

/-! ### Fidelity to the continuous functional calculus -/

theorem matPow_eq_cfc {ρ : Matrix d d ℂ} (hρ : ρ.PosDef) (s : ℝ) :
    matPow s ρ = cfc (fun x : ℝ ↦ x ^ s) ρ := by
  rw [hρ.1.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  conv_lhs => rw [hρ.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [matPow_conj _ hρ.1.eigenvectorUnitary.2]
  exact congrArg (fun M ↦ _ * M * _) (matPow_diagonal s hρ.eigenvalues_pos)

theorem matLog_eq_cfc {ρ : Matrix d d ℂ} (hρ : ρ.PosDef) : matLog ρ = cfc Real.log ρ := by
  rw [hρ.1.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  conv_lhs => rw [hρ.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [matLog_conj hρ.1.eigenvectorUnitary.2]
  exact congrArg (fun M ↦ _ * M * _) (matLog_diagonal hρ.eigenvalues_pos)

end AlphaCurvature.Quantum
