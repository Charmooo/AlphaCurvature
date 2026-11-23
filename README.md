# AlphaCurvature

A Lean 4 + Mathlib proof of the **α-geometry curvature conjecture** of Gibilisco and Isola: on
the open probability simplex with `n ≥ 3` points, the scalar curvature of the α-geometry is
strictly Schur-increasing for `p ∈ (2, ∞]` and strictly Schur-decreasing for `p ∈ (1, 2)`. Here
`p = 2/(1 − α)`. The theorems are in [`AlphaCurvature/Main.lean`](AlphaCurvature/Main.lean),
whose docstring lists the definitions the statement depends on.

```lean
theorem AlphaCurvature.scalarCurvature_alphaChart_lt_of_two_lt {n : ℕ} {x y : Fin n → ℝ}
    {p : ℝ} (hp : 2 < p) (hn : 3 ≤ n)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hxy : IsMajorizedBy x y)
    (hne : ∀ σ : Equiv.Perm (Fin n), x ∘ σ ≠ y) :
    scalarCurvature (alphaChart (1 - 2 / p) (simplexTangent (Fin n)) y) 0 <
      scalarCurvature (alphaChart (1 - 2 / p) (simplexTangent (Fin n)) x) 0

theorem AlphaCurvature.scalarCurvature_alphaChart_lt_of_lt_two {n : ℕ} {x y : Fin n → ℝ}
    {p : ℝ} (hp₁ : 1 < p) (hp : p < 2) (hn : 3 ≤ n)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hxy : IsMajorizedBy x y)
    (hne : ∀ σ : Equiv.Perm (Fin n), x ∘ σ ≠ y) :
    scalarCurvature (alphaChart (1 - 2 / p) (simplexTangent (Fin n)) x) 0 <
      scalarCurvature (alphaChart (1 - 2 / p) (simplexTangent (Fin n)) y) 0
```

`IsMajorizedBy x y` says that `x` is more mixed than `y`. The endpoint `p = ∞` is `α = 1`, which
`scalarCurvature_alphaChart_lt` covers with the logarithmic embedding. Every theorem uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Which statement

This is **Conjecture 4.1** of P. Gibilisco and T. Isola, *On the monotonicity of scalar curvature
in classical and quantum information geometry* (J. Math. Phys. 46 (2005); arXiv
math-ph/0407007). It reappears as Conjecture 1 of P. Gibilisco, *Lp unit spheres and the
α-geometries: questions and perspectives* (Entropy 22 (2020) 1409), which lists it as open.

| Gibilisco–Isola | Lean |
|---|---|
| Def. 4.3: the α-geometry is the pullback of the Euclidean metric by `A_p(ρ) = p ρ^(1/p)`, and by `log ρ` at `p = ∞` | `alphaChart α (simplexTangent (Fin n)) x`: the metric `∑ᵢ xᵢ^(−1−α) dxᵢ²` in the affine chart of the simplex through `x`. `pullback_amariEmbed` proves it is the Amari pullback, for every `α`. |
| Def. 4.4: `Scal_p(ρ)` | `scalarCurvature G 0`, the trace of `G⁻¹ Ric` at the centre of the chart |
| `p = 2` gives `(n − 1)(n − 2)/4`, and `p = 1` gives `0` | `scalarCurvature_alphaChart_zero`; at `α = −1` the closed form vanishes |
| Def. 2.3: `x ≻ y`, "x is more mixed" | `IsMajorizedBy x y`: equal totals, and the sums of the `k` smallest entries of `x` are at least those of `y` |
| Def. 2.4: strict means "x is not a permutation of y" | `hne : ∀ σ, x ∘ σ ≠ y` |
| `n > 2` | `3 ≤ n`. On two points the curve has no intrinsic curvature. |
| density vectors | positive vectors of any total, which majorization preserves |

Also in `Main.lean`:
* the non-strict forms `scalarCurvature_alphaChart_le` (`0 ≤ α ≤ 1`) and
  `scalarCurvature_alphaChart_le_of_nonpos` (`−1 ≤ α ≤ 0`), for every `n`;
* the strict forms in `α`, `scalarCurvature_alphaChart_lt` (`0 < α ≤ 1`) and
  `scalarCurvature_alphaChart_lt_of_neg` (`−1 < α < 0`).

**Cross-check of the closed form.** [`scripts/t1_closed_form.py`](scripts/t1_closed_form.py)
computes the scalar curvature directly from the metric in coordinates, with Christoffel symbols
and the Riemann tensor in 40-digit arithmetic. It agrees with the closed form that Lean proves
equal to `scalarCurvature` (`scalarCurvature_alphaChart`) to a relative error of `3·10⁻³⁷`, for
`n = 3…6` and `p ∈ {3/2, 2, 3, 4, 10}`.

## The route

1. **Curvature of a metric in a chart** (`Curvature/`). The Christoffel, Riemann, Ricci and scalar
   curvature maps of a field of bilinear forms, how they change under a change of chart, and the
   curvature of a Hessian metric: `S = ¼ (|T|² − |τ|²)` in an orthonormal basis.
2. **The closed form** (`Metric.lean`). The α-metric is a Hessian metric in the affine chart of the
   simplex. Contracting its cubic form against the completeness kernel
   `Kᵢⱼ = wᵢ δᵢⱼ − wᵢ wⱼ / W`, with `w = x^(1+α)`, gives
   `S = (1 + α)²/4 · ((P(α)² − P(2α)) P(1+α) − 2 P(α) P(1+2α) + 2 P(1+3α)) / P(1+α)²`, where
   `P(s) = ∑ᵢ xᵢˢ`.
3. **The gradient** (`Gradient.lean`). With `a = xᵢ > b = xⱼ`, the difference `∂ᵢS − ∂ⱼS` is a
   positive multiple of a numerator `Z`. `Z` is a cubic polynomial in five power sums `q` of the
   other points.
4. **The per-point form** (`PerPoint.lean`). Assign each monomial of `Z(q)` to its highest-index
   power sum. This writes `Z = ∑ₖ Ψ(yₖ; q)`, one term for each other point, in an explicit closed
   form. For `0 < α ≤ 1`, `Ψ < 0`. Its one indefinite part reduces to a one-variable inequality,
   proved by the tangent line of `sᵅ` and Bernoulli. For `−1 < α < 0`, `Ψ > 0`, by
   `∑ vₗ² ≤ (∑ vₗ)²` and the tangent line of `t^(1+α)`.
5. **Schur–Ostrowski** (`ForMathlib/Majorization.lean`, `Main.lean`). A symmetric function whose
   gradient is antitone in the entry is Schur-increasing, and strictly so if the gradient drops
   strictly across distinct entries. With a third point present, `Ψ` gives that strict drop.

The per-point form was found numerically before it was proved
([`scripts/t6_per_point.py`](scripts/t6_per_point.py),
[`scripts/t7_per_point_neg.py`](scripts/t7_per_point_neg.py)). Two other natural ways of
splitting `Z` fail for `α ≥ 0.9`. A split of `Z` into terms over sets of at most three other
points proves the conjecture for `p ≤ 10`, but past about `p ≈ 30` its two-point term changes
sign. At `α = 1`, `Z` is
`−2(a − b)` times a sum of squares plus positive terms. The top-degree part is
`∑ₖ yₖ² (∑ₗ yₗ − 2yₖ)²`, which pairs each point with a sum over all points, and no
fixed-size split can see that.

## Building

```bash
lake exe cache get
```

```bash
lake build
```

The toolchain is in [`lean-toolchain`](lean-toolchain), and Mathlib is pinned in
[`lakefile.toml`](lakefile.toml). The scripts need Python with `mpmath`, `numpy`, `scipy` and
`sympy`.

## Layout

| File | Contents |
|---|---|
| `Curvature/Basic.lean` | Christoffel, Riemann, Ricci and scalar curvature of a field of bilinear forms |
| `Curvature/Pullback.lean` | change of chart; curvature is a tensor |
| `Curvature/Hessian.lean` | curvature of a metric with a totally symmetric derivative |
| `ForMathlib/Basic.lean` | small lemmas: derivatives of fields of linear maps, invertible bilinear forms |
| `ForMathlib/Majorization.lean` | majorization and the Schur–Ostrowski criterion, non-strict and strict |
| `Metric.lean` | the α-metric, the Amari embedding, the chart, the closed form |
| `Gradient.lean` | the curvature on the positive orthant, its gradient, the numerator `Z` |
| `PerPoint.lean` | the per-point form of `Z` and its sign |
| `Main.lean` | the conjecture |

## Prior work

* Gibilisco and Isola's Theorem 4.1 is the two-point model of the conjecture. It is stated for
  `c_p`, the curvature of the image of the simplex as a curve in the plane, because the
  intrinsic scalar curvature of a curve is zero. A. Andai, *On the curvature of the quantum state space with pull-back metrics* (Linear Algebra
  Appl. 426 (2007); arXiv math-ph/0604031), reduced the three-point case to an inequality in one
  variable.
* The endpoint `p = ∞` (the logarithmic geometry, `α = 1`), with every `n ≥ 3` and the strict
  form, was proved in Lean first, in the
  [trureturing](https://github.com/the-omega-institute/trureturing) project: pull request
  [#15566](https://github.com/the-omega-institute/trureturing/pull/15566), merged on
  11 October 2026. In that project the finite-`p` case is still listed as open
  ([issue #26510](https://github.com/the-omega-institute/trureturing/issues/26510), last updated
  4 November 2026). The same project proved the `p = 3` slice of the quantum Conjecture 4.2
  ([#15831](https://github.com/the-omega-institute/trureturing/pull/15831)). This library proves
  the endpoint independently, through the same per-point form as for finite `p`.
* As of 23 November 2026 we know of no other proof. Lu, *The Lᵖ-geometry and its applications*
  (arXiv 2512.13051), answers Problem 7 of Gibilisco's 2020 list, on Orlicz spaces, and not the
  curvature conjecture.

Please tell us about any earlier work that we have missed.

## History

The library was developed inside a larger Lean project and extracted here. The curvature
infrastructure is shared with [PetzCurvature](https://github.com/Charmooo/PetzCurvature).

## License

Apache 2.0, see [`LICENSE`](LICENSE).
