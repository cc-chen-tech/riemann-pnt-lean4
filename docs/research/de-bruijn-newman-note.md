# de Bruijn–Newman Constant Research Note

## Purpose

This note opens a new research direction for the repository: the de
Bruijn–Newman constant `Λ`.  It is not a proof plan yet.  It fixes the
mathematical definitions, records the classical fact chain with literature
anchors, audits the current Mathlib (vendored with Lean toolchain v4.29.1)
for the infrastructure that a formalization of `Λ ≥ 0` would need, and
proposes a phased plan with effort and risk estimates.  The companion Lean
skeleton is `RiemannExplorer/DeBruijnNewman.lean`.

A grep over the Lean sources confirms that the repository currently has
**zero** prior mention of de Bruijn–Newman, `H_t`, or the constant `Λ`; this
is a first-stage exploration.

## Mathematical Definitions

All notation follows Rodgers–Tao, arXiv:1801.05914 (published as
*Forum of Mathematics, Pi* 8 (2020), e6 — note: the venue is Forum Math. Pi,
not Acta Math.).

### The kernel `Φ`

```text
Φ(u) := Σ_{n ≥ 1} (2 π² n⁴ e^{9u} − 3 π n² e^{5u}) · exp(−π n² e^{4u}),
        u ∈ ℝ.
```

Facts:

- The series converges absolutely for every fixed real `u`, because for
  fixed `u` the factor `exp(−π n² e^{4u})` decays super-polynomially in `n`.
  (Proved in the Lean skeleton as `summable_phiTerm`.)
- `Φ` is even: `Φ(−u) = Φ(u)`.  This is a theorem of Riemann, equivalent
  via Poisson summation to the functional equation of `ζ`; it is *not*
  visible from the raw series.
- `Φ` decays double-exponentially: `Φ(u) ~ 2 π² e^{9u − π e^{4u}}` as
  `u → +∞` (and by evenness also as `u → −∞`).  In particular `Φ` is
  super-exponentially decaying ("faster than any exponential").

### The family `H_t`

```text
H_t(z) := ∫_0^∞ e^{t u²} Φ(u) cos(z u) du,    t ∈ ℝ, z ∈ ℂ.
```

Facts:

- The integral converges absolutely for every `t ∈ ℝ` and `z ∈ ℂ` (the
  double-exponential decay of `Φ` dominates `e^{t u²} · |cos(z u)|`), so
  `H_t` is an even entire function of order at most `1`.
- Backward heat equation: `∂_t H_t = −∂_z² H_t`, since
  `∂_t e^{t u²} = u² e^{t u²}` and `∂_z² cos(z u) = −u² cos(z u)`.  This is
  the "heat flow evolution of the Riemann ξ function" in the Polymath15
  viewpoint.
- Fundamental identity (Riemann, essentially the original 1859
  computation):

```text
H_0(z) = (1/8) · Ξ(z/2),    where Ξ(z) := ξ(1/2 + i z)
```

  with `ξ(s) = (1/2) s (s−1) π^{−s/2} Γ(s/2) ζ(s)`.  Hence

```text
H_0 has only real zeros  ⇔  Ξ has only real zeros  ⇔  RH,
```

  because `Ξ(z) = 0` at `z = γ − i(β − 1/2)` for `ρ = β + iγ` a nontrivial
  zero, and `z` is real iff `β = 1/2`.

### The constant `Λ`

Define

```text
Λ := inf { t ∈ ℝ : H_t has only real zeros }.
```

De Bruijn's monotonicity theorem (below) shows the set on the right is
upward-closed, so `Λ` is a genuine threshold: `H_t` has only real zeros iff
`t ≥ Λ` (the boundary case `t = Λ` follows from a Hurwitz-type closedness
argument).  Until that theory is formalized, the `sInf` value is a
placeholder in the sense of the repository's `def ... : Prop` target
discipline.

## Classical Fact Chain (Literature Anchors)

| Fact | Statement | Source |
| --- | --- | --- |
| de Bruijn monotonicity | If `H_t` has only real zeros and `t' ≥ t`, then `H_{t'}` has only real zeros | N. G. de Bruijn, *The roots of trigonometric integrals*, Duke Math. J. 17 (1950), 197–226 |
| de Bruijn strip theorem | If the zeros of `H_0` lie in `|Im z| ≤ Δ`, then `H_t` has only real zeros for `t ≥ Δ²/2` | same paper |
| de Bruijn upper bound | `Λ ≤ 1/2` (apply the strip theorem with `Δ = 1`: zeros of `H_0` are `2γ − 2i(β−1/2)`, so `|Im| ≤ 1` by the critical strip; the `z/2` scaling in `H_0 = (1/8)Ξ(z/2)` doubles the half-width `1/2` to `1`) | same paper |
| Newman lower bound | `Λ > −∞`; Newman conjectured `Λ ≥ 0` | C. M. Newman, *Fourier transforms with only real zeros*, Proc. Amer. Math. Soc. 61 (1976), 245–251 |
| Csordas–Norfolk–Varga | `Λ ≥ −0.385` (constructive, via a Jensen polynomial with nonreal zeros) | Numer. Math. 52 (1988), 483–497 |
| te Riele | `Λ ≥ −0.0991` | Numer. Math. 58 (1991), 661–667 |
| Csordas–Smith–Varga (Lehmer pairs) | `Λ ≥ −4.379·10⁻⁶` | *Lehmer pairs of zeros, the de Bruijn–Newman constant Λ, and the Riemann hypothesis*, Constr. Approx. 10 (1994), 107–129 |
| Odlyzko | `Λ ≥ −2.7·10⁻⁹`, using a Lehmer pair near zero number `10²⁰` | *An improved bound for the de Bruijn–Newman constant*, Numer. Algorithms 25 (2000), 293–303 |
| Saouter–Gourdon–Demichel | `Λ ≥ −1.15·10⁻¹¹` | Math. Comp. 80 (2011), 2281–2287 |
| Ki–Kim–Lee | `Λ < 1/2` (strict improvement of de Bruijn) | *On the de Bruijn–Newman constant*, Adv. Math. 222 (2009), 281–306 |
| Polymath15 | `Λ ≤ 0.22` (certified numerics up to a large height + shrinking of the effective strip via the classical zero-free region + a Lehmer-pair-free region) | D.H.J. Polymath, *Effective approximation of heat flow evolution of the Riemann ξ function, and a new upper bound for the de Bruijn–Newman constant*, Res. Math. Sci. 6 (2019), Art. 31; arXiv:1904.12438 |
| Rodgers–Tao (Newman's conjecture) | `Λ ≥ 0` | arXiv:1801.05914 (2018); Forum Math. Pi 8 (2020), e6, 62 pp. |
| Logical position of RH | `RH ⇔ Λ ≤ 0`; combined with `Λ ≥ 0`, `RH ⇔ Λ = 0` | folklore, made precise by the threshold property above |

The Rodgers–Tao argument in one paragraph: assume for contradiction that
`Λ < 0`.  Then for every `Λ < t ≤ 0` the zeros of `H_t` are all real, and
they evolve under the de Bruijn ODE
`ż_j(t) = 2 Σ_{k ≠ j} (z_j(t) − z_k(t))⁻¹`.  Building on the
Csordas–Smith–Varga analysis of this dynamics, one obtains increasingly
strong control on the zeros of `H_t` in the range `Λ < t ≤ 0`, until one
concludes that the zeros of `H_0` are in *local equilibrium*: locally (on
average) they behave as if equally spaced in an arithmetic progression,
with gaps close to the global average gap.  Since `Λ < 0` implies that
`H_0` is real-zeroed, i.e. RH, the zeros of `H_0` are (rescaled) zeta
zeros, and local equilibrium contradicts known results on the local
distribution of zeta zeros, specifically Montgomery's pair-correlation
estimates (which are legitimately available because RH holds inside the
contradiction assumption).

Deep inputs used by that proof, as an inventory for formalization:

1. de Bruijn's theory: monotonicity, the strip theorem, the zero-dynamics
   ODE (itself justified via the Hadamard product of `H_t`).
2. Hadamard factorization of the order-1 entire function `H_t`, and
   identities such as `Σ_j z_j⁻² = −(∂_z² log H_t)(0)` with their
   time evolution under the heat equation.
3. Riemann–Siegel-type asymptotics for `H_t` (proved within the paper).
4. Montgomery-type pair-correlation estimates for zeta zeros.

## Mathlib Gap Analysis

Verified by grepping the vendored Mathlib source in this worktree
(`vendor/mathlib/Mathlib`, toolchain v4.29.1).  Status legend:
✅ exists; 🟡 partial / exists in a different shape; ❌ missing.

| # | Infrastructure | Status | Mathlib anchor (verified path / name) | Needed for | Classification |
| --- | --- | --- | --- | --- | --- |
| 1 | Real-line Fourier transform, complex-valued | ✅ | `Mathlib/Analysis/Fourier/FourierTransform.lean`: `VectorFourier.fourierIntegral`, `Real.fourierIntegral`; notation `𝓕` (`Mathlib/Analysis/Fourier/Notation.lean`); derivatives `FourierTransformDeriv.lean`; inversion `Inversion.lean` | `H_t` as a (cosine) Fourier transform; heat flow on the Fourier side | done |
| 2 | Cosine transform as named API | 🟡 | no `cosFourier`; the kernel `cos(z u)` must be handled directly or via `cos w = (e^{iw}+e^{−iw})/2`; `Real.fourierChar` uses the `2π` convention, so the unscaled kernel is *not* `Real.fourierIntegral` | defining `H_t` | trivial glue |
| 3 | Schwartz functions / rapid decay | ✅ | `Mathlib/Analysis/Distribution/SchwartzSpace.lean` (+ `SchwartzSpace/Fourier.lean`, `FourierSchwartz.lean`) | regularity of `Φ` (optional; integrability suffices for `H_t`) | done |
| 4 | Holomorphicity of parametric integrals | ✅ | `Mathlib/Analysis/MellinTransform.lean`: `mellin_differentiableAt_of_isBigO_rpow`, `mellin_differentiableAt_of_isBigO_rpow_exp`; `Mathlib/Analysis/Calculus/ParametricIntegral.lean`: `hasFDerivAt_integral_of_dominated_of_fderiv_le`; Morera's theorem on disks and on `ℂ`: `Mathlib/Analysis/Complex/HasPrimitives.lean` | `H_t` entire; `∂_t`, `∂_z` differentiation under the integral | done (as templates) |
| 5 | Gaussian integrals, Fourier of Gaussian | ✅ | `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`: `integrable_exp_neg_mul_sq`; `.../Gaussian/FourierTransform.lean`: `fourierIntegral_gaussian` | heat-kernel computations | done |
| 6 | Poisson summation | ✅ | `Mathlib/Analysis/Fourier/PoissonSummation.lean`: `SchwartzMap.tsum_eq_tsum_fourier`, `Real.tsum_eq_tsum_fourier_of_rpow_decay` | `Φ` even (Riemann's FE proof) | done |
| 7 | Jacobi theta | ✅ | `Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean`: `jacobiTheta`, `differentiableAt_jacobiTheta`, `jacobiTheta_S_smul`; `TwoVariable.lean`: `jacobiTheta₂_functional_equation` | `Φ` even (Φ is a derivative combination of `θ(e^{4u})`-type terms) | done |
| 8 | Locally uniform limits of holomorphic functions (Weierstrass) | ✅ | `Mathlib/Analysis/Complex/LocallyUniformLimit.lean`: `TendstoLocallyUniformlyOn.differentiableOn`, `.deriv`, `logDeriv_tendsto` | zero continuity; threshold closedness | done |
| 9 | Hurwitz theorem (zeros of limits: limit of nonvanishing / zero-count stability) | ❌ | not found in Mathlib; only Hurwitz *zeta* hits | `t = Λ` boundary closedness; Polymath15-style perturbation | Mathlib-level gap, moderate; repo-level shortcut exists (row 10) |
| 10 | Argument principle / rectangle zero counting | ❌ in Mathlib; ✅ in-repo | repo: `MathlibAux/RectangleResidue.lean`, `MathlibAux/BoundaryRectResidue.lean`, `MathlibAux/LogDerivArgumentPrinciple.lean`, `MathlibAux/HorizontalArgument.lean`; Mathlib has Nevanlinna-style counting: `Mathlib/Analysis/Complex/ValueDistribution/` (`FirstMainTheorem.lean`, `LogCounting`) | zero counting for `H_t`; Hurwitz; de Bruijn strip theorem | repo-level gap, moderate |
| 11 | Hadamard/Weierstrass factorization, genus, canonical products | ❌ | `Mathlib/Analysis/Complex/Hadamard.lean` is only the *three-lines* theorem; no Weierstrass products, no genus | `H_t`'s order-1 product; `Σ z_j⁻²` identities; zero-dynamics ODE; Rodgers–Tao inverse-moment evolution | major Mathlib-level gap (also listed in `docs/research/rh-proof-roadmap.md` blocker table, Route C) |
| 12 | Order of an entire function / Phragmén–Lindelöf | 🟡 / ✅ | no "order" API found; `Mathlib/Analysis/Complex/PhragmenLindelof.lean` exists | growth control of `H_t` | small gap |
| 13 | Heat equation / backward heat flow / zero-dynamics ODE | ❌ | no heat-equation infrastructure (only Gaussian raw material, row 5) | Polymath15 evolution-equation view; de Bruijn ODE formalization | research-level gap |
| 14 | Laguerre–Pólya class, multiplier sequences (Pólya–Schur) | ❌ | not found | de Bruijn's original real-zero criteria | research-level gap |
| 15 | Montgomery pair correlation / local zero-spacing estimates | ❌ | not found | the final contradiction in Rodgers–Tao | research-paper-level gap (the one plausible in-repo route is the explicit-formula chain, see below) |
| 16 | `sInf` threshold housekeeping on `ℝ` | ✅ | conditionally complete linear order | defining `Λ` | done |

## Phased Plan, Effort and Risk

| Phase | Deliverable | Main missing infrastructure | Class | Rough effort | Risk |
| --- | --- | --- | --- | --- | --- |
| 0 (this stage) | Research note + Lean skeleton: `Φ` term definition, series summability (proved), `H_t` integral definition, all key statements as `def : Prop` targets | none | repo-level | days | low |
| 1a | `heat_integrand_integrable_target` discharged: absolute integrability of `e^{t u²} Φ(u) cos(z u)` on `(0,∞)` via the `|Φ(u)| ≤ K (2π² e^{9u} + 3π e^{5u}) e^{−π e^{4u}}` bound and `exp` domination | none beyond row 1–5 | repo-level | days | low |
| 1b | `H_t` even and entire (`h_even_entire_target`); backward heat equation (`backward_heat_equation_target`) | Morera/parametric templates (row 4) | repo-level | 1–2 weeks | low-medium |
| 1c | `Φ` even (`phi_even_target`) via theta/Poisson: express `Φ` through derivatives of `θ` at `e^{4u}` and use `jacobiTheta₂_functional_equation` | glue between `jacobiTheta` API and the `e^{4u}` parametrization | repo-level, real work | 2–4 weeks | medium |
| 1d | `H_0 = (1/8) Ξ(z/2)`: Mellin transform of the theta pieces against `Γ(s/2)`, identified with `completedRiemannZeta` — Riemann's 1859 computation; must fix the canonical `xiFunction` first (see `docs/research/xi-definition-audit.md`) | Mellin/theta glue; canonical xi | repo-level, hard | 1–2 months | medium-high |
| 2 | de Bruijn layer: Hurwitz (repo route via `MathlibAux`), strip theorem, monotonicity, threshold property; then `lambda_le_half_target` (`Λ ≤ 1/2`) and **`rh_iff_lambda_le_zero_target` as a proved theorem** — the logical position of RH in the Λ-scale needs no part of `Λ ≥ 0` | rows 9, 10, 12, 14 | repo-level + Mathlib-level | 2–4 months | medium-high |
| 3a | Newman `Λ > −∞` (`newman_lower_bound_target`) | growth analysis of `H_t` for `t → −∞` | research-lite | months | high |
| 3b | Rodgers–Tao `Λ ≥ 0` (`lambda_nonneg_target`) | rows 11 (Hadamard), 13 (heat/zero dynamics), 15 (pair correlation) — each a major standalone project | research-paper-level | person-years | very high |

Recommended immediate sequence after this stage: 1a → 1b → 1c → 1d, then
Phase 2.  The Phase-2 milestone "`RH ⇔ Λ ≤ 0` proved" is the natural
first *deep* theorem of this direction and is independent of the
research-level Phase 3.

## Integration With Existing Repository Assets

- `RiemannExplorer.lean`: `RiemannHypothesis.Statement`, `IsNontrivialZero`,
  `criticalLine`, and `completedZeta` with `functional_equation` — the RH
  side of `rh_iff_lambda_le_zero_target`.  The canonical-xi question is
  tracked in `docs/research/xi-definition-audit.md` (and a parallel
  worktree `xi-li-criterion` exists); the `H_0` identity in Phase 1d is a
  downstream consumer of that work, not a duplicate.
- `PrimeNumberTheorem.lean`: `rh_statement_iff_mathlib`,
  `explicit_formula_von_mangoldt`, and the moving-height explicit-formula
  modules (`PrimeNumberTheorem.ExplicitFormulaAllHeights`,
  `PrimeNumberTheorem.CofinalExplicitFormula`) — the only plausible in-repo
  substrate for any future pair-correlation input (Phase 3b).
- `HardyTheorem.lean`: `completedRiemannZeta_critical_line_real` and
  conjugation facts — useful for critical-line reality checks of `H_0`.
- `ZeroFreeRegion.lean`: the proved classical `c/log|t|` region — the
  Polymath15 strip-shrinking mechanism (Phase 3 upper-bound refinements)
  would consume this, but nothing in Phase 0–2 needs it.
- `MathlibAux/`: rectangle residues and the log-derivative argument
  principle — the substrate for the repo-level Hurwitz theorem in Phase 2.
- `PrimeNumberTheorem.SincSquareFourier`, `FourierL1L2`,
  `PositiveFourierKernel` etc.: precedent for measure-theoretic Fourier
  work in this repository's style.

## What This Note Does Not Claim

- No part of `Λ ≥ 0`, `Λ ≤ 1/2`, or RH is proved here.  All deep
  statements appear in the Lean skeleton only as `def ... : Prop` targets,
  per `docs/implementation-standards.md`.
- The numerical bounds in the fact-chain table are literature anchors, not
  formalized content.
- The new Prop targets are deliberately **not** registered in
  `docs/missing-chains-index.md` (which tracks the four maintained target
  chains); on merge they should be registered as a separate
  research-direction category rather than folded into the existing count.

## References

- N. G. de Bruijn, *The roots of trigonometric integrals*, Duke Math. J. 17
  (1950), 197–226.
- C. M. Newman, *Fourier transforms with only real zeros*, Proc. Amer.
  Math. Soc. 61 (1976), 245–251.
- G. Csordas, T. S. Norfolk, R. S. Varga, *A lower bound for the de
  Bruijn–Newman constant Λ*, Numer. Math. 52 (1988), 483–497.
- H. J. J. te Riele, *A new lower bound for the de Bruijn–Newman constant*,
  Numer. Math. 58 (1991), 661–667.
- G. Csordas, W. Smith, R. S. Varga, *Lehmer pairs of zeros, the de
  Bruijn–Newman constant Λ, and the Riemann hypothesis*, Constr. Approx. 10
  (1994), 107–129.
- A. M. Odlyzko, *An improved bound for the de Bruijn–Newman constant*,
  Numer. Algorithms 25 (2000), 293–303.
- Y. Saouter, X. Gourdon, P. Demichel, *An improved lower bound for the de
  Bruijn–Newman constant*, Math. Comp. 80 (2011), 2281–2287.
- H. Ki, Y.-O. Kim, J. Lee, *On the de Bruijn–Newman constant*, Adv. Math.
  222 (2009), 281–306.
- D.H.J. Polymath, *Effective approximation of heat flow evolution of the
  Riemann ξ function, and a new upper bound for the de Bruijn–Newman
  constant*, Res. Math. Sci. 6 (2019), Art. 31; arXiv:1904.12438.
- B. Rodgers, T. Tao, *The de Bruijn–Newman constant is non-negative*,
  arXiv:1801.05914 (2018); Forum Math. Pi 8 (2020), e6.
