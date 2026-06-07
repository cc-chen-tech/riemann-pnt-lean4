# Hardy Theorem Chain

This note records the remaining chain from the verified Hardy Z-function setup
in `HardyTheorem.lean` to Hardy's theorem.  It is a planning artifact only:
the `*_target` declarations in Lean are not proved theorems.

## Verified Lean Starting Point

`HardyTheorem.lean` already proves the useful algebraic and topological
infrastructure:

- `thetaPhase` and `hardyZ` are defined on the critical line.
- `completedRiemannZeta_conj_eq_of_one_lt_re` and
  `completedRiemannZeta₀_conj_eq` give conjugation compatibility.
- `completedRiemannZeta_critical_line_real` shows the completed zeta function
  is real on `s = 1/2 + it`.
- `Gammaℝ_re_im_arg` connects `thetaPhase` to the argument of the completed
  gamma factor.
- `hardyZ_zero_iff_zeta_zero` proves pointwise equivalence between zeros of
  `hardyZ` and zeros of `riemannZeta (1/2 + it)`.
- `hardyZ_continuous` gives the continuity needed for intermediate-value
  sign-change arguments.
- `hardyZ_eventually_const_sign_of_finite_zeros` proves that finitely many
  zeros force `hardyZ` to be eventually positive or eventually negative.
- `weightedIntegralOf_neg` proves the basic sign relation for negating the
  integrand.

These results are enough for the elementary end of Hardy's argument, but they
do not supply the analytic asymptotics.

## Current Target Audit

### Final theorem target

Current Lean target:

```lean
def hardy_theorem_target : Prop :=
    {t : ℝ | riemannZeta (0.5 + I * t) = 0}.Infinite
```

This statement is mathematically true, but it is weaker than the usual Hardy
theorem formulation used by the analytic proof.  Hardy proves zeros with
arbitrarily large positive ordinates, not merely an infinite subset of `ℝ`.
In a purely topological setting, an infinite zero set could still be bounded.
Analytic discreteness rules this out for zeta, but that is a separate theorem
and should not be hidden inside the Hardy chain.

Better final target:

```lean
def hardy_zeros_unbounded_target : Prop :=
    ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧ riemannZeta ((1 / 2 : ℂ) + I * t) = 0
```

Optional positive-ordinate version:

```lean
def hardy_positive_zeros_unbounded_target : Prop :=
    ∀ T : ℝ, ∃ t : ℝ, max T 0 ≤ t ∧
      riemannZeta ((1 / 2 : ℂ) + I * t) = 0
```

The existing `hardy_theorem_target` should become a corollary of this stronger
unbounded target, not the main target.

### Moment asymptotic target

Current Lean target:

```lean
def integral_asymptotic_target (n : ℕ) : Prop :=
    n ≥ 1 ∧ ∃ C : ℝ, C ≠ 0 ∧
      (fun T => weightedIntegral n T) ~[atTop]
        (fun T => C * T ^ (2*n + 1/4))
```

This is an improvement over quantifying over an arbitrary constant, but it is
still too weak for the sign-change proof.  The contradiction needs a known
sign for the leading constant.  If `hardyZ` is eventually positive, all large
weighted integrals with nonnegative weights should be positive; if `hardyZ` is
eventually negative, they should be negative.  A nonzero but sign-unknown
constant cannot contradict either eventual sign.

Corrected moment theorem shape:

```lean
def hardy_weighted_moment_signed_target (n : ℕ) : Prop :=
    1 ≤ n ∧ ∃ A : ℝ, 0 < A ∧
      (fun T => weightedIntegral n T) ~[atTop]
        (fun T => ((-1 : ℝ) ^ n * A) * T ^ ((2 * n : ℝ) + 1 / 4))
```

This form lets the proof use `n = 1` for a negative asymptotic and `n = 2` for
a positive asymptotic.  A leaner first milestone can avoid exact constants:

```lean
def hardy_two_signed_moments_target : Prop :=
    (∃ A : ℝ, 0 < A ∧
      (fun T => weightedIntegral 1 T) ~[atTop]
        (fun T => -A * T ^ ((2 : ℝ) + 1 / 4))) ∧
    (∃ B : ℝ, 0 < B ∧
      (fun T => weightedIntegral 2 T) ~[atTop]
        (fun T => B * T ^ ((4 : ℝ) + 1 / 4)))
```

For Lean, the two-moment version is likely the best first target: it avoids
formalizing a parameterized family of constants before the sign-change chain
is working.

### Positivity of weighted integrals

The current `weightedIntegralOf_eventually_positive_target` correctly records
that eventual positivity of an integrand is not enough by itself; a bounded
initial negative contribution can dominate an integrable positive tail.  The
right generic lemma needs a tail-divergence or tail-dominance hypothesis.

Recommended generic target:

```lean
def weightedIntegralOf_eventually_positive_from_tail_target
    (f : ℝ → ℝ) (n : ℕ) : Prop :=
    (∀ᶠ t in atTop, f t > 0) →
    (∃ A : ℝ, Tendsto
      (fun T => ∫ t in A..T, weightFunction n t * f t) atTop atTop) →
    ∀ᶠ T in atTop, weightedIntegralOf f n T > 0
```

The negative version should be derived with `weightedIntegralOf_neg` rather
than reproved.

### Approximate functional equation target

Current Lean target:

```lean
def approximate_functional_equation_target : Prop :=
    ∃ C > 0, ∀ t : ℝ, t > 1 → ∃ R : ℂ,
      riemannZeta (0.5 + I * t) =
        ∑ n ∈ Finset.range (Nat.floor (Real.sqrt (t / (2*Real.pi)))),
          1/((n+1 : ℂ) ^ (0.5 + I*t))
        + Complex.exp (I * thetaPhase t) *
          ∑ n ∈ Finset.range (Nat.floor (Real.sqrt (t / (2*Real.pi)))),
            1/((n+1 : ℂ) ^ (0.5 - I*t))
        + R ∧ ‖R‖ ≤ C * t^(-1/4 : ℝ)
```

This is not yet a safe target.  The phase in the second sum should be the
functional-equation factor on the critical line, usually expressible as
`exp (-2 * I * theta t)` after choosing an unwrapped Riemann-Siegel theta
function satisfying `Z(t) = exp (I * theta t) * zeta(1/2 + it)`.  The current
`exp (I * thetaPhase t)` factor is not the standard zeta approximate functional
equation factor and is likely phase-inconsistent.

The target should also avoid principal-branch `thetaPhase` in statements that
need continuous asymptotics.  Use a new unwrapped `theta : ℝ → ℝ` and state the
phase relation separately.

Recommended zeta-level target:

```lean
def zeta_critical_afe_target : Prop :=
    ∃ theta : ℝ → ℝ, ∃ C > 0,
      (∀ t : ℝ, Complex.exp (I * theta t) =
        Complex.exp (I * thetaPhase t)) ∧
      ∀ᶠ t in atTop, ∃ R : ℂ,
        riemannZeta ((1 / 2 : ℂ) + I * t) =
          (∑ n ∈ Finset.range (Nat.floor (Real.sqrt (t / (2 * Real.pi)))),
            1 / ((n + 1 : ℂ) ^ ((1 / 2 : ℂ) + I * t))) +
          Complex.exp (-2 * I * theta t) *
            (∑ n ∈ Finset.range (Nat.floor (Real.sqrt (t / (2 * Real.pi)))),
              1 / ((n + 1 : ℂ) ^ ((1 / 2 : ℂ) - I * t))) +
          R ∧ ‖R‖ ≤ C * t ^ (-1 / 4 : ℝ)
```

For the moment theorem, a more direct `Z`-level target is better:

```lean
def hardyZ_riemann_siegel_afe_target : Prop :=
    ∃ theta : ℝ → ℝ, ∃ C > 0,
      (∀ t : ℝ, Complex.exp (I * theta t) =
        Complex.exp (I * thetaPhase t)) ∧
      ∀ᶠ t in atTop, ∃ R : ℝ,
        hardyZ t =
          2 * (∑ n ∈ Finset.range
            (Nat.floor (Real.sqrt (t / (2 * Real.pi)))),
            (1 / Real.sqrt (n + 1)) *
              Real.cos (theta t - t * Real.log (n + 1))) +
          R ∧ |R| ≤ C * t ^ (-1 / 4 : ℝ)
```

This is closer to the eventual stationary-phase proof of the signed moments.

### Special function asymptotics

Current Lean target:

```lean
def gamma_asymptotic_half_plus_it_target : Prop :=
    (fun (t : ℝ) => Complex.Gamma (0.5 + I * t)) ~[atTop]
      (fun (t : ℝ) => Real.sqrt (2*Real.pi) *
        Complex.exp (I * t * Real.log t - I * t) *
        Complex.exp (-Real.pi * t / 2))
```

This is plausible for the special case `Γ(1/2 + it)`, but it is not the main
asymptotic needed by this file.  The local theta definition uses
`Γ(1/4 + i t/2)` and the completed factor
`Gammaℝ (1/2 + it) = π^(-(1/2+it)/2) Γ(1/4+it/2)`.

Recommended first targets:

```lean
def gamma_quarter_vertical_stirling_target : Prop :=
    (fun t : ℝ => Complex.Gamma ((1 / 4 : ℂ) + I * t / 2)) ~[atTop]
      (fun t : ℝ =>
        Real.sqrt (2 * Real.pi) *
          (t / 2) ^ (-1 / 4 : ℝ) *
          Complex.exp (-(Real.pi * t / 4 : ℝ)) *
          Complex.exp
            (I * ((t / 2) * Real.log (t / 2) - t / 2 - Real.pi / 8)))

def riemann_siegel_theta_asymptotic_target : Prop :=
    ∃ theta : ℝ → ℝ,
      (∀ t : ℝ, Complex.exp (I * theta t) =
        Complex.exp (I * thetaPhase t)) ∧
      (fun t : ℝ => theta t) ~[atTop]
        (fun t : ℝ =>
          (t / 2) * Real.log (t / (2 * Real.pi)) - t / 2 - Real.pi / 8)
```

The second statement is already close to `theta_asymptotic_target` and should
be kept; the important Lean design point is that later statements should use
the unwrapped `theta`, not the principal-branch `thetaPhase`.

## Minimal Dependency Chain

The shortest credible chain to `hardy_zeros_unbounded_target` is now:

1. Use finite-zero sign control.
   This is formalized as:

   ```lean
   lemma hardyZ_eventually_const_sign_of_finite_zeros
       (h : {t : ℝ | hardyZ t = 0}.Finite) :
       (∀ᶠ t in atTop, hardyZ t > 0) ∨
       (∀ᶠ t in atTop, hardyZ t < 0)
   ```

2. Use the signed-moment asymptotics directly.
   If `hardyZ` is eventually positive, the `n = 1` weighted integral is
   eventually bounded below, contradicting its `atBot` limit.  If `hardyZ`
   is eventually negative, the `n = 2` weighted integral is eventually bounded
   above, contradicting its `atTop` limit.  This bridge is now formalized as:

   ```lean
   lemma hardy_theorem_target_of_two_signed_moments :
       hardy_two_signed_moments_target → hardy_theorem_target
   ```

   The current compatibility target also has a direct checked bridge:

   ```lean
   lemma hardy_theorem_target_of_integral_asymptotic_one_two :
       integral_asymptotic_target 1 →
       integral_asymptotic_target 2 →
       hardy_theorem_target
   ```

   With bounded-strip finiteness for critical-line zeros, the same two
   signed-moment target, and therefore the same two asymptotic targets, now
   also yield both unbounded-height interfaces:

   ```lean
   lemma hardy_zeros_abs_unbounded_of_two_signed_moments_of_bounded_strips :
       (∀ B, {t | |t| ≤ B ∧ riemannZeta (0.5 + I * t) = 0}.Finite) →
       hardy_two_signed_moments_target →
       hardy_zeros_abs_unbounded_target

   lemma hardy_zeros_unbounded_of_two_signed_moments_of_bounded_strips :
       (∀ B, {t | |t| ≤ B ∧ riemannZeta (0.5 + I * t) = 0}.Finite) →
       hardy_two_signed_moments_target →
       hardy_zeros_unbounded_target

   lemma hardy_zeros_abs_unbounded_of_integral_asymptotic_one_two_of_bounded_strips :
       (∀ B, {t | |t| ≤ B ∧ riemannZeta (0.5 + I * t) = 0}.Finite) →
       integral_asymptotic_target 1 →
       integral_asymptotic_target 2 →
       hardy_zeros_abs_unbounded_target

   lemma hardy_zeros_unbounded_of_integral_asymptotic_one_two_of_bounded_strips :
       (∀ B, {t | |t| ≤ B ∧ riemannZeta (0.5 + I * t) = 0}.Finite) →
       integral_asymptotic_target 1 →
       integral_asymptotic_target 2 →
       hardy_zeros_unbounded_target
   ```

3. Prove two signed moments.
   It is enough to establish one negative moment and one positive moment:
   `weightedIntegral 1` has negative leading term and `weightedIntegral 2`
   has positive leading term.  This avoids parameterized constants at first.

4. Convert to zeta zeros.
   Use the pointwise equivalence to transfer unbounded Hardy-Z zeros to
   unbounded critical-line zeta zeros, then derive the existing
   `hardy_theorem_target` as a corollary.

## Suggested Lean Milestones

### Phase 1: elementary, no deep analysis

- Add a set-extensional corollary of `hardyZ_zero_iff_zeta_zero`.
- Add `hardyZ_eventually_const_sign_of_bounded_zeros`.
- Add generic asymptotic-sign lemmas:
  if `f ~[atTop] g`, `g` is eventually positive, then `f` is eventually
  positive; likewise for negative.
- Add the bounded-below / bounded-above weighted-integral lemmas used by
  `hardy_theorem_target_of_two_signed_moments`.

These should not require special-function asymptotics or approximate
functional equations.

### Phase 2: corrected analytic targets

- Introduce an unwrapped Riemann-Siegel theta target.
- Replace `approximate_functional_equation_target` with either the corrected
  zeta-level phase `exp (-2 * I * theta t)` or the direct `hardyZ`-level
  Riemann-Siegel formula.
- Replace `integral_asymptotic_target` with `hardy_two_signed_moments_target`
  or `hardy_weighted_moment_signed_target`.

### Phase 3: deep analysis

- Formalize Stirling asymptotics in the vertical strip needed for
  `Γ(1/4 + it/2)`.
- Prove the Riemann-Siegel/approximate functional equation with a usable
  uniform remainder.
- Prove the signed moment estimates by integrating the Riemann-Siegel
  expression and bounding the remainder.

## Immediate Small Lemma Opportunity

Without touching deep analytic estimates, the most useful immediate Lean lemma
is the bounded-zero version of the existing finite-zero sign lemma:

```lean
lemma hardyZ_eventually_const_sign_of_bounded_zeros
    (h : Bornology.IsBounded {t : ℝ | hardyZ t = 0}) :
    (∀ᶠ t in atTop, hardyZ t > 0) ∨
    (∀ᶠ t in atTop, hardyZ t < 0)
```

The proof should be a near-copy of
`hardyZ_eventually_const_sign_of_finite_zeros`, starting from `h` instead of
`Set.Finite.isBounded h`.  This is small, local, and does not depend on
Stirling, approximate functional equations, or moment estimates.

Do not add it in this task because the current file boundary forbids editing
Lean source.
