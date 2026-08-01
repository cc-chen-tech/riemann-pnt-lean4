# Sharp low-height energy boundary

## Unconditional milestone

For a genuine positive-ordinate zeta zero `rho` with

```text
2 / 3 < rho.re < 1,
```

the branch proves a cofinal positive Gaussian energy lower bound for the
actual finite-zero complement with `S = empty`.  The detector and outer
heights are independent:

```text
Tlow in [exp (gammaLow * log Y), exp (gammaLow * log Y) + 1],
Tlow <= exp (alpha * log Y),
gammaLow < alpha.
```

The normalized remainder estimate uses the exact conditions

```text
(1 - rho.re) * (1 + epsilon) < gammaLow < rho.re.
```

The lower-bound constant is
`initialEmptyClusterFullMovingGaussianL2Constant epsilon rho k`; it is fixed
before `Y` and therefore does not decay along the cofinal sequence.

## Joint two-height parameter compatibility

The existing theorem `exists_jointTwoHeightTargetAmplitudeParameters` should
remain the canonical numerical selector for the eventual two-height argument.
It gives

```text
gammaLow = alpha / 2,
1 - beta < alpha,
gammaLow + sigma - beta + epsilonLow < 0,
alpha + sigma - beta - gammaLow + epsilonLow < 0.
```

Those are the correct low/high zero-tail margins.  They do not by themselves
imply

```text
(1 - beta) * (1 + epsilon) < gammaLow,
```

which is the stronger condition used by the direct low-height explicit-formula
remainder theorem in this branch.  Therefore the final joint-parameter
corollary must not identify the two arguments.  It must use the outer good
height `H = x ^ alpha`, then show that the genuine zero tail between
`x ^ gammaLow` and `H` is negligible by the already proved two-height mass
estimates.  This branch does not reprove the numerical feasibility theorem.

## Why this does not yet iterate over finite recorded sets

The requested directed complement is formed with

```text
rightHigherExclusionSet S Told sigma Tlow.
```

Once `Told >= rho.im`, this set contains both the original anchor zero and its
conjugate.  The existing Sharp lower bound may be carried entirely by that
pair.  Moreover, the verified blocker theorem states that if every zero up to
`Tlow` is already in `S`, below `Told`, or has real part at most `sigma`, then
the directed complement energy is exactly zero.

Consequently, an unconditional positive lower bound for every finite `S` and
every old height would already prove that one off-line zero forces new zeta
zeros of real part greater than `sigma` at arbitrarily large ordinates.  This
is not a formal transfer consequence of the current anchor theorem.

This implication is itself a major open boundary.  The standard question
"if RH fails, must it fail infinitely often?" is not known; the explicit
formula is consistent with finitely many exceptional zero pairs contributing
finite secondary oscillatory terms.  Bombieri's analysis of Weil's quadratic
functional explicitly studies the hypothetical finite-exception case rather
than excluding it:

- <https://mathoverflow.net/questions/50186/if-the-riemann-hypothesis-fails-must-it-fail-infinitely-often>
- <https://www.bdim.eu/item?id=RLIN_2000_9_11_3_183_0>

Therefore no smoothing, higher-order kernel, or q-power annihilator can by
itself guarantee the requested positive complement energy after `S` contains
all off-line exceptions.  Such a theorem must contain the new mathematical
argument that rules out a finite exceptional set; better contour decay only
becomes relevant after that response mechanism exists.

## Minimum new genuine-zeta analytic input

The next Sharp theorem must be a response-minus-loss estimate, not an abstract
coefficient interface.  A sufficient numerical endpoint has the following
shape.  Here `H x = x ^ alpha` is the outer contour height and
`Ylow x = x ^ gammaLow` is the detector height.

```lean
theorem exists_cofinally_rightHigher_trueZeta_energy_ge
    {rho0 : Complex} {beta sigma alpha gammaLow epsilon : Real}
    (hzero : riemannZeta rho0 = 0)
    (hbeta : beta = rho0.re)
    (hbeta23 : 2 / 3 < beta)
    (hsigma : 1 / 2 < sigma ∧ sigma < beta)
    (hheights : 0 < gammaLow ∧ gammaLow < alpha ∧ alpha ≤ 1)
    (hwindow : (1 - beta) * (1 + epsilon) < gammaLow) :
    ∀ (S : Finset Complex) (Told : Real),
      ∃ eta : Real, 0 < eta ∧
        ∀ X : Real, ∃ x : Real, X ≤ x ∧
          ∃ Tlow ∈ Set.Icc (x ^ gammaLow) (x ^ gammaLow + 1),
            Tlow ≤ x ^ alpha ∧
            eta ≤
              ∫ t in Set.Icc 0 (epsilon * Real.log x),
                normalizedGaussian ((epsilon * Real.log x) ^ 2) t *
                  ‖normalizedFiniteZeroClusterComplementContribution
                      (rightHigherExclusionSet S Told sigma Tlow)
                      Tlow beta (Real.log x + t)‖ ^ 2
```

This signature is documentation only.  It is deliberately not introduced as
a `Prop`, axiom, class, or conditional theorem.

The q-power detector branch supplies exact pole cancellation and coefficient
mass identities, but not yet the needed true-zeta prime response.  The missing
strict inequality must retain a target response after old poles are cancelled
and dominate all of:

```text
prime-side negative coefficient loss,
other zero residues,
trivial-zero and pole terms,
horizontal and left-edge contour integrals,
outer-height truncation error.
```

If the ordinary Perron kernel cannot make that margin positive, the next
admissible route is a smoothed or higher-order Mellin kernel.  Its minimum tail
theorem must bound the complete contour remainder uniformly for
`Tlow = x ^ gammaLow` while the contour itself is truncated at
`H = x ^ alpha`.  Merely renaming the two heights or reusing the non-local
`pi / 2` oscillation theorem does not provide repeatable `S`-relative energy.

No Carlson contradiction, zero-density violation, or RH conclusion is proved
here.
