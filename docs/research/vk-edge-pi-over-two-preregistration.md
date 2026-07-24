# VK-edge finite-spectrum gap: preregistration

## Status and boundary

This document preregisters a mathematical research question. It does not state
a proved zeta theorem, add a Lean target, or claim an improvement over the
classical `pi / 2` oscillation constant.

The branch has one hard gate:

```text
For each fixed M, does a uniform delta_M > 0 exist such that every admissible
real exponential polynomial with at most M positive frequencies and a
distinguished Fourier coefficient 1 has sup norm at least pi / 2 + delta_M?
```

If the answer is no for any fixed `M`, the `pi / 2` breakthrough goal stops on
this branch. A shorter-interval theorem is a different research project.

## Exact finite-spectrum class

Fix an integer `M >= 1`. An admissible polynomial is

```text
F(y) = 2 Re(sum_{j=0}^{r-1} a_j exp(i lambda_j y)),
```

subject to all of the following conditions:

1. `1 <= r <= M`.
2. `lambda_j > 0` for every `j`.
3. Frequencies are pairwise distinct after exact equal-frequency terms have
   been combined.
4. The distinguished frequency is normalized by

   ```text
   lambda_0 = 1,  a_0 = 1.
   ```

   A nonzero distinguished coefficient and frequency can be put in this form
   by dividing the polynomial by the coefficient modulus, translating `y` to
   remove its phase, and rescaling `y`.
5. The negative-frequency coefficients are the complex conjugates of the
   displayed positive-frequency coefficients. Thus `F` is real-valued.
6. There is no zero-frequency term.

Near collisions `lambda_j -> lambda_k`, rational relations between the
frequencies, and unbounded frequencies are allowed. Exact collisions must be
combined before normalization. In particular, an additional coefficient at
the distinguished frequency is not allowed to cancel `a_0`; its contribution
must first be included in the combined distinguished coefficient.

Define

```text
kappa_M =
  inf { sup_{y in R} |F(y)| : F is admissible with at most M frequencies }.
```

The candidate gap is

```text
delta_M = kappa_M - pi / 2.
```

The research target is `delta_M > 0` for every fixed `M`.

## Baseline coefficient inequality

Let `K` be the compact closure of the frequency flow in a torus, and let
`chi_0` be the distinguished character. Haar measure pushes forward under
`chi_0` to normalized measure on the circle. For a real bounded function `F`
with distinguished Fourier coefficient `1`,

```text
1
  = integral_K F conjugate(chi_0)
  = integral_K F Re(chi_0)
  <= ||F||_infinity integral_K |Re(chi_0)|
  = (2 / pi) ||F||_infinity.
```

Therefore every admissible polynomial satisfies

```text
||F||_infinity >= pi / 2.
```

This argument proves only the non-strict baseline. Equality in the integral
inequality would force

```text
F / ||F||_infinity = sign(Re(chi_0))
```

almost everywhere. That equality profile has infinitely many odd harmonics
on the distinguished circle. This rules out equality for each individual
finite polynomial, but it does not yet prove a uniform positive gap over all
frequency configurations with at most `M` terms. The missing uniformity is
the central mathematical problem.

## Mandatory falsification families

Before attempting a compactness proof, the experiment must test:

1. `M = 1`, where the exact norm is `2`.
2. One additional rationally dependent frequency.
3. One additional irrational frequency.
4. Near collisions with the distinguished frequency.
5. Near collisions between nondistinguished frequencies.
6. Large integer frequencies.
7. Truncated Fourier series of `(pi / 2) sign(cos y)`, normalized so the
   distinguished coefficient equals `1`.
8. Deterministic random coefficient and frequency families.

The experiment samples a finite interval and therefore returns a lower
estimate for the true sup norm. It may find a candidate counterexample to a
proposed quantitative gap, but it cannot prove `kappa_M > pi / 2`, cannot
prove a global sup norm, and cannot certify a counterexample at the exact
threshold without a subsequent rigorous error bound.

The general search uses the Python standard library. The periodic rational
scan additionally requires NumPy. Both scripts use deterministic defaults and
write their parameters into the JSON output.

## Proof gates

### Gate F0: fixed-configuration strictness

Prove that each admissible finite polynomial has norm strictly larger than
`pi / 2`, using the equality case of the coefficient inequality.

### Gate F1: uniformity for fixed M

Prove or refute

```text
kappa_M > pi / 2.
```

A valid proof must control degenerating frequency configurations. Merely
showing pointwise strictness is insufficient. Candidate proof mechanisms are:

1. compactness on frequency-flow closures plus rigidity of the equality case;
2. a finite-dimensional dual certificate with a gap depending only on `M`;
3. a quantitative lower bound for approximation of `sign(cos)` by at most
   `M` characters.

### Gate Z0: Bellotti mapping

Only after Gate F1 succeeds, map Bellotti's

```text
N(sigma, T) = O_A(1)
```

at the Vinogradov--Korobov edge to a bound `M_B` on the relevant
multiplicity-counted positive-frequency package. Verify that combining equal
ordinates preserves a nonzero distinguished coefficient.

### Gate Z1: analytic transfer

Prove, without a route assumption, that the finite maximal-real-part package
dominates:

1. lower-real-part local zeros;
2. remote zeros;
3. the moving-height explicit-formula truncation error;
4. the closed terms and the `psi_0` to `psi` endpoint correction.

The localization exponent may depend on `A`, but not on the target height
`gamma_0`. The starting point may depend on the actual zero configuration.

## Candidate zeta theorem

The eventual candidate, not a current result, is:

```text
Fix A > A_0. There exist Gamma_A, C_A and delta_A > 0 such that:

if rho_0 = beta_0 + i gamma_0 is a Riemann-zeta zero,
gamma_0 >= Gamma_A, and
beta_0 >= 1 - A g(gamma_0),

then for every epsilon with 0 < epsilon < delta_A there is
Y_0 = Y_0(rho_0, epsilon) such that every Y >= Y_0 admits
x in [Y, Y ^ C_A] with

  |psi(x) - x|
    >= (pi / 2 + delta_A - epsilon)
         x ^ beta_0 / |rho_0|.
```

Here

```text
g(t) = (log t)^(-2/3) (log log t)^(-1/3).
```

The proposed relation is `delta_A = delta_(M_(A+2))`. This relation is
meaningful only after Gates F1 and Z0 are proved.

## Success and stop rules

The branch succeeds mathematically only if:

1. `delta_M > 0` is proved for the required fixed finite count;
2. the Bellotti count is mapped to the exact zeta package;
3. every analytic remainder in Gate Z1 is quantitatively closed.

Numerical evidence, a Lean interface, pointwise strictness for each fixed
polynomial, or recovery of `pi / 2 - epsilon` is not success.

The branch stops if a rigorous family gives `kappa_M = pi / 2` for some fixed
`M`, or an admissible exact counterexample reaches the baseline. The
counterexample and its proof should be recorded, but the theorem statement
must not be silently weakened.

## Prior-art checks

The minimum comparison set is:

- S. Gy. Revesz, *Oscillation of the remainder term in the prime number
  theorem of Beurling, caused by a given zeta-zero*, arXiv:2202.01837.
- C. Bellotti, *A new zero-density estimate for the Riemann zeta function and
  the error term in the Prime Number Theorem*, arXiv:2508.02041.
- S. Neuwirth, *On the (Fourier analytic) Sidon constant of {0,1,2,3}*,
  arXiv:2603.28229.

Any positive result must receive a separate historical search for finite
character extremal inequalities and an independent expert proof review before
being described as new mathematics.
