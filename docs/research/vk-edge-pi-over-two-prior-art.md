# VK-edge `pi / 2` project: prior-art audit

## Audit conclusion

The search did not find a primary source stating the exact
cardinality-bounded theorem from
`vk-edge-pi-over-two-proof-record.md`:

```text
For every fixed M, a real exponential polynomial with at most M positive
frequencies and a distinguished positive-frequency coefficient 1 has norm
at least pi/2 + delta_M, with delta_M > 0 depending only on M.
```

It also did not find a classical-zeta theorem deriving a constant strictly
above `pi/2` from Bellotti's bounded count of Vinogradov--Korobov-edge zeros.

These negative search results are not priority proofs. The abstract theorem
has high rediscovery risk because its proof uses classical Fourier duality,
and the exact `kappa_2=sqrt(3)` calculation is close to old Chebyshev and
trinomial extremal problems.

The zeta application has lower collision risk but much higher proof risk. It
remains unproved.

## Closest prescribed-coefficient result

Ash and Ganzburg study the least uniform norm of a real trigonometric
polynomial with a prescribed real coefficient. Their degree-bounded constants
approach the `sign(cos)` extremizer and, after converting their cosine
coefficient normalization to a positive complex Fourier coefficient, the
limiting constant is `pi/2`.

Reference:

- J. M. Ash and M. I. Ganzburg, *A sharp estimate for trigonometric
  polynomials with a given coefficient*, Proceedings of the AMS 127 (1999).
  <https://doi.org/10.1090/S0002-9939-99-04481-0>

Their parameter is maximum degree, not the number of occupied frequencies.
The result therefore explains the limiting `pi/2` constant but does not
directly provide the fixed-cardinality gap proved on this branch.

Ivanshin characterizes minimum-`L-infinity` extensions with prescribed
initial Fourier data by constant-modulus, finitely jumping functions. This
supports `sign(cos)` as the equality profile in the unrestricted bounded
class.

Reference:

- P. N. Ivanshin, *Minimum Norm Extension of a Finite Sequence in Fourier
  Analysis*, Mathematics 7 (2019), 651.
  <https://doi.org/10.3390/math7070651>

## Finite spectra and Sidon constants

Revesz constructs finite odd-harmonic polynomials with norm at most
`pi/2+epsilon`, where the required number of frequencies grows as epsilon
shrinks. This is consistent with both facts proved here:

```text
kappa_M > pi/2 for each fixed M,
kappa_M -> pi/2 as M -> infinity.
```

Reference:

- S. Gy. Revesz, *Oscillation of the remainder term in the prime number
  theorem of Beurling, caused by a given zeta-zero*, Lemma 9.
  <https://arxiv.org/abs/2202.01837>

Neuwirth computes exact Sidon constants for three-element integer frequency
sets. Sidon constants optimize the ratio of the coefficient `l1` norm to the
polynomial sup norm, so they do not directly equal the real-symmetric
prescribed-one-coefficient constant used here. They show that nearby small
finite-spectrum extremal problems are classical and depend sensitively on
arithmetic relations among frequencies.

References:

- S. Neuwirth, *The Sidon constant of sets with three elements*.
  <https://arxiv.org/abs/math/0102145>
- S. Neuwirth, *The maximum modulus of a trigonometric trinomial*.
  <https://doi.org/10.1007/s11854-008-0028-2>
- S. Neuwirth, *On the (Fourier analytic) Sidon constant of {0,1,2,3}*.
  <https://arxiv.org/abs/2603.28229>

The last manuscript reports that even the adjacent four-element complex
Sidon problem remains delicate.

## Oscillation constant and zeta literature

Revesz's earlier classical theorem and later Beurling theorem establish the
`pi/2-epsilon` given-zero oscillation constant. The Beurling work also
constructs systems for which `pi/2` is sharp up to epsilon. Therefore a
constant above `pi/2` cannot hold uniformly for general Beurling zeta
functions.

References:

- S. Gy. Revesz, *Effective oscillation theorems for a general class of
  real-valued remainder terms*, Acta Arithmetica 49 (1988), 481--505.
  <https://doi.org/10.4064/aa-49-5-481-505>
- S. Gy. Revesz, *Oscillation of the remainder term in the prime number
  theorem of Beurling, caused by a given zeta-zero*, IMRN (2023).
  <https://doi.org/10.1093/imrn/rnac274>

Bellotti proves

```text
N(sigma,T) = O_A(1)
```

in a fixed region near the Vinogradov--Korobov boundary. This is a
multiplicity-counted zero-density statement, not a finite-package explicit
formula and not an oscillation theorem.

Reference:

- C. Bellotti, *A new zero-density estimate for the Riemann zeta function and
  the error term in the Prime Number Theorem*, Theorem 1.2.
  <https://arxiv.org/abs/2508.02041>

## Claim policy

The following wording is currently acceptable:

```text
We proved a cardinality-dependent Fourier gap above pi/2 and the exact
two-frequency value kappa_2=sqrt(3). A targeted search found no identical
statement, but historical priority remains unverified.
```

The following wording is not acceptable:

```text
We proved a new zeta oscillation theorem above pi/2.
```

Before claiming novelty for the abstract theorem, obtain a specialist search
covering Taikov-type coefficient inequalities, Chebyshev systems,
trigonometric minimax problems, idempotent measures, and sparse Sidon
constants.

Before claiming new analytic-number-theory progress, close the envelope-local
or multiphase-transform bridge in
`vk-edge-pi-over-two-zeta-bridge.md`.
