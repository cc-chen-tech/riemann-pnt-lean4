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

The global absolute-`limsup` zeta application is proved in
`vk-edge-pi-over-two-abel-transfer.md`, modulo Bellotti's stated theorem. The
stronger power-interval localization remains unproved. Both have lower
collision risk than the abstract Fourier lemma but require a direct
specialist prior-art check.

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

## Ingham and Anderson--Stark comparison

Anderson and Stark develop a general Mellin oscillation theorem using weak
independence of selected zero ordinates. In one standard formulation, a
selected set `Gamma_0` must admit no bounded integer relation, and no bounded
integer combination of `Gamma_0` may equal another zero ordinate below the
truncation height. This produces explicit lower and upper oscillation
constants.

Reference:

- R. J. Anderson and H. M. Stark, *Oscillation theorems*, in *Analytic
  Number Theory*, Lecture Notes in Mathematics 899, pp. 79--106.
  <https://doi.org/10.1007/BFb0096454>

The Abel argument on this branch belongs to that classical Mellin-oscillation
framework, but its spectral hypothesis is different and weaker in one
specific direction. It requires only:

```text
one missing odd multiple n gamma_0,
with n <= 2M+1,
on the boundary line Re(s)=beta_0.
```

It does not require the full bounded-relation independence used by
Anderson--Stark. Bellotti's bounded VK-edge count supplies this missing odd
multiple uniformly. No source found in the targeted search states this exact
combination, but older variants of coefficient-kernel oscillation theorems
remain a serious priority risk.

Revesz already identifies the underlying obstruction in the discussion
around his finite-sum lemma: suppressing the distinguished pair down to
`pi/2` would require an odd-harmonic zero pattern comparable to the Fourier
series of `sign`, while sufficiently sparse zeros force a finite-sum
overshoot. He also records finite sine polynomials with norm at most
`pi/2+epsilon`. Therefore neither the qualitative finite-spectrum overshoot
mechanism nor the possibility of approaching `pi/2` with an increasing
number of terms can be claimed as new here.

What is not stated in that discussion, and is the only plausible new
analytic-number-theory contribution on this branch, is the uniform
combination

```text
Bellotti O_A(1) VK-edge count
  -> one missing bounded odd multiple
  -> an explicit fixed-cardinality gap
  -> a strict zeta/PNT global limsup constant above pi/2.
```

This distinction must remain in any later claim of novelty.

## Claim policy

The following wording is currently acceptable for the abstract result:

```text
We proved a cardinality-dependent Fourier gap above pi/2 and the exact
two-frequency value kappa_2=sqrt(3). A targeted search found no identical
statement, but historical priority remains unverified.
```

The following wording is not acceptable:

```text
We proved a localized zeta oscillation theorem above pi/2 in every power
interval.
```

Before claiming novelty for the abstract theorem, obtain a specialist search
covering Taikov-type coefficient inequalities, Chebyshev systems,
trigonometric minimax problems, idempotent measures, and sparse Sidon
constants.

The global Mellin--Abel transfer in
`vk-edge-pi-over-two-abel-transfer.md` bypasses the envelope-local bridge and
gives a strict `limsup` constant above `pi/2`. A targeted search has not yet
found the same Bellotti-plus-missing-harmonic conclusion, but this is not a
priority proof. Anderson--Stark type oscillation theorems and older
coefficient inequalities must be checked directly before describing the
global theorem as new.

The envelope-local or multiphase-transform bridge in
`vk-edge-pi-over-two-zeta-bridge.md` is still required for the stronger
power-interval localization.
