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
stronger power-interval localization is derived in
`vk-edge-pi-over-two-localized-transfer.md`, modulo Bellotti's theorem and
Revesz's standard simultaneous contour lemmas. Both have lower collision risk
than the abstract Fourier lemma but require a direct specialist prior-art
check.

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

in a fixed region near the Vinogradov--Korobov boundary. Bellotti defines
`N(sigma,T)` as the cardinality of a set of zero locations and does not
explicitly state a multiplicity convention.  The argument on this branch only
needs the resulting bound on distinct locations; zero multiplicity is carried
separately by logarithmic-derivative residues.  Bellotti's result is not a
finite-package explicit formula and not an oscillation theorem.

Reference:

- C. Bellotti, *A new zero-density estimate for the Riemann zeta function and
  the error term in the Prime Number Theorem*, Theorem 1.2.
  <https://arxiv.org/abs/2508.02041>

As checked on 2026-07-25, arXiv lists only v1, submitted 2025-08-04.  Until a
later version or published proof is available, every zeta specialization here
must state that it is conditional on Bellotti's stated theorem.

## Ingham and Anderson--Stark comparison

Anderson and Stark develop a general Mellin oscillation theorem using weak
independence of selected zero ordinates.  The exact standard formulation is
reproduced as Proposition 1 of Mossinghoff--Oliveira e Silva--Trudgian (2021).
For `Gamma'` to be `N`-independent in `Gamma cap [0,T]`, both of the following
must hold:

```text
(a) sum_(gamma in Gamma') c_gamma gamma = 0 and |c_gamma| <= N
    implies every c_gamma = 0;

(b) sum_(gamma in Gamma') c_gamma gamma = gamma_star in Gamma cap [0,T]
    and |c_gamma| <= N implies gamma_star is in Gamma',
    c_(gamma_star) = 1, and every other coefficient is zero.
```

Under those hypotheses their lower bound is

```text
limsup g(u) >= Res(G,0)
  + (2N/(N+1)) sum_(gamma in Gamma') kappa_T(gamma) |Res(G,i gamma)|,
```

with the analogous upper bound for `liminf`.

Mossinghoff--Trudgian (2017), Theorem 4.1, gives a proof of this formulation
and records the more general Anderson--Stark version: each selected frequency
may have its own contiguous coefficient bound `|c_gamma| <= N_gamma`, and
`N/(N+1)` is replaced termwise by `N_gamma/(N_gamma+1)`.  This is the relevant
generality in the original result; it is still a bounded-integer-relation
hypothesis, not an arbitrary certificate supported on a chosen subset of
integer coefficients.

Reference:

- R. J. Anderson and H. M. Stark, *Oscillation theorems*, in *Analytic
  Number Theory*, Lecture Notes in Mathematics 899, pp. 79--106.
  <https://doi.org/10.1007/BFb0096454>
- M. J. Mossinghoff, T. Oliveira e Silva, and T. S. Trudgian, *The
  distribution of k-free numbers*, Proposition 1, Math. Comp. 90 (2021),
  907--929. <https://arxiv.org/abs/1912.04972>
- M. J. Mossinghoff and T. S. Trudgian, *The Liouville function and the
  Riemann hypothesis*, Theorem 4.1 and the paragraph immediately following
  its proof (2017).
  <https://www.researchgate.net/publication/307577874_The_Liouville_function_and_the_Riemann_hypothesis>

For a singleton `Gamma' = {gamma_0}`, condition (b) has an especially clear
consequence:

```text
c gamma_0 is not another pole frequency for every integer 2 <= c <= N.
```

Thus even the generalized Anderson--Stark theorem requires the absence of
*all* positive multiples through the selected coefficient bound.  The
branch theorem instead obtains a strict gain from the absence of just one
specified odd multiple `(2k+1) gamma_0`; lower multiples and unrelated
bounded integer relations are allowed.  Consequently the published
Anderson--Stark weak-independence theorem does not directly imply the branch
theorem.

### Original-text access audit

Checked on 2026-07-25:

- Springer exposes the chapter metadata and front matter, but the 27-page
  chapter is subscription content in the available session.
- Google Books provides only snippet/limited preview for the scanned volume.
- Internet Archive lists a controlled-borrow copy, but the available session
  is not authenticated for borrowing; the downloadable LCP file is encrypted.
- ResearchGate has no deposited full text and offers only an author-request
  action.

No paywall or controlled-borrow restriction was bypassed.  Therefore this is
not a page-by-page audit of the 1981 scan.  It is, however, an audit of the
precise Anderson--Stark theorem as explicitly attributed, restated, proved,
and generalized in two later primary mathematical sources.  The remaining
original-text risk is that another, separately stated result elsewhere in
the 1981 chapter might subsume the missing-one-odd-harmonic certificate.  No
later source found in the targeted search attributes such a result to
Anderson--Stark.

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

One plausible uniform analytic-number-theory contribution on this branch is
the combination

```text
Bellotti O_A(1) VK-edge count
  -> one missing bounded odd multiple
  -> an explicit fixed-cardinality gap
  -> a strict zeta/PNT global limsup constant above pi/2.
```

This distinction must remain in any later claim of novelty.

There is also a Bellotti-independent candidate in
`vk-edge-pi-over-two-carlson-transfer.md`. For a fixed zeta zero with
`beta_0>1/2`, Carlson's classical estimate gives `N(sigma,T)=o(T)` for a
fixed `sigma` strictly between `1/2` and `beta_0`. Consequently one odd
multiple of `gamma_0` is missing, and the localized pole-annihilation
argument gives a strict gap `delta_(rho_0)>0` in every late `[Y,Y^7]`.

Revesz 1988, Section 5, already imposes a sublinear density condition and
observes that it excludes the linearly dense odd-harmonic obstruction. His
extremal construction also proves that no gap can be uniform as the finite
support size grows. The unresolved priority question is therefore not the
qualitative sparsity mechanism; it is whether the exact

```text
fixed zeta zero + Carlson o(T)
  -> strict zero-dependent gap above pi/2
  -> every [Y,Y^7]
```

conclusion has previously been stated or follows verbatim from an older
general oscillation theorem.

The closest primary statements located in the targeted audit are:

- Revesz (1988), Corollary 2: `pi/2-epsilon` in every sufficiently late
  power interval, but with exponent proportional to `log |rho_0|`;
- Revesz (2023), Theorem 5: the same baseline with an exponent depending on
  `gamma_0` and the distance from the Beurling remainder line;
- Anderson--Stark: finite-frequency gains under bounded integer-relation
  independence, which is stronger than merely omitting one odd harmonic;
- Pintz and Schlage-Puchta: shorter localization obtained with a loss in the
  target-height factor.

None of the checked sources states the exact combination

```text
strict zero-dependent gap above pi/2
  + every [Y,Y^7]
  + arbitrary fixed right-hand zeta zero.
```

This is evidence for a candidate theorem, not proof that no earlier source
contains it. The Carlson `o(T)` pigeonhole itself is a direct classical
observation and must not be presented as the original part.

## Claim policy

The following wording is currently acceptable for the abstract result:

```text
We proved a cardinality-dependent Fourier gap above pi/2 and the exact
two-frequency value kappa_2=sqrt(3). A targeted search found no identical
statement, but historical priority remains unverified.
```

The following wording is not yet acceptable:

```text
We proved a new localized zeta oscillation theorem above pi/2 in every power
interval, with established historical priority.
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

The finite-pole annihilation route in
`vk-edge-pi-over-two-localized-transfer.md` bypasses the earlier
envelope-local and weighted-Cassels blockers. The mathematical derivation has
passed internal audit, but historical priority and external specialist review
remain open.
