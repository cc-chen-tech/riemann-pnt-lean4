# Selberg positive proportion: mathematical mainline audit

## Status

This is a paper-first audit.  It does not claim that Selberg's theorem has
already been reproved in Lean.  The exact Fourier--Mellin step S1 has now been
proved both on paper and in Lean, and the complete finite S13 coefficient
estimate has now also been formalized.  The full S12 estimate has now been
proved as well: its quantitative reciprocal-zeta input, coprime Dirichlet
series, exact logarithmic Perron identity, finite Euler factors, square-root
kernel integral, and optimized choice `epsilon = 1 / log Y` are all closed
without `sorry`, `admit`, or new axioms.  The initially formalized integer
cutoff was not sufficient for the arithmetic split, whose exact local
parameter is the real number `Y = X / d`.  This has now been repaired by
`SelbergS12RealCutoff.lean`, including the range `0 < Y < e`.

The paper derivation of S-arith is now closed below.  Its Jordan weight,
smooth/coprime unique factorization, exact taper/Perron bridge, finite pair
reindexing, grouped equation (S17), the two asymmetric S12 applications,
the S13 finite-product bridge, the resulting bound (S19), the concrete
four-variable Jordan quadratic identity (S14), the primewise fourth-power
comparison, and the final `rho`-sum using (S20) have all been formalized.
Thus S-arith itself is now closed.  S2 is now connected to the exact S1
kernel with the genuine sliding integral and exact Mathlib Fourier
normalization.  S3 is now complete, and S4 has both its exact critical-line
modulus bridge, its genuine `re(s)=2` first-moment main term, and its uniform
horizontal-edge estimate.  Its uniform lower-Stirling estimate is now also
formalized.  The theorem remains incomplete until these S4 components are
assembled into the lower first moment and the S5/packing interfaces are
instantiated.

The main conclusion is decisive:

* the length-`T^3` linear Möbius moment is not the missing lemma in Selberg's
  positive-proportion proof;
* the appropriate mainline is Selberg's original Fourier--Mellin argument,
  as presented in Titchmarsh, §§10.9--10.22;
* the repository's existing logarithmic-window packing theorem can be reused,
  but the present one-sided zeta truncation should not be the analytic engine
  for the two bad-set estimates.

The implementation order is strict: first close each remaining estimate on
paper with one Fourier normalization, and only then formalize that estimate.
This rule was used for S1--S2 and remains in force for S3--S4.

## 1. Why the `T^3` moment is not the Selberg mainline

The separate note

```text
docs/research/2026-08-24-mobius-weighted-off-diagonal.md
```

studies

\[
 \int |\zeta(\tfrac12+it)|^2
 \left|\sum_{n\le T^3}\frac{\mu(n)}{n^{1/2+it}}
        \left(1-\frac{\log n}{3\log T}\right)\right|^2W(t/T)\,dt.
\]

An asymptotic of size `T` for this object is a length-three instance of the
all-length mollifier problem.  It is far stronger than the existence of an
unspecified positive Selberg proportion.  The published Bettin--Chandee--
Radziwill estimate does not cover its longest boxes, and the proposed
`MWKF(3)` estimate is unproved.

There is also an earlier analytic break in the claimed exact reduction.  In
Bettin--Chandee--Radziwill, the zero Poisson mode is converted to the main
term only after all of the following operations:

1. truncate an approximate functional equation in a range in which its
   error remains harmless after multiplication by the polynomial;
2. replace the exact logarithmic phase and exact weight by their leading
   forms, with a quantified error;
3. integrate twice by parts in the shift variable;
4. use the cosine Mellin transform, the `zeta(2w)` functional equation, and
   a test function which vanishes at `w = 1/2`;
5. finally shift from `Re w = 2` to `Re w = -1/4` and take the residue at
   zero.

The current formulas (4.6b)--(4.8) in the `T^3` note retain the exact
nonlinear kernel but then jump directly to the Mellin expression produced by
steps 2--4.  The exact kernel does not separate into a bare `zeta(2w)`
Dirichlet series by the argument presently written.  Thus (4.6b), and hence
the assertion that the remainder in (4.8) consists exactly of the nonzero
Poisson modes, remains unproved independently of `MWKF(3)`.

This does not disprove the long-mollifier moment.  It classifies it correctly:
it is a separate frontier problem and not a prerequisite for Selberg's
theorem.

## 2. The correct mollifier and sign function

For `Re s > 1`, define

\[
 \zeta(s)^{-1/2}=\sum_{n\ge1}\frac{\alpha_n}{n^s},
 \qquad \alpha_1=1.
\]

The Euler product gives multiplicativity on coprime arguments and
`|alpha_n| <= 1`.  Put

\[
 \beta_n=\alpha_n\left(1-\frac{\log n}{\log X}\right)
       \mathbf 1_{n<X},
 \qquad
 \psi_X(s)=\sum_{n<X}\frac{\beta_n}{n^s}.
\]

This is the same square-root-zeta taper already represented by the repository
definitions `selbergSqrtZetaCoeff` and
`selbergSqrtZetaTaperedCoeff`.

Following Titchmarsh §10.10, introduce, for `delta > 0`, a real function

\[
 F_{\delta,X}(t)
 =\frac{1}{\sqrt{2\pi}}
   \frac{\Xi(t)}{t^2+1/4}
   |\psi_X(\tfrac12+it)|^2
   \exp\!\left((\tfrac\pi4-\tfrac\delta2)t\right).
\]

The gamma and exponential factors outside `Xi(t)` are strictly positive,
while `|psi_X|^2` is nonnegative and may vanish.  Thus, up to the fixed
global sign coming from the convention relating `Xi` to completed zeta,
every strict positive or negative value of `F` gives the opposite strict
sign of the Hardy function.  Zeros of the mollifier can add zeros to `F`,
but cannot create a sign change.  This one-way sign-change transfer is all
the counting argument needs.  This is
the reason to use the completed function: its Mellin representation gives an
exact Fourier transform, so no pointwise zeta approximation and no long
Dirichlet-polynomial remainder are introduced.

The repository already contains two important pieces of this route:

* `HardyTheorem/HardyCompletedCriticalLine.lean` transfers signs and zeros
  between the completed critical-line function and `hardyZ`;
* `HardyTheorem/CompletedZetaFourier.lean` gives an exact critical-line
  Fourier representation from Mathlib's modified theta Mellin kernel.

## 3. Parameter order

The parameters must be selected in this order.

1. Choose a fixed `c` with `0 < c < 1/8`.
2. Choose `a > 0` small enough for the final good-window inequality.
3. Require

   \[
     (a+2)c\le \frac14.
   \]

4. For large `T`, set

   \[
     \delta=T^{-1},\qquad X=\delta^{-c}=T^c,
     \qquad h=\frac{2\pi}{a\log X}=\frac{2\pi}{ac\log T}.
   \]

   The factor `2*pi` is deliberate.  The paper uses the unitary angular
   frequency `y`, whereas Mathlib's `L2` Fourier operator uses frequency
   `w` and phase `exp(-2*pi*i*t*w)`.  Thus `y=2*pi*w`, and this choice makes
   the Fourier split `|w|=1/h` correspond exactly to
   `|y|=a*log X`, so that `G=exp(a*log X)=X^a`.  This fixed factor has no
   effect on the final `T*log T` scale.

The mollifier therefore has a small positive power length.  It is neither a
fixed polynomial nor a polynomial of length `T^3`.

## 4. Paper-proof lemma ledger

The following ledger is a self-contained target for the mathematical proof.
Implicit constants may depend on fixed `a` and `c`, but not on `T`.

### S1. Exact Fourier pair

Derive the Fourier transform of `F_{delta,X}` by multiplying the completed
zeta Mellin integral by `psi_X(s) psi_X(1-s)` and interchanging only finite
mollifier sums with the absolutely convergent initial integral.  After the
logarithmic change of variables, the transform is the explicit theta series
in Titchmarsh §10.10.

The proof must record the Fourier convention, the exponential tilt, the pole
residue, and the reality symmetry.  No approximate functional equation is
needed.

### S2. Arithmetic Fourier energy

Let `g(x)` be the nonconstant triple theta sum obtained from S1 and define

\[
 J(x,\theta)=\int_x^\infty |g(u)|^2u^{-\theta}\,du,
 \qquad 0<\theta\le\frac12.
\]

Reproduce the diagonal/off-diagonal calculation of §§10.11--10.17.  If
`q = gcd(kappa*nu, lambda*mu)`, the diagonal is governed by

\[
 S(\theta)=
 \sum_{\kappa,\lambda,\mu,\nu<X}
 \left(\frac{q}{\kappa\mu}\right)^{1-\theta}
 \frac{\beta_\kappa\beta_\lambda
       \beta_\mu\beta_\nu}{\lambda\nu}.
\]

The arithmetic core is

\[
 \boxed{S(\theta)\ll \frac{X^{2\theta}}{\log X}}
 \qquad(0\le\theta\le\tfrac12),
 \tag{S-arith}
\]

uniformly in `theta`; in particular `S(0) << 1/log X`.  The
square-root-zeta coefficients and their linear taper must be kept until after
the coprime reindexing.  The conditions `c < 1/8` and
`(a+2)c <= 1/4` are used when the off-diagonal Gaussian tails and the
remaining endpoint terms are discarded.

The proof of (S-arith) must expose, rather than hide, the two estimates used
in Titchmarsh §§10.12--10.14.  With `rho` supported on the primes extracted
from the gcd,

\[
 \sum_{\substack{k<X/d\\(k,\rho)=1}}
  \frac{\alpha_k}{k^{1-\theta}}
  \log\frac{X}{dk}
 \ll
 \left(\frac Xd\right)^\theta
 \left(\log\frac Xd\right)^{1/2}
 \prod_{p\mid\rho}\left(1+\frac1p\right)^{1/2},
 \tag{S12}
\]

and

\[
 \sum_{\rho\mid dd_1}
  \frac{|\alpha_d\alpha_{d_1}|}{dd_1}
 \ll \frac1\rho
 \prod_{p\mid\rho}\left(1+\frac1p\right).
 \tag{S13}
\]

For (S12), the square-root branch in
`1/sqrt(zeta(1-theta+s))` is shifted to `Re s = theta`.  This uses the
classical zero-free line `zeta(1+it) != 0`, the pole at `t = 0`, and the
quantitative bound

\[
  |\zeta(1+it)|^{-1}\ll |t| \qquad(t\ne0).
  \tag{Z1}
\]

Near zero, (Z1) is the Laurent expansion at the pole; at large height it is
a deliberately coarse consequence of the classical zero-free-line bounds.
Mere nonvanishing is not enough: the square root of (Z1) is what makes the
shifted Perron integral cost `theta^(-1/2)`, and hence only
`sqrt(log (X/d))`.  These are genuine analytic dependencies and must be
present in the later Lean dependency audit.

For the Lean proof, (Z1) can be obtained from the already formalized inner
zero-free-region estimate even though its available logarithmic-derivative
bound is only `O(log^2 |t|)`.  Let that bound be

\[
 \left|\frac{\zeta'}\zeta(\sigma+it)\right|
 \le C\log^2|t|
\]

throughout the inner zero-free strip.  Choose a fixed `a > 0` with
`a*C <= 1/2`, and put `sigma_1 = 1 + a/log|t|`.  Absolute convergence of the
Mobius Dirichlet series gives

\[
 \left|\zeta(\sigma_1+it)^{-1}\right|
 \le \zeta(\sigma_1)
 \le \frac{\sigma_1}{\sigma_1-1}
 \ll_a \log|t|.
\]

Apply Gronwall to `g(x) = 1/zeta(sigma_1-x+it)` on the horizontal segment of
length `a/log|t|`.  Since `|g'| <= C log^2|t| |g|`,

\[
 |g(a/\log|t|)|
 \le |g(0)|\exp(aC\log|t|)
 \ll_a \log|t|\,|t|^{1/2}
 \ll_a |t|.
\]

Thus the existing `O(log^2)` theorem is quantitatively sufficient for (Z1);
no unproved boundary-line logarithmic-derivative estimate is being assumed.
On bounded height, compactness away from `t=0` and the reciprocal pole model
at `1` supply the remaining uniform constant.

This route is now formalized, without `sorry`, `admit`, or new axioms, in:

* `HardyTheorem/SelbergS12RightLine.lean` (absolute-convergence base point),
* `HardyTheorem/SelbergS12Gronwall.lean` (exact horizontal derivative and
  Gronwall propagation),
* `HardyTheorem/SelbergS12HighTransfer.lean` and
  `HardyTheorem/SelbergS12HighBound.lean` (large height),
* `HardyTheorem/SelbergS12NearOne.lean` (linear vanishing of the reciprocal
  local model),
* `HardyTheorem/SelbergS12BoundedHeight.lean` (compact annulus), and
* `HardyTheorem/SelbergS12ZetaInverse.lean` (global punctured Z1),
* `HardyTheorem/SelbergS12CoprimeDirichlet.lean` (principal-character
  deletion of the Euler factors dividing `r`),
* `HardyTheorem/SelbergPerronKernel.lean` and
  `HardyTheorem/SelbergPerronLSeries.lean` (exact logarithmic Perron
  inversion and absolute Tonelli interchange),
* `HardyTheorem/SelbergS12PerronIdentity.lean` (the exact finite weighted
  coprime sum),
* `HardyTheorem/SelbergS12StripZetaInverse.lean` and
  `HardyTheorem/SelbergS12CoprimeStripBound.lean` (the two-dimensional strip
  bound and its finite Euler factors),
* `HardyTheorem/SelbergS12KernelIntegral.lean` (the scale-invariant
  square-root Perron kernel), and
* `HardyTheorem/SelbergS12PerronBound.lean` and
  `HardyTheorem/SelbergS12OptimizedBound.lean` (Perron synthesis and the
  standard integer-cutoff S12 estimate), and
* `HardyTheorem/SelbergS12RealCutoff.lean` (the exact positive real cutoff
  `Y = X / d`, including a global-`X` estimate uniform for `0 < Y <= X`).

The puncture at `t=0` in the boundary-line Z1 statement is required because
Mathlib assigns a finite point value to the meromorphic zeta function at its
pole.  The completed S12 proof avoids evaluating a boundary square root:
Perron's identity is valid on every line `sigma > theta`, and the optimized
proof takes `sigma = theta + 1 / log Y`.  Hence the whole integral stays in
the absolute-convergence half-plane while approaching the boundary at the
exact rate for which `Y^(1 / log Y) = e`.

### Exact closure of S-arith on paper

Put

\[
 P(\rho)=\prod_{p\mid\rho}\left(1+\frac1p\right),
 \qquad
 A_\rho(\theta)=
 \sum_{\substack{\kappa,\nu\le X\\ \rho\mid\kappa\nu}}
 \frac{\beta_\kappa\beta_\nu}
      {\kappa^{1-\theta}\nu}.
\]

For `0 <= theta <= 1/2`, generalized Jordan inversion gives the exact
identity

\[
 \gcd(m,n)^{1-\theta}
 =\sum_{\rho\mid\gcd(m,n)}J_{1-\theta}(\rho),
 \qquad
 S(\theta)=\sum_{\rho\le X^2}
 J_{1-\theta}(\rho)A_\rho(\theta)^2.                 \tag{S14}
\]

Here `J_alpha = mu * (n -> n^alpha)`.  Its prime-power formula is

\[
 J_\alpha(p^{k+1})=p^{(k+1)\alpha}-p^{k\alpha};
\]

hence for `alpha >= 0`,

\[
 0\le J_\alpha(\rho)\le \rho^\alpha.                \tag{S15}
\]

For each positive integer `n`, split its prime factorization uniquely as

\[
 n=d k,\qquad p\mid d\Longrightarrow p\mid\rho,
 \qquad (k,\rho)=1.                                  \tag{S16}
\]

This is exactly the substitution made in Titchmarsh §10.11.  Since the
square-root-zeta coefficients are multiplicative across the coprime split,
write

\[
 B_{\rho,d}(\eta)=
 \sum_{\substack{k\ge1\\(k,\rho)=1}}
 \frac{\alpha_k}{k^{1-\eta}}
 \log^+\frac{X}{dk}.
\]

The support of `log+` makes this a finite sum.  Notice that its cutoff is
the exact real number `X/d`; replacing it by an integer ceiling would change
the signed logarithmic weight.  The taper identity and (S16) give

\[
 A_\rho(\theta)=\frac1{\log^2X}
 \sum_{\substack{d,d_1\ \rho\text{-supported}\\
                  \rho\mid dd_1}}
 \frac{\alpha_d\alpha_{d_1}}
      {d^{1-\theta}d_1}
 B_{\rho,d}(\theta)B_{\rho,d_1}(0).                 \tag{S17}
\]

The two inner sums are deliberately estimated with different parameters:
S12 is used with `eta = theta` for the first and `eta = 0` for the second.
The global-`X` real-cutoff form of S12 gives, uniformly even when `X/d < e`,

\[
 |B_{\rho,d}(\theta)|
 \ll (X/d)^\theta\sqrt{\log X}\sqrt{P(\rho)},
 \qquad
 |B_{\rho,d_1}(0)|
 \ll \sqrt{\log X}\sqrt{P(\rho)}.                  \tag{S18}
\]

Consequently the factor `d^(-theta)` from (S18) combines with
`d^(-(1-theta))` in (S17), and the two square-root logarithms cancel only
one of the two taper logarithms:

\[
 |A_\rho(\theta)|
 \ll \frac{X^\theta P(\rho)}{\log X}
 \sum_{\substack{d,d_1\ \rho\text{-supported}\\
                  \rho\mid dd_1}}
 \frac{|\alpha_d\alpha_{d_1}|}{dd_1}.
\]

The finite S13 estimate therefore yields

\[
 \boxed{
 |A_\rho(\theta)|
 \ll \frac{X^\theta}{\rho\log X}P(\rho)^2.}        \tag{S19}
\]

Combining (S14), (S15), and (S19),

\[
 S(\theta)\ll \frac{X^{2\theta}}{\log^2X}
 \sum_{\rho\le X^2}\frac{P(\rho)^4}{\rho^{1+\theta}}.
\]

For every prime `p >= 2`,

\[
 (1+p^{-1})^4\le1+9p^{-1}.
\]

Thus `P(rho)^4 <= product_(p|rho)(1+9/p)`.  The squarefree-divisor
expansion of this latter product, comparison with `tau_9(d)/d^2`, and one
harmonic sum give

\[
 \sum_{\rho\le Y}\frac1\rho
   \prod_{p\mid\rho}(1+9/p)\ll1+\log Y.              \tag{S20}
\]

Since `rho^(-theta) <= 1` and `X >= e`, (S20) with `Y = X^2` proves

\[
 \boxed{S(\theta)\ll X^{2\theta}/\log X}
 \qquad(0\le\theta\le1/2).
\]

The following Lean modules now certify the complete derivation of S-arith:

* `SelbergJordanWeight.lean`: (S14)'s divisor identity and (S15);
* `SelbergSmoothCoprimeSplit.lean`: the existence, uniqueness,
  coprimality, support, and coefficient factorization in (S16);
* `SelbergTaperPerronBridge.lean`, `SelbergSmoothCoprimeEquiv.lean`, and
  `SelbergSArithmeticPairReindex.lean`: the exact taper identity, finite
  smooth/coprime equivalence, and removal of the coprime residuals from
  `rho | kappa * nu`;
* `SelbergSArithmeticPairSplit.lean`, `SelbergSArithmeticLocalSum.lean`, and
  `SelbergSArithmeticGrouped.lean`: the exact finite split, equality of each
  coprime fiber with the real-cutoff S12 sum, and grouped equation (S17);
* `SelbergSArithmeticFactorBound.lean`: the exact cancellation
  `d^(theta-1) * (X/d)^theta = X^theta/d` and the local S12 factor bound;
* `SelbergS13DivisorPair.lean` through `SelbergS13AbsoluteBound.lean`: S13;
* `SelbergS13BoundedSmoothBridge.lean` and
  `SelbergS13GroupedAbsolute.lean`: the bridge from the actual bounded
  smooth pair set to S13 and the uniform `2 * rho^-1 * P(rho)` estimate;
* `SelbergSArithmeticPairBound.lean`: the complete uniform bound (S19),
  with no `sorry`, `admit`, or new axiom;
* `SelbergSArithmeticJordanIdentity.lean`: the concrete Titchmarsh
  four-variable sum with `q = gcd(kappa * nu, lambda * mu)`, and its exact
  factorization as the Jordan-weighted square (S14);
* `SelbergSArithmeticEulerWeight.lean`: the primewise comparison
  `P(rho)^4 <= product_(p|rho)(1+9/p)`;
* `SelbergSArithmeticDivisorExpansion.lean`,
  `SelbergSArithmeticSummability.lean`,
  `SelbergSArithmeticDivisorMajorant.lean`,
  `SelbergSArithmeticHarmonic.lean`,
  `SelbergSArithmeticFiniteConvolution.lean`, and
  `SelbergSArithmeticLogTail.lean`: (S20);
* `SelbergSArithmeticFinalBound.lean`: insertion of S19 into S14, the
  nonnegative Jordan-weight estimate, the S20 logarithmic tail, and the
  final uniform bound
  `norm S(theta) <= C * X^(2*theta) / log X` for `0 <= theta <= 1`.

The required sliding signed-mass consequence is

\[
 \boxed{
 \int_{\mathbb R}
   \left|\int_t^{t+h}F_{\delta,X}(u)\,du\right|^2dt
 \ll \frac{h}{\delta^{1/2}\log X}.}
 \tag{S2}
\]

### Paper closure of S2

The normalization in S1 agrees with Titchmarsh exactly.  Write `x = exp y`
and

\[
 g(x)=\sum_{n\ge1}\sum_{\mu,\nu<X}
 \frac{\beta_\mu\beta_\nu}{\nu}
 \exp\!\left[-\pi\frac{n^2\mu^2x^2}{\nu^2}
                 (\sin\delta+i\cos\delta)\right].
\]

For `0 < theta <= 1/2`, put

\[
 J(x,\theta)=\int_x^\infty |g(u)|^2u^{-\theta}\,du.
\]

After expanding the square, the diagonal condition is

\[
 \frac{m\kappa}{\lambda}=\frac{n\mu}{\nu}.
\]

Let `q = gcd(kappa*nu,lambda*mu)`.  Since the two quotients after division
by `q` are coprime, every diagonal solution is uniquely

\[
 m=r\frac{\lambda\mu}{q},\qquad
 n=r\frac{\kappa\nu}{q}\qquad(r\ge1).
\]

Thus its Gaussian parameter is

\[
 \eta=2\pi\frac{\kappa^2\mu^2}{q^2}\sin\delta.
\]

For `z >= 1`, Euler summation in the form

\[
 \sum_{r\le z}r^{\theta-1}
 =\frac{z^\theta}{\theta}+\frac{K(\theta)}{\theta}
   +O(z^{\theta-1}),
 \qquad |K(\theta)|\ll1,
 \tag{S2-Euler}
\]

is uniform on `0 < theta <= 1/2`.  This uniformity can be proved without
analytic continuation: subtract the telescoping increments of
`t^theta/theta`; the resulting summand is `O(n^(theta-2))`, uniformly
summable in this theta range.  The substitution `v=r*sqrt(eta)*u` then
gives

\[
 \begin{aligned}
 \sum_{r\ge1}\int_x^\infty e^{-\eta r^2u^2}u^{-\theta}\,du
 &=\frac{\sqrt\pi}{2\theta x^\theta\sqrt\eta}
   +\frac{K_1(\theta)}{\theta}\eta^{(\theta-1)/2}\\
 &\quad+O\!\left(\frac{x^{1-\theta}}{\theta}
             \log(2+\eta^{-1})\right),
 \end{aligned}
 \tag{S2-diagonal-kernel}
\]

with `K_1` uniformly bounded.  The first two terms must remain signed:
after summing the mollifier variables they are exactly constant multiples
of `S(0)` and `S(theta)`.  Taking absolute values earlier would destroy the
square-root-zeta cancellation.  Only the final displayed remainder is
estimated with `|beta_n| <= 1`.  The proved S-arith estimate yields, for
`1 <= x <= G`,

Here is the exact route to (S2-diagonal-kernel), including the endpoint
errors that are suppressed in the classical notation.  Put

\[
 a=x\sqrt\eta,\qquad
 A_\theta(z)=\sum_{1\le r\le z}r^{\theta-1}.
\]

Tonelli and `y=r*sqrt(eta)*u` give

\[
 \sum_{r\ge1}\int_x^\infty e^{-\eta r^2u^2}u^{-\theta}\,du
 =\eta^{(\theta-1)/2}
   \int_a^\infty e^{-y^2}y^{-\theta}
     A_\theta(y/a)\,dy.                 \tag{S2-diagonal-Tonelli}
\]

For real `z>=1`, the discrete Euler theorem already proved in
`SelbergEulerPowerSum.lean` implies the sharpened floor form

\[
 A_\theta(z)=\frac{z^\theta+K(\theta)}\theta+E_\theta(z),
 \qquad |E_\theta(z)|\le z^{\theta-1}. \tag{S2-Euler-floor}
\]

Indeed, with `N=floor(z)`, the existing exact formula has
`(N+1)^theta/theta-R_N`.  Concavity gives
`0<=((N+1)^theta-z^theta)/theta<=z^(theta-1)`, while
`0<=R_N<=(N+1)^(theta-1)<=z^(theta-1)`.  Their difference therefore has
absolute value at most `z^(theta-1)`; using the sum of the two bounds would
unnecessarily lose a factor two.

Inserting (S2-Euler-floor) into (S2-diagonal-Tonelli) separates three
terms.  The `z^theta` term is

\[
 \frac{x^{-\theta}\eta^{-1/2}}\theta
 \int_a^\infty e^{-y^2}\,dy
 =\frac{\sqrt\pi}{2\theta x^\theta\sqrt\eta}
  +O\!\left(\frac{x^{1-\theta}}\theta\right),
\]

because the omitted interval `[0,a]` has length `a`.  The signed
`K(theta)` term is

\[
 \frac{K(\theta)}{\theta}\eta^{(\theta-1)/2}
 \int_a^\infty e^{-y^2}y^{-\theta}\,dy
 =\frac{K_1(\theta)}\theta\eta^{(\theta-1)/2}
  +O\!\left(\frac{x^{1-\theta}}\theta\right),
\]

where

\[
 K_1(\theta)=\frac12K(\theta)
   \Gamma\!\left(\frac{1-\theta}{2}\right).
\]

This remains uniformly bounded for `0<theta<=1/2`; the lower-interval
error uses `1/(1-theta)<=2`.  Finally the floor remainder is bounded by

\[
 x^{1-\theta}\int_a^\infty\frac{e^{-y^2}}y\,dy
 \ll x^{1-\theta}\log(2+\eta^{-1}).
\]

For `a<=1`, split at one and use
`integral_a^1 dy/y=log(1/a)<=log(2+eta^(-1))`; for `a>=1`, dominate the
tail by an absolute constant.  This derivation identifies the next Lean
interfaces precisely: first (S2-Euler-floor), then the three scalar
Gaussian integral bounds, and only then Tonelli and the signed kernel
identity.

The proved S-arith estimate yields, for `1 <= x <= G`,

\[
 \Sigma_1\ll
 \frac1{\delta^{1/2}\theta x^\theta\log X},
 \tag{S2-diagonal}
\]

provided the integer cutoff satisfies `X <= delta^(-c)`, `G=X^a`, and

\[
(a+2)c\le\frac14.
\]

The exact finite diagonal bookkeeping is now closed as follows.  With

\[
 \eta=2\pi\sin\delta\left(\frac{\kappa\mu}{q}\right)^2,
 \qquad q=\gcd(\kappa\nu,\lambda\mu),
\]

the two signed kernel main terms have been identified term by term with the
concrete finite sums `S(0)` and `S(theta)`, before taking norms.  The remaining
kernel error is summed only after applying `|beta_n| <= 1`.  The deliberately
coarse count of the four mollifier variables gives

\[
 \|\Sigma_{\rm rem}\|\le X^4\left\{
   3\frac{x^{1-\theta}}\theta+
   x^{1-\theta}\log\left(2+\frac{X^4}{\delta}\right)
 \right\}.                                           \tag{S2-diagonal-rem}
\]

Here the uniform parameter bound follows from
`q <= kappa*nu <= X^2`, `kappa*mu >= 1`, and
`pi*sin(delta) >= delta` for `0 < delta <= 1`, which imply
`eta >= delta/X^4`.  This crude `X^4` loss is sufficient and keeps the
remainder proof independent of the signed arithmetic cancellation.

For completeness, the absorption has the following exact power accounting.
Use `X<=delta^(-c)`, `x<=X^a`, and put

\[
 \varepsilon=\frac14-2c>0.
\]

The ratio of (S2-diagonal-rem) to the target
`delta^(-1/2)/(theta*x^theta*log X)` is at most a constant times

\[
 \delta^{1/2}X^{a+4}\log X
 \left(3+\theta\log\left(2+X^4/\delta\right)\right)
 \ll \delta^\varepsilon(1+\log^2(1/\delta)),
\]

because

\[
 \frac12-c(a+4)
 =\frac12-c(a+2)-2c\ge\frac14-2c=\varepsilon.
\]

The right side is uniformly bounded for `0 < delta <= 1`.  For the signed
`S(theta)` main term, the corresponding ratio is

\[
 \delta^{\theta/2}X^{2\theta}x^\theta
 \le \left(\delta^{1/2}X^{a+2}\right)^\theta
 \le \delta^{\theta/4}\le1.
\]

Thus both signed main terms and the absolute remainder have the scale in
(S2-diagonal).  No cancellation is claimed for the remainder.

Before estimating the off-diagonal, the exact square expansion has to be
kept visible.  Put

\[
 A=\frac{m\kappa}{\lambda},\qquad
 B=\frac{n\mu}{\nu},\qquad
 b_{\kappa,\lambda}=\frac{\beta_\kappa\beta_\lambda}{\lambda}.
\]

The term of `g(u)` indexed by `(m,kappa,lambda)` is

\[
 b_{\kappa,\lambda}
 \exp\{-\pi A^2u^2(\sin\delta+i\cos\delta)\}.
\]

Since every `beta` is real, multiplication by the conjugate term indexed by
`(n,mu,nu)` gives exactly

\[
 \frac{\beta_\kappa\beta_\lambda\beta_\mu\beta_\nu}
      {\lambda\nu}
 u^{-\theta}
 \exp\{-P u^2+i\pi\cos\delta(B^2-A^2)u^2\},              \tag{S2-pair}
\]

where

\[
 P=\pi\sin\delta(A^2+B^2).
\]

Thus the diagonal is `A=B`, not merely a formally selected gcd sum.  On that
set (S2-pair) is precisely the real Gaussian series already reindexed by

\[
 m=r\frac{\lambda\mu}{q},\qquad
 n=r\frac{\kappa\nu}{q},\qquad
 q=(\kappa\nu,\lambda\mu).
\]

The two off-diagonal sides require slightly different bookkeeping.  If
`A>B`, put

\[
 Q=\pi\cos\delta(A^2-B^2)>0.
\]

The actual integrand then contains `exp((-P-iQ)u^2)`, whereas the normalized
oscillatory lemma is stated with `exp((-P+iQ)u^2)`.  These two integrals are
complex conjugates because the remaining weight is real, so their norms are
equal.  On the reverse side `B>A` the phase is already `+iQ`.  This
conjugation step and the partition

\[
 \{A=B\}\ \dot\cup\ \{A>B\}\ \dot\cup\ \{B>A\}
\]

must occur before applying the existing positive square-gap majorant.  In
particular, the present `selbergOffDiagonalTwoSideSquareSum` is a proved
majorant for the two ordered pair sums, but it is not by itself yet the
object-level expansion of `J`; the missing formal bridge is the equality

\[
 (J(x,\theta):\mathbf C)
   =\Sigma_{\rm diag}(x,\theta)
    +\Sigma_{A>B}(x,\theta)
    +\Sigma_{B>A}(x,\theta).                         \tag{S2-J-split}
\]

Absolute Fubini is legitimate here and should be proved before
(S2-J-split): on `u>=x>=1`, `u^(-theta)<=1`, and the norm of (S2-pair) is
bounded by

\[
 \frac1{\lambda\nu}
 e^{-a_0(m^2+n^2)u^2},\qquad
 a_0=\frac{\delta}{X^2}>0,
\]

using `|beta_j|<=1` and
`pi*sin(delta)*(j/k)^2 >= delta/X^2` for `1<=j,k<=X`.  The double Gaussian
series and its tail integral converge absolutely.  This supplies both the
square-product interchange and the sum--integral interchange without using
off-diagonal cancellation.

For the numerical off-diagonal estimate, set

\[
 P=\pi\sin\delta\left(rac{m^2\kappa^2}{\lambda^2}
                       +\frac{n^2\mu^2}{\nu^2}\right),\qquad
 Q=\pi\cos\delta\left|\frac{m^2\kappa^2}{\lambda^2}
                       -\frac{n^2\mu^2}{\nu^2}\right|.
\]

One integration after `v=u^2` (equivalently the second mean-value theorem)
gives

\[
 \left|\int_x^\infty e^{-Pu^2+iQu^2}u^{-\theta}\,du\right|
 \ll \frac{e^{-Px^2}}{x^{\theta+1}Q}
 \le \frac{e^{-Px^2}}{x^\theta Q}.
 \tag{S2-osc}
\]

If `m*kappa/lambda > n*mu/nu`, then

\[
 \frac{m^2\kappa^2}{\lambda^2}
 -\frac{n^2\mu^2}{\nu^2}
 \ge\frac{m\kappa(m\kappa\nu-n\lambda\mu)}{\lambda^2\nu}.
\]

The last parenthesis is a positive integer.  The Gaussian factor
`exp(-P*x^2)` is essential here: dropping it would leave a divergent
harmonic sum over `m`.  More precisely, put

\[
 K=m\kappa\nu,\qquad d=\lambda\mu,\qquad
 N=\left\lfloor\frac{K-1}{d}\right\rfloor,
 \qquad r=K-Nd.
\]

Then `1 <= r <= d`, the admissible positive integers `n` are exactly
`1 <= n <= N`, and the order-reversing substitution `j=N-n` gives

\[
 \sum_{\substack{n\ge1\\nd<K}}\frac1{K-nd}
 =\sum_{j=0}^{N-1}\frac1{r+jd}
 \le 1+\frac{1+\log N}{d}.                 \tag{S2-gap-class}
\]

Since `N <= K/d <= m*X^2`, one may replace `log N` by `log(m*X^2)`.
For `m,X >= 1`, `log(m*X^2) <= 2*log(m*X)`, which is the exact
constant-bearing form behind Titchmarsh's
`1+O(log(mX)/(lambda*mu))`.  Equivalently, after the first positive residue
is separated, the remaining values lie in a residue class of step
`d=lambda*mu`; if there are at most `M` remaining values then

\[
 \sum_{j=1}^{M}\frac1{r+jd}
 \le \frac1d\sum_{j=1}^{M}\frac1j
 \le \frac{1+\log M}{d}.
\]

This is now formalized, together with the preceding rational-square gap, in
`SelbergOffDiagonalArithmetic.lean`.  Applying it with
`M <= m*kappa*nu/(lambda*mu)`, and then summing the remaining damped
`m`-series, gives

\[
 \begin{aligned}
 &\frac{\lambda}{\kappa}
   \frac{e^{-am^2}}m
   \left(1+\frac{1+\log N}{\lambda\mu}\right)\\
 &\qquad\le
 \frac{2\lambda}{\kappa}
 \left\{
   \frac{e^{-am^2}}m+
   \frac1{\lambda\mu}
   \frac{\log(mX)e^{-am^2}}m
 \right\}.                                      \tag{S2-fixed-side}
 \end{aligned}
\]

Indeed `N <= m*X^2`, `log N <= 2*log(m*X)`, and
`(lambda*mu)^(-1) <= 1`.  Thus the explicit factor `2` absorbs both the
first residue-class correction and the factor two in the logarithm.  The
reverse side follows by the involution
`(m,kappa,lambda) <-> (n,mu,nu)`; the exterior coefficient
`1/(lambda*nu)` is invariant under this simultaneous swap.  Summing
(S2-fixed-side) over `m` and then the four mollifier indices gives

\[
 \Sigma_2\ll \frac{X^4}{x^\theta}\log^2\frac1\delta.
 \tag{S2-offdiagonal}
\]

The reverse inequality is symmetric.  The explicit Lean majorant currently
proved is

\[
 8x^{-\theta}\{X^4(1+\log X)L+X^2(1+\log X)^2W\},       \tag{S2-off-explicit}
\]

where

\[
 L=\log(2X^2/\delta),\qquad
 W=(\log X+\log(X^2/\delta))L+2.
\]

Here is an exact elementary absorption, avoiding an unspecified
`O(log^2(1/delta))`.  Let `z=X^2/delta` and
`ell=1+log z`.  For `X>=e` and `0<delta<=1`,

\[
 0\le\log X\le\log z\le\ell,\quad L\le\ell,\quad
 W\le4\ell^2.
\]

Hence the braces in (S2-off-explicit) are at most `5 X^4 ell^4`.  After
division by the diagonal target
`delta^(-1/2)x^(-theta)/(theta log X)`, the ratio is at most

\[
 20\,\delta^{1/2}X^4\ell^5.                            \tag{S2-off-ratio}
\]

For every `r>0`, `ell <= (1+1/r)z^r`; therefore (S2-off-ratio) is bounded
by

\[
 20(1+1/r)^5
 \delta^{1/2-5r}X^{4+10r}
 \le
 20(1+1/r)^5
 \delta^{1/2-4c-r(5+10c)}.
\]

When `c<1/8`, choose

\[
 0<r\le\frac{1/2-4c}{5+10c}.
\]

The final exponent is nonnegative, so the ratio is uniformly bounded for
`0<delta<=1`.  Thus, once the object-level equality (S2-J-split) and its
Fubini justification are proved, the reverse side and (S2-off-explicit)
combine with (S2-diagonal) to give, uniformly for `0<theta<=1/2`,

\[
 \boxed{J(x,\theta)\ll
 \frac1{\delta^{1/2}\theta x^\theta\log X}}
 \qquad(1\le x\le G).
 \tag{S2-J}
\]

Put `L=log G` and assume `L>=2`, as is harmless after increasing the final
large-parameter threshold.  The low mass does not require differentiating
`J`.  Choose `theta=1/L`.  Since `1<=x<=G` implies
`x^(-theta)>=G^(-theta)=exp(-1)`, positivity gives

\[
 \int_1^G|g(x)|^2\,dx
 \le eJ(1,1/L)
 \ll\frac{L}{\delta^{1/2}\log X}.
 \tag{S2-low-g}
\]

For the tail, use `J` only at the endpoint `x=G`; this is important because
the proved uniform estimate is not asserted for `x>G`.  Tonelli and
nonnegativity give

\[
 \int_0^{1/2}\theta J(G,\theta)\,d\theta
 =\int_G^\infty |g(x)|^2 K(\log x)\,dx,
 \qquad
 K(v)=\int_0^{1/2}\theta e^{-v\theta}\,d\theta.
\]

For `v>0`, direct integration gives

\[
 K(v)=\frac{1-e^{-v/2}(1+v/2)}{v^2}.
\]

The function `(1+r)exp(-r)` decreases for `r>=0`.  Hence, for `v>=2`,

\[
 K(v)\ge \frac{1-2/e}{v^2},
 \qquad 1-2/e>0.
\]

On the other hand (S2-J) gives

\[
 \int_0^{1/2}\theta J(G,\theta)\,d\theta
 \ll \frac1{\delta^{1/2}\log X}
       \int_0^{1/2}G^{-\theta}\,d\theta
 \le \frac1{\delta^{1/2}L\log X}.
\]

Combining these two inequalities yields

\[
 \int_G^\infty\frac{|g(x)|^2}{\log^2x}\,dx
 \ll\frac1{\delta^{1/2}L\log X}.
 \tag{S2-high-g}
\]

Finally S1 says that the inverse unitary Fourier transform of `F` is

\[
 f(y)=\tfrac12z^{1/2}\phi(1)\phi(0)-z^{-1/2}g(e^y),
 \qquad z=e^{-y-i(\pi/2-\delta)}.
\]

For real `F`, `f(-y)=conj(f(y))`, hence `|f(-y)|=|f(y)|`.  To match the
normalization used by the existing Mathlib `L2` Fourier operator, write

\[
 (\mathcal F_{\rm ml}F)(w)
 =\int_{\mathbb R}F(t)e^{-2\pi itw}\,dt
 =\sqrt{2\pi}\,f(2\pi w).
\]

The already proved rectangular-multiplier inequality, followed by
`y=2*pi*w` and the reality symmetry, therefore gives the exact safe bound

\[
 \int_{\mathbb R}\left|\int_t^{t+h}F(u)\,du\right|^2dt
 \le 2h^2\int_0^L|f(y)|^2dy
    +32\pi^2\int_L^\infty\frac{|f(y)|^2}{y^2}dy,
 \qquad L=\frac{2\pi}{h}.
 \tag{S2-Plancherel}
\]

Under `y=log x`, the two nonconstant pieces are precisely
(S2-low-g) and (S2-high-g).  The residue pieces use only
`phi(0)=O(X)` and `phi(1)=O(log X)`.  More explicitly, if
`B=|phi(1)phi(0)|`, then

\[
 |R(y)|^2=\frac14e^{-y}B^2,
 \quad
 \int_0^L|R(y)|^2dy\le\frac14B^2,
 \quad
 \int_L^\infty\frac{|R(y)|^2}{y^2}dy
 \le\frac{B^2}{4e^L L^2}.
\]

The coefficient bound `|beta_n|<=1` gives
`B<=X(1+log X)`.  Since `X<=delta^(-c)`, both residue contributions are
absorbed by the strict power gap `1/2-2c>0` (in particular by `c<1/8`).
Using `|R+N|^2<=2|R|^2+2|N|^2`, (S2-low-g), and (S2-high-g), one obtains

\[
 \int_{\mathbb R}\left|\int_t^{t+h}F(u)\,du\right|^2dt
 \ll \frac1{\delta^{1/2}L\log X},
 \qquad L=a\log X,
\]

which is S2.  This normalization records the otherwise easy-to-miss
`2*pi` conversion rather than silently identifying angular and Mathlib
frequencies.

The first two exact S2 inputs are now checked independently in Lean:

* `SelbergEulerPowerSum.lean` proves (S2-Euler) with an explicit constant
  satisfying `|K(theta)| <= 1` and a nonnegative remainder bounded by
  `(N+1)^(theta-1)`;
* `SelbergOffDiagonalArithmetic.lean` proves the rational-square gap and
  the residue-class harmonic-tail estimate used in (S2-offdiagonal).
* `SelbergGaussianHarmonicSum.lean` proves the two damped sums required
  after that residue-class estimate:
  \[
   \sum_{m\ge1}\frac{e^{-am^2}}m\le\log(2/a),\qquad
   \sum_{m\ge1}\frac{\log(mX)e^{-am^2}}m
   \le(\log X+\log(1/a))\log(2/a)+2
  \]
  for `0<a<=1`.  For the actual parameter, which need not be at most one,
  the proved interface uses `min(a,1)` and Gaussian monotonicity; no hidden
  `a<=1` assumption is exported to the outer four-variable sum.
* `SelbergOffDiagonalOuterSum.lean` performs the outer four finite sums
  without losing an extra power of `X`.  If `L` and `W` are the uniform
  one-log and two-log local bounds, respectively, it proves
  \[
   \mathrm{Outer}\le
   X^4(1+\log X)L+X^2(1+\log X)^2W.
  \]
* `SelbergOffDiagonalParameter.lean` proves the non-asymptotic uniform
  parameter bridge
  \[
   \frac{\delta}{X^2}\le
   \min\!\left(\pi\sin\delta\,\frac{\kappa^2}{\lambda^2},1\right),
  \]
  and therefore replaces the varying local logarithms by
  `log(2*X^2/delta)` and `log(X^2/delta)`.  It also instantiates both
  Gaussian `tsum` estimates and the full fixed-residue-class damped bracket
  uniformly in `kappa,lambda`.
* `SelbergOscillatoryGaussian.lean` proves the improper oscillatory integral
  by direct integration by parts.  Its usable theorem retains the necessary
  Gaussian factor and is slightly stronger than (8.10):
  \[
   \left|\int_x^\infty u^{-\theta}e^{(-P+iQ)u^2}\,du\right|
   \le \frac{2e^{-Px^2}x^{-\theta-1}}Q.
  \]
  An undamped corollary is exported only for convenience and is not used in
  the off-diagonal summation.
* `SelbergOffDiagonalGapReindex.lean` proves the exact admissible range
  `1 <= n <= floor((K-1)/d)`, the residue bounds `1 <= r <= d`, the
  order-reversing finite-sum identity in (S2-gap-class), its reciprocal-sum
  bound, and `log(m*X^2) <= 2*log(m*X)` for `m,X >= 1`.
* `SelbergOffDiagonalFixedSide.lean` keeps the exterior
  `1/(lambda*nu)` coefficient, proves its pointwise conversion through the
  rational-square gap, sums the actual finite admissible `n`-range, and
  obtains (S2-fixed-side) with explicit factor `2` and no asymptotic
  placeholder.  It also sums this bound over every `m >= 1`, proving
  summability of the original fixed-side square sum rather than merely of
  its Gaussian majorant.

For the two ordered sides, write

\[
 B_{\kappa,\lambda;\mu,\nu}
 =L_{\kappa,\lambda}
   +(\lambda\mu)^{-1}W_{\kappa,\lambda}.
\]

The proved fixed-side estimate is

\[
 2\frac{\lambda}{\kappa}B_{\kappa,\lambda;\mu,\nu}.
\]

The reverse side is obtained by the exact involution
`(m,kappa,lambda) <-> (n,mu,nu)` and is therefore

\[
 2\frac{\nu}{\mu}
 \{L_{\mu,\nu}+(\nu\kappa)^{-1}W_{\mu,\nu}\}.
\]

When all four mollifier indices range over the same finite interval, the
second fourfold sum is exactly the first after renaming
`kappa <-> mu` and `lambda <-> nu`.  Hence, once the local Gaussian sums are
replaced by uniform bounds `L,W`, the full two-sided square-gap sum is at
most

\[
 4\,\mathrm{Outer}(X,L,W).
 \tag{S2-two-sides}
\]

For `0 <= delta <= 1`,
`cos(delta) >= 1-delta^2/2 >= 1/2`; together with `pi >= 2`, this gives
`pi*cos(delta) >= 1` and hence no parameter loss from
`1/(pi*cos(delta))`.  Thus the factor `2` in the oscillatory integral and
(S2-two-sides) give the safe explicit multiplier `8` in front of the
already proved outer majorant.

`SelbergOffDiagonalTwoSides.lean` now verifies this entire interface.  In
particular, it does not stop at an abstract outer majorant: it defines the
two fourfold sums of the original fixed-side infinite sums, proves the
reverse sum is the exact swapped copy of the positive sum, instantiates the
uniform Gaussian bounds, proves the full two-sided square-gap sum is at most
`4*Outer`, and combines it with the oscillatory prefactor to obtain the
explicit multiplier `8` above.  All logarithmic factors remain displayed
as `selbergOffDiagonalUniformL/W`; no power absorption is hidden here.

The diagonal kernel is now closed through its integrated Euler expansion.
`SelbergEulerPowerFloor.lean` proves, for every real `z>=1`,

\[
 A_\theta(z)=\frac{z^\theta+K(\theta)}\theta+E_\theta(z),
 \qquad |E_\theta(z)|\le z^{\theta-1},
\]

with constant one rather than an avoidable factor two.  The scalar Gaussian,
weighted-Gaussian, and logarithmic-tail modules then prove the exact complete
integrals, the two low-interval bounds, and

\[
 \int_a^\infty \frac{e^{-y^2}}y\,dy
 \le \frac12\log(1+a^{-2})\le\log(2+a^{-2}).
\]

`SelbergDiagonalKernelIntegral.lean` preserves the signed Euler constant term
and obtains

\[
 D_{\eta,x,\theta}=M_{\eta,x,\theta}
   -C_{\eta,x,\theta}+R_{\eta,x,\theta},
\]

where `M` is the two-term Titchmarsh main expression,

\[
 |C_{\eta,x,\theta}|\le
 3\frac{x^{1-\theta}}\theta,
 \qquad
 |R_{\eta,x,\theta}|\le
 x^{1-\theta}\log(2+\eta^{-1}).
\]

No absolute value is taken before the signed `K(theta)` contribution has been
identified.  `SelbergDiagonalTermSubstitution.lean` verifies the exact
one-term change of variables, including

\[
 (\sqrt\eta\,r)^{\theta-1}
 =\eta^{(\theta-1)/2}r^{\theta-1},
\]

and `SelbergDiagonalTonelliReindex.lean` proves the no-off-by-one identity

\[
 \sum_{n\ge0}{\bf1}_{n+1\le z}(n+1)^{\theta-1}=A_\theta(z).
\]

`SelbergDiagonalTonelliReindex.lean` now also closes the measure-theoretic
bridge.  It replaces every open tail by the a.e.-equal closed tail, proves
finite support of the cutoff series at each height, proves nonnegativity and
integrability of every summand, and applies dominated Tonelli with the
integrable floor kernel itself as the summed bound.  Consequently

\[
 \sum_{r\ge1}\int_x^\infty e^{-\eta r^2u^2}u^{-\theta}\,du
 =D_{\eta,x,\theta}
\]

is now a proved `HasSum` and `tsum` identity, not merely a formal exchange.
`SelbergDiagonalArithmeticMain.lean` has begun the finite arithmetic
assembly: it keeps the two signed contributions as the exact linear
combination of `S(0)` and `S(theta)` and inserts the already proved S-arith
bounds simultaneously.  The remaining diagonal interface is the explicit
four-variable termwise identification with that linear combination, followed
by the parameter absorption and the rectangular Plancherel assembly.

For an integer Lean cutoff, `X = delta^(-c)` will be replaced by the
stable interface

\[
 X\le\delta^{-c}\le 2X,
\]

once `delta` is sufficiently small.  All power absorption lemmas are to be
proved explicitly from this interface; no asymptotic parameter relation is
to be introduced as an axiom.

### S3. Global square mass and absolute sliding mass

This step does **not** follow by putting `x=delta^(-2)` into the proved
`J(x,theta)` estimate: that estimate only has the uniform base-point range
`x<=X^a`.  Fortunately no such extension is needed.  The low mass uses only
`J(1,theta)`, and the remaining tail is bounded directly from the absolutely
convergent Gaussian theta series.

Put

\[
 D=\delta^{-1/2},\qquad G=\delta^{-2},\qquad
 L_\delta=\log(1/\delta),\qquad \log G=2L_\delta.
\]

Assume `log G>=2`, which is an honest eventual small-`delta` condition, and
choose

\[
 \theta=\frac1{\log G}\le\frac12.
\]

If

\[
 q(u)=|g(u)|^2,
\]

then positivity and `u^(-theta)>=G^(-theta)=e^(-1)` on `1<=u<=G`
give

\[
 \int_1^Gq(u)\,du
 \le e\int_1^G u^{-\theta}q(u)\,du
 \le eJ(1,\theta).
\]

The proved S2 estimate is applicable at `x=1`, because
`1<=1<=X^a`.  Consequently

\[
 \boxed{
 \int_1^Gq(u)\,du
 \ll D\frac{\log G}{\log X}
 =2D\frac{L_\delta}{\log X}.}
 \tag{S3-low}
\]

This is the precise correction to the tempting but unnecessary use of
`J(G,theta)`.  It also avoids differentiating `J`.

For the direct tail, write

\[
 B=\frac{\delta}{2X^2}.
\]

The elementary sine bound already used in S2 says
`delta<=2*pi*sin(delta)`.  Hence, for `u>=1`, every positive theta term with
`1<=kappa,lambda<=X` and `n>=1` satisfies

\[
 \left|\exp\!\left(-\pi\sin\delta
       \left(\frac{n\kappa}{\lambda}\right)^2u^2
       -i\,\cdots\right)\right|
 \le e^{-Bn^2u^2}\le e^{-Bnu^2}.
 \tag{S3-ray}
\]

Moreover `|beta_n|<=1` and the harmonic-sum estimate give

\[
 \sum_{\kappa,\lambda\le X}
   \frac{|\beta_\kappa\beta_\lambda|}{\lambda}
 \le X(1+\log X).
 \tag{S3-coeff}
\]

For `u>=G`, put `z=Bu^2`.  From `X<=delta^(-c)`, `c<1/8`, and
`0<delta<=1`,

\[
 z\ge BG^2=\frac1{2X^2\delta^3}
 \ge\frac12\delta^{-3+2c}\ge\frac12.
\]

The shifted theta series is therefore uniformly geometric:

\[
 \sum_{n\ge1}e^{-Bn^2u^2}
 \le\frac{e^{-Bu^2}}{1-e^{-Bu^2}}
 \le\frac{e^{-Bu^2}}{1-e^{-1/2}}.
\]

Combining this with (S3-coeff), for an absolute constant `C_0`,

\[
 q(u)\le C_0X^2(1+\log X)^2e^{-2Bu^2}.
 \tag{S3-point-tail}
\]

Now split one Gaussian factor at the endpoint and integrate the other over
the whole positive ray:

\[
 \begin{aligned}
 \int_G^\infty q(u)\,du
 &\le C_0X^2(1+\log X)^2e^{-BG^2}
       \int_0^\infty e^{-Bu^2}\,du\\
 &=C_0\sqrt{\frac\pi2}\,
       D X^3(1+\log X)^2e^{-BG^2}.
 \end{aligned}
\]

The elementary exponential estimate `e^(-z)<=2/z^2` yields

\[
 e^{-BG^2}\le 8X^4\delta^6.
\]

Since `1+log X<=X`,

\[
 \int_G^\infty q(u)\,du
 \ll D X^9\delta^6
 \le D\delta^{6-9c}
 \ll D.
 \tag{S3-tail-raw}
\]

The endpoint assumptions force `c>0` and `delta<1`; taking logarithms in
`X<=delta^(-c)` gives

\[
 \log X\le cL_\delta<L_\delta.
\]

Thus the last `D` is absorbed by `D*L_delta/log X`, and

\[
 \boxed{
 \int_G^\infty q(u)\,du
 \ll D\frac{L_\delta}{\log X}.}
 \tag{S3-tail}
\]

Under `y=log u`, the exact S1 mass bridge identifies (S3-low) and
(S3-tail) with the full positive-frequency square mass of the nonconstant
inverse Fourier kernel.  The residue is even easier: the already proved
pointwise estimate

\[
 |R(y)|^2\le D e^{-y}
\]

gives `integral_0^infinity |R(y)|^2 dy<=D`, which is absorbed by the same
target.  Applying `|R+N|^2<=2|R|^2+2|N|^2`, reflecting by the proved reality
symmetry, transporting `y=2*pi*w`, and finally applying Plancherel gives

\[
 \boxed{
 \int_{\mathbb R}|F_{\delta,X}(t)|^2dt
 \ll \frac{\log(1/\delta)}{\delta^{1/2}\log X}.}
 \tag{S3a}
\]

There is no pointwise inverse-Fourier assumption in this last step.  In
Mathlib's `L2` convention it is exactly the chain

\[
 \int|F|^2=\|F\|_2^2=\|\mathcal F_{\rm ml}F\|_2^2
 =\int|\mathcal F_{\rm ml}F|^2,
\]

using `MeasureTheory.Lp.norm_fourier_eq`; the a.e. compatibility theorem
then inserts the explicit S1 kernel.

Finally, for every `h>=0`, pointwise Cauchy--Schwarz gives

\[
 \left(\int_t^{t+h}|F(u)|\,du\right)^2
 \le h\int_t^{t+h}|F(u)|^2\,du.
\]

Tonelli is applicable because the integrand is nonnegative.  For fixed
`u`, the set of starting points satisfying `t<=u<=t+h` is `[u-h,u]`, of
measure `h`.  Hence

\[
 \int_{\mathbb R}\int_t^{t+h}|F(u)|^2\,du\,dt
 =h\int_{\mathbb R}|F(u)|^2\,du,
\]

and therefore

\[
 \boxed{
 \int_{\mathbb R}
   \left(\int_t^{t+h}|F_{\delta,X}(u)|\,du\right)^2dt
 \ll \frac{h^2\log(1/\delta)}{\delta^{1/2}\log X}.}
 \tag{S3b}
\]

Thus S3 is closed at paper level.  Its Lean decomposition is:

1. a `G=delta^(-2)` low-mass specialization of the existing
   `J(1,theta)` bridge;
2. a pointwise physical-theta Gaussian tail bound and its integrated tail;
3. positive explicit-kernel mass assembly and exact `2*pi`/Plancherel
   transport;
4. an abstract nonnegative sliding-window Cauchy--Schwarz--Tonelli theorem
   proving the factor `h^2`.

All four Lean layers are now complete.  In particular,
`SelbergGlobalLowMass.lean` instantiates only `J(1,theta)` at
`G=delta^(-2)`, while `SelbergPhysicalThetaGaussianTail.lean` proves the
single-term decay, the uniform theta-ray bound, the two finite mollifier
sums, and the integrated tail.  For the formal tail integration it uses the
equally valid simplification `u^2>=G*u` on `u>=G`; this gives the explicit raw
bound

\[
 \int_G^\infty q(u)\,du
 \le \frac{64X^4}{B^2G^3}=256X^8\delta^4
 \le256\delta^{-1/2}.
\]

The last inequality reuses the already proved `X^4<=delta^(-1/2)` twice.
This avoids square-root algebra from the complete Gaussian integral while
retaining more than enough strict power saving.  The new
`SelbergGlobalFourierMass.lean` then assembles the residue and nonconstant
positive half-line masses, proves the exact `y=2*pi*w` transport, reflects
the scalar Fourier energy by reality, and applies Mathlib's `L2` Plancherel
isometry.  Thus (S3a) is complete in Lean.  Finally,
`MathlibAux/AbsoluteSlidingWindowL2.lean` proves the abstract exact-constant
bound by setwise Cauchy--Schwarz and convolution with the backward rectangular
kernel, whose integral is exactly `H`.  The public
`SelbergSlidingAbsoluteSecondMoment.lean` specializes this result to (S3a).
Consequently (S3b), and hence all of S3, is now complete in Lean.

### S4. First absolute moment

This step deliberately uses the auxiliary holomorphic product

\[
 G_X(s)=\zeta(s)\psi_X(s)^2,
\]

not the reflected Mellin product
`zeta(s) psi_X(s) psi_X(1-s)` used in S1.  The two complex values need not
agree on the critical line.  What S4 needs is only their common modulus:
the tapered coefficients are real, so

\[
 |G_X(\tfrac12+it)|
 =|\zeta(\tfrac12+it)|\,|\psi_X(\tfrac12+it)|^2.
\]

Together with the positive archimedean factor this is now recorded exactly
in Lean by
`abs_selbergCompletedMollifiedF_eq_gamma_tilt_mul_abs_sqrtZeta`.
For `delta <= 1/T`, shift the contour for `G_X` as in §§10.20--10.21.
Its ordinary Dirichlet series on `Re(s)=2` has constant coefficient one and
the remaining coefficients satisfy a divisor majorant.  This yields

\[
 \boxed{
 \int_0^T |F_{\delta,X}(t)|\,dt\gg T^{3/4},}
 \tag{S4a}
\]

and hence

\[
 \boxed{
 \int_0^T\int_t^{t+h}|F_{\delta,X}(u)|\,du\,dt
 \gg hT^{3/4}.}
 \tag{S4b}
\]

### S5. Good-window measure

Let

\[
 E=\left\{t\in(0,T):
   \left|\int_t^{t+h}F(u)\,du\right|
   <\int_t^{t+h}|F(u)|\,du\right\}.
\]

Using S2--S4 and Cauchy--Schwarz gives

\[
 m(E)^{1/2}
 \ge C_1 c^{1/2}T^{1/2}-C_2(ac)^{1/2}T^{1/2}.
\]

After `c` is fixed, choose `a` so that the second constant is at most half
the first.  Then

\[
 \boxed{m(E)\gg T.}
 \tag{S5}
\]

Every `t in E` forces a sign change in `(t,t+h)`.  Partitioning `(0,T)` into
intervals of length `h`, and allowing each zero to be charged at most twice,
gives

\[
 N_{0,\mathrm{odd}}(T)\gg \frac{T}{h}\gg T\log T.
\]

The last packing step is already represented, in a dyadic version, by
`HardyTheorem/SelbergPacking.lean`.

## 5. What should be reused and what should be retired

Reuse:

* the square-root-zeta local and multiplicative coefficient library;
* completed-zeta Fourier representation and sign transfer;
* abstract sliding-integral Fourier/Plancherel lemmas;
* the good-window sign-change and logarithmic packing bridge.

Do not use as the main Selberg input:

* the length-`T^3` linear Möbius twisted moment;
* `MWKF(3)`;
* the current first-zeta approximation with cutoff `floor(4*T)` followed by
  a frequency-by-frequency absolute gap sum.

The last route is not logically false, but it discards the exact completed
Fourier structure which makes Selberg's proof close and creates arithmetic
budgets that the classical proof never needs.

## 6. Admission rule for Lean

Lean work begins only after S1--S5 have been rewritten as a continuous paper
proof with:

* one Fourier normalization;
* explicit domains of absolute convergence;
* the full proof of the `S(theta)` estimate;
* an independent check of every use of `(a+2)c <= 1/4`;
* a final statement counting odd-multiplicity zeros, not merely distinct
  zero ordinates.

The current honest repository status is:

```text
Hardy                         proved
Hardy--Littlewood c*T         proved
Selberg c*T*log T             S1--S3 proved; S4 analytic gates proved, contour assembly remains
T^3 linear Möbius moment      separate open long-mollifier problem
Conrey two fifths             not yet formalized
```

The abstract S5 measure argument, logarithmic packing, and transfer to
odd-multiplicity critical-line zeros already exist in
`SelbergGoodWindowMeasure.lean` and `SelbergPacking.lean`.  They still need
new S2--S4 hypotheses instantiated for `selbergCompletedMollifiedF`; the old
one-sided-zeta bad-set modules are not those instantiations.

## 7. Exact derivation of S1

This subsection closes S1 at paper level.  It uses the unitary convention

\[
 \widehat f(t)=\frac1{\sqrt{2\pi}}
   \int_{\mathbb R}f(y)e^{ity}\,dy.
\]

Put

\[
 \gamma(s)=\pi^{-s/2}\Gamma(s/2),\qquad
 \vartheta=\frac\pi4-\frac\delta2,
 \qquad 0<\delta<\frac\pi2.
\]

For `c > 1` and initially for a complex `z` with
`|arg z| < pi/4`, use the principal power and define

\[
 \Phi(z)=\frac1{4\pi i}\int_{(c)}
   \gamma(s)\zeta(s)\psi_X(s)\psi_X(1-s)z^s\,ds.
 \tag{7.1}
\]

The mollifier factors are finite Dirichlet polynomials.  Stirling gives
`|Gamma((sigma+it)/2)|` a factor `exp(-pi|t|/4)`, while the principal
power contributes `exp(-t arg z)`.  Thus the horizontal sides vanish when
the contour is shifted to `Re s = 1/2`; the strict angular inequality gives
exponential decay at both ends.  The only crossed pole is the simple pole of
zeta at one.  Consequently

\[
 \Phi(z)=\frac12z\psi_X(1)\psi_X(0)
  -\frac{z^{1/2}}{2\pi}\int_{\mathbb R}
    \frac{\Xi(t)}{t^2+1/4}
    |\psi_X(\tfrac12+it)|^2z^{it}\,dt.
 \tag{7.2}
\]

Here

\[
 \xi(s)=\frac12s(s-1)\gamma(s)\zeta(s),
 \qquad \Xi(t)=\xi(\tfrac12+it).
\]

Indeed, on the critical line `psi_X(1-s)` is the complex conjugate of
`psi_X(s)`, and

\[
 s(s-1)=-(t^2+1/4),
\]

which accounts for both the minus sign and the factor `1/(2*pi)` in
(7.2).  This also records the harmless global sign between `Xi` and the
repository's real completed-zeta restriction.

On `Re s = c`, all three Dirichlet series may be expanded absolutely.  The
inverse Mellin formula for the Gaussian gives

\[
 \begin{aligned}
 \Phi(z)
 &=\sum_{n\ge1}\sum_{\mu<X}\sum_{\nu<X}
   \frac{\beta_\mu\beta_\nu}{\nu}
   \frac1{4\pi i}\int_{(c)}
    \Gamma(s/2)
    \left(\frac{n\mu\sqrt\pi}{z\nu}\right)^{-s}ds\\
 &=\sum_{n\ge1}\sum_{\mu<X}\sum_{\nu<X}
   \frac{\beta_\mu\beta_\nu}{\nu}
   \exp\!\left(-\frac{\pi n^2\mu^2}{z^2\nu^2}\right).
 \end{aligned}
 \tag{7.3}
\]

Now set

\[
 z=z(y)=e^{-i\vartheta-y}.
\]

Since `0 < vartheta < pi/4`, all preceding convergence statements remain
valid.  Define

\[
 \begin{aligned}
 f_{\delta,X}(y)
 ={}&\frac12z(y)^{1/2}\psi_X(1)\psi_X(0)\\
 &-z(y)^{-1/2}
 \sum_{n\ge1}\sum_{\mu<X}\sum_{\nu<X}
   \frac{\beta_\mu\beta_\nu}{\nu}
   \exp\!\left(-\frac{\pi n^2\mu^2}
                         {z(y)^2\nu^2}\right).
 \end{aligned}
 \tag{7.4}
\]

Because

\[
 z(y)^{it}=e^{\vartheta t}e^{-iyt},
\]

equations (7.2)--(7.4) give the exact identity

\[
 f_{\delta,X}(y)
 =\frac1{2\pi}\int_{\mathbb R}
   \frac{\Xi(t)}{t^2+1/4}
   |\psi_X(\tfrac12+it)|^2
   e^{\vartheta t}e^{-iyt}\,dt.
 \tag{7.5}
\]

Thus `f` is the inverse unitary Fourier transform of `F`, and Fourier
inversion gives the S1 pair.  Absolute convergence in (7.5) follows directly
from the remaining exponential `exp(-delta*t/2)` at positive infinity and
the stronger gamma decay at negative infinity; the finite mollifier has at
most polynomial growth in `t`.

For Lean, the most economical definition is not to introduce a second xi
function.  On the critical line,

\[
 \frac{\Xi(t)}{t^2+1/4}
 =-\frac12\,\Lambda(\tfrac12+it),
\]

so `F` can be defined directly from `hardyCompletedCriticalLine`, multiplied
by the nonnegative mollifier square and the positive exponential tilt.  The
fixed factor `-1/2` reverses sign orientation but not sign-change locations.

### 7.1 Exact vertical-Gamma bound needed by the formal contour shift

The remaining analytic S1 gate can be reduced to a ray-rotation estimate
which is both stronger and more directly usable than invoking a full
Stirling expansion.  If `sigma>0` and `0<eta<pi/2`, rotation of the Gamma
integral from the positive real ray to angle `sign(t)*eta` gives

\[
 \boxed{
 |\Gamma(\sigma+it)|
 \le \Gamma(\sigma)(\cos\eta)^{-\sigma}e^{-\eta|t|}.}
 \tag{7.6}
\]

For `t>=0`, parameterizing the rotated ray by `z=r*exp(i*eta)` gives the
factor `exp(i*eta*(sigma+i*t))`, whose norm is `exp(-eta*t)`, and

\[
 \int_0^\infty r^{\sigma-1}e^{-r\cos\eta}\,dr
 =(\cos\eta)^{-\sigma}\Gamma(\sigma).
\]

For `t<=0`, rotate through angle `-eta`; the same calculation gives
`exp(-eta*|t|)`.  The circular connecting arcs vanish at zero and infinity
because `sigma>0` and `cos eta>0`.

Apply (7.6) to `Gamma(s/2)` with

\[
 \eta=\frac\pi2-\frac\delta2.

\]

Then its positive-height decay is
`exp(-(pi/4-delta/4)*t)`.  The principal power `z(y)^s`, with
`arg z=-(pi/4-delta/2)`, costs
`exp((pi/4-delta/2)*t)`, leaving the strict margin
`exp(-delta*t/4)`.  At negative height both factors decay.  The finite
mollifier is bounded by a fixed polynomial, and the repository already has
polynomial growth of zeta on fixed vertical strips.  Thus (7.6) supplies
both absolute convergence on the vertical lines and vanishing of the two
horizontal sides.

The formalized S1 layer now includes the principal-power tilt `z^(i*t)`,
the exact identity `z^(-2)=exp(2*y)*(sin delta+i*cos delta)`, positivity of
both phase components, absolute convergence of every positive-index
Gaussian theta series, and the justified interchange with the two finite
mollifier sums.  It also includes a proof of (7.6) by a finite logarithmic
rectangle, vanishing of both vertical sides, the exact substitution back to
Euler's Gamma integral, and conjugation for negative height.  Applied to
`Gamma((sigma+i*t)/2)`, the formal bound absorbs the Fourier tilt and leaves
exactly `exp(-delta*|t|/4)` on the whole real line.

The meromorphic part of S1 is now also closed.  The formal proof constructs
the analytic pole unit `(s-1)*zeta(s)`, removes the pole with `dslope`, and
proves on every finite rectangle from `Re(s)=1/2` to `Re(s)=2` that the raw
integrand has boundary integral

\[
 2\pi i\,z\psi_X(1)\psi_X(0).
\]

The horizontal sides tend to zero by the preceding exponential estimate.
The same estimate, with the polynomial absorbed into half of the exponential
margin, proves absolute integrability of both vertical lines.  Passing to
infinite height gives the exact identity

\[
 \int_{\mathbb R}I(2+it)\,dt-
 \int_{\mathbb R}I(\tfrac12+it)\,dt
 =2\pi z\psi_X(1)\psi_X(0),
\]

and multiplication by `1/(4*pi)` gives precisely half the residue.  This
proof is independent of Zeta23.

That last S1 obligation is now closed as well.  The complex Gaussian inverse
Mellin formula below is formalized together with its exact vertical `L1`
norm; the resulting `n^(-2)` majorant justifies Tonelli on the right line.
`HardyTheorem.selbergS1_inverseFourier_identity` combines that evaluation,
the infinite contour shift, and the critical-line algebra into (7.5), with
no admissions and no Zeta23 dependency.

### 7.2 Complex Gaussian inverse Mellin lemma

There is a branch issue in (7.3) which should not be suppressed.  The
Gaussian parameter

\[
 w=\frac{\pi n^2\mu^2}{z^2\nu^2}
\]

is not positive real after `z=exp(-y-i*vartheta)`; it lies in the first
quadrant.  Write `w=r*exp(i*phi)`, where `r>0` and
`0<phi=pi/2-delta<pi/2`.  For `u=c/2+it/2`, rotate Euler's Gamma ray from
the positive axis to angle `phi`:

\[
 \Gamma(u)=e^{i\phi u}
   \int_0^\infty e^{-e^{i\phi}v}v^{u-1}\,dv.
 \tag{7.7}
\]

Because the principal logarithm gives
`w^{-u}=r^{-u}e^{-i*phi*u}`, the two phase factors cancel exactly.  Hence

\[
 \frac1{2\pi}\int_{\mathbb R}\Gamma(c/2+it/2)
       w^{-(c/2+it/2)}\,\frac{dt}{2}
 =\frac1{2\pi}\int_{\mathbb R}
   \mathcal M(e^{-e^{i\phi}v})(c/2+iu)
   r^{-(c/2+iu)}\,du
 =e^{-e^{i\phi}r}=e^{-w}.
 \tag{7.8}
\]

Equivalently, after restoring the original variable `s=c+it`,

\[
 \boxed{\frac1{4\pi}\int_{\mathbb R}
   \Gamma((c+it)/2)w^{-(c+it)/2}\,dt=e^{-w}.}
 \tag{7.9}
\]

The convergence hypotheses are supplied by exactly the same rotated-Gamma
bound already used in the rectangle shift: choose a rotation angle strictly
between `phi` and `pi/2`; the residual exponential is
`exp(-(eta-phi)|t|/2)`.  Thus (7.9) reduces the complex case to Mathlib's
real-radius Mellin inversion without analytic-continuation shorthand.  In
the formal proof the phase must be cancelled before invoking Mellin
inversion; applying the real theorem directly to complex `w` would be
invalid.

## 8. Arithmetic derivation of (S-arith)

This subsection reduces (S-arith) to (S12), and proves the remaining gcd and
Euler-product algebra.  The contour proof of (S12) is isolated at the end.

Let

\[
 J_{1-\theta}(r)=(\mu * \operatorname{id}^{,1-\theta})(r).
\]

Then

\[
 q^{1-\theta}=\sum_{r\mid q}J_{1-\theta}(r),
 \qquad
 J_{1-\theta}(r)
 =r^{1-\theta}\prod_{p\mid r}(1-p^{\theta-1})\ge0.
 \tag{8.1}
\]

Inserting (8.1) into the definition of `S(theta)` and collecting the two
identical real factors gives

\[
 S(\theta)=\sum_{r<X^2}J_{1-\theta}(r)
 \left(
  \sum_{r\mid\kappa\nu}
   \frac{\beta_\kappa\beta_\nu}
        {\kappa^{1-\theta}\nu}
 \right)^2.
 \tag{8.2}
\]

For each `kappa`, uniquely write `kappa = d k` where every prime of `d`
divides `r` and `(k,r)=1`; similarly write `nu = d_1 l`.  The condition
`r | kappa*nu` is then exactly `r | d*d_1`.  Multiplicativity and the linear
taper give

\[
 \beta_{dk}=\frac{\alpha_d\alpha_k}{\log X}
             \log\frac{X}{dk}
\]

on the support.  Apply (S12) with exponent `theta` to the `k` sum and with
exponent zero to the `l` sum.  Since both logarithms are at most `log X`,

\[
 \left|\sum_{r\mid\kappa\nu}
   \frac{\beta_\kappa\beta_\nu}
        {\kappa^{1-\theta}\nu}\right|
 \ll \frac{X^\theta}{\log X}
 \prod_{p\mid r}\left(1+\frac1p\right)
 \sum_{r\mid dd_1}\frac{|\alpha_d\alpha_{d_1}|}{dd_1}.
 \tag{8.3}
\]

To prove (S13), let `alpha'_n` denote the nonnegative coefficients of
`sqrt(zeta(s))`.  The binomial Euler factors give
`|alpha_n| <= alpha'_n`, while

\[
 \sum_{dd_1=D}\alpha'_d\alpha'_{d_1}=1
\]

because the square of `sqrt(zeta)` is zeta.  Since `d,d_1` are supported on
the primes of `r`,

\[
 \begin{aligned}
 \sum_{r\mid dd_1}\frac{|\alpha_d\alpha_{d_1}|}{dd_1}
 &\le \sum_{\substack{r\mid D\\p\mid D\Rightarrow p\mid r}}\frac1D\\
 &=\frac1r\prod_{p\mid r}(1-p^{-1})^{-1}\\
 &\ll\frac1r\prod_{p\mid r}(1+p^{-1}).
 \end{aligned}
 \tag{8.4}
\]

The last implicit constant is absolute because

\[
 \prod_p\frac{(1-p^{-1})^{-1}}{1+p^{-1}}
 =\prod_p(1-p^{-2})^{-1}=\zeta(2).
\]

This S13 chain is now formalized without asymptotic hypotheses in
`SelbergSqrtZetaInverseMajorant.lean`, `SelbergS13DivisorPair.lean`,
`SelbergS13EulerProduct.lean`, and `SelbergS13AbsoluteBound.lean`.  In
particular, Lean verifies the concrete finite bound

\[
 \sum \frac{|\alpha_d\alpha_{d_1}|}{dd_1}
 \le \frac{2}{\rho}\prod_{p\mid\rho}(1+p^{-1})
\]

after grouping the admissible products as `D = rho*m`; the constant two is
obtained from the exact correction product and
`zeta(2) = pi^2/6 < 2`.

Combining (8.2)--(8.4), and using
`J_{1-theta}(r) <= r^(1-theta)`, gives

\[
 S(\theta)\ll \frac{X^{2\theta}}{\log^2X}
 \sum_{r<X^2}\frac1{r^{1+\theta}}
  \prod_{p\mid r}(1+p^{-1})^4.
 \tag{8.5}
\]

For every prime `p >= 2`, the elementary expansion gives the concrete bound

\[
 (1+p^{-1})^4
 =1+4p^{-1}+6p^{-2}+4p^{-3}+p^{-4}
 \le 1+9p^{-1}.
\]

Hence

\[
 \prod_{p\mid r}(1+p^{-1})^4
 \le \prod_{p\mid r}(1+9/p)
 =\sum_{d\mid r}\frac{9^{\omega(d)}\mu^2(d)}d.
\]

Consequently

\[
 \begin{aligned}
 \sum_{r\le Y}\frac1{r^{1+\theta}}
  \prod_{p\mid r}(1+p^{-1})^4
 &\le \sum_{d\le Y}\frac{C^{\omega(d)}\mu^2(d)}{d^{2+\theta}}
       \sum_{m\le Y/d}\frac1{m^{1+\theta}}\\
 &\ll \log(2Y),
 \end{aligned}
\]

uniformly for `0 <= theta <= 1/2`.  More explicitly, after writing `r=dm`
and dropping `theta` from the denominator,

\[
 \sum_{r\le Y}\frac1{r^{1+\theta}}
   \sum_{d\mid r}\frac{9^{\omega(d)}\mu^2(d)}d
 \le
 \left(\sum_{d\ge1}\frac{9^{\omega(d)}\mu^2(d)}{d^2}\right)
 \left(\sum_{m\le Y}\frac1m\right).
\]

The first factor is the convergent Euler product
`prod_p (1 + 9 / p^2)` (bounded, for example, by
`exp(9 * sum_p p^(-2))`), and the second is at most `1 + log Y`.
With `Y = X^2`, (8.5) therefore proves (S-arith), including the endpoint
`theta = 0`, with no hidden loss of a logarithm.

### 8.1 Contour proof required for (S12)

Put `Y=X/d`.  If `Y<2`, (S12) is immediate.  Otherwise Perron's identity
for the logarithmic weight gives

\[
 \sum_{\substack{k<Y\\(k,r)=1}}
  \frac{\alpha_k}{k^{1-\theta}}\log\frac Yk
 =\frac1{2\pi i}\int_{(1)}
   \frac{Y^s}{s^2}
   \prod_{p\mid r}(1-p^{-(1-\theta+s)})^{-1/2}
   \frac{ds}{\sqrt{\zeta(1-\theta+s)}}.
 \tag{8.6}
\]

The branch is fixed first in `Re(1-theta+s)>1` by the Euler product.  The
classical zero-free line continues it to the contour used below, with the
zero of `1/sqrt(zeta)` at the pole of zeta treated by a slit/indentation.

If `theta >= 1/log Y`, move (8.6) to `Re s = theta`.  On this line,

\[
 |\zeta(1+it)|^{-1/2}\ll |t|^{1/2}.
\]

This is the square root of (Z1), not a consequence of nonvanishing alone;
near zero it is interpreted using the simple pole at `t=0`.
The finite Euler product is

\[
 \ll\prod_{p\mid r}(1+p^{-1})^{1/2}.
\]

Integration of `|t|^(1/2)/(theta^2+t^2)` yields

\[
 \ll Y^\theta\theta^{-1/2}
 \prod_{p\mid r}(1+p^{-1})^{1/2}
 \le Y^\theta(\log Y)^{1/2}
 \prod_{p\mid r}(1+p^{-1})^{1/2}.
\]

If `0 <= theta < 1/log Y`, use the same displaced contour but detour to the
right of the circle `|s|=2/log Y`.  On the circle `|Y^s|<=e^2`, while the
pole of zeta gives

\[
 |\zeta(1-\theta+s)|^{1/2}\gg(\log Y)^{1/2}.
\]

The circular arc and the remaining vertical pieces are each

\[
 \ll (\log Y)^{1/2}
 \prod_{p\mid r}(1+p^{-1})^{1/2}.
\]

This is (S12) in the second range, since `Y^theta=O(1)`.  The two cases prove
(S12) uniformly.  A fully formal version must replace the shorthand
continuation around the square-root branch point by an explicit slit domain;
this is the only branch-sensitive step in S2.

For formalization there is a cleaner equivalent route which removes that
branch-sensitive step entirely.  Keep Perron's line inside absolute
convergence and put

\[
 \varepsilon=(\log Y)^{-1},\qquad \sigma=\theta+\varepsilon.
\]

Then the Dirichlet-series identity is literal on the whole contour and

\[
 1-\theta+\sigma+it=1+\varepsilon+it,
 \qquad Y^\sigma=eY^\theta.
\]

The uniform strip estimate

\[
 |\zeta(1+\varepsilon+it)|^{-1}\ll \varepsilon+|t|
\]

and the deleted Euler factors give

\[
 |B_r(1+\varepsilon+it)|
 \ll \sqrt{\varepsilon+|t|}
 \prod_{p\mid r}(1+p^{-1})^{1/2}.
\]

Finally, since `0 < epsilon <= sigma`, scaling `t = sigma u` yields

\[
 \int_{\mathbb R}
 \frac{\sqrt{\varepsilon+|t|}}{\sigma^2+t^2}\,dt
 \ll \sigma^{-1/2}.
\]

Thus

\[
 |S_{12}|\ll
 Y^\theta(\theta+(\log Y)^{-1})^{-1/2}
 \prod_{p\mid r}(1+p^{-1})^{1/2}
 \le
 Y^\theta\sqrt{\log Y}
 \prod_{p\mid r}(1+p^{-1})^{1/2}.
\]

This proves the same uniform S12 bound without a contour shift, indentation,
or a boundary square-root value.

### 8.2 Diagonal, off-diagonal, and the sliding bound

Write `x=e^y`.  Apart from the elementary residue term in (7.4), the Fourier
kernel is

\[
 g(x)=\sum_{n\ge1}\sum_{\mu,\nu<X}
  \frac{\beta_\mu\beta_\nu}{\nu}
  \exp\!\left(-\pi\frac{n^2\mu^2x^2}{\nu^2}
                    (\sin\delta+i\cos\delta)\right).
 \tag{8.7}
\]

For `0<theta<=1/2`, expand

\[
 J(x,\theta)=\int_x^\infty |g(u)|^2u^{-\theta}\,du.
\]

The diagonal condition is

\[
 \frac{m\kappa}{\lambda}=\frac{n\mu}{\nu}.
\]

Let `q=gcd(kappa*nu,lambda*mu)`, write
`kappa*nu=Aq`, `lambda*mu=Bq`, and `(A,B)=1`.  Then every diagonal
solution is `m=rB`, `n=rA`.  Hence its contribution is

\[
 \Sigma_1=
 \sum_{\kappa,\lambda,\mu,\nu<X}
  \frac{\beta_\kappa\beta_\lambda
        \beta_\mu\beta_\nu}{\lambda\nu}
  \sum_{r\ge1}\int_x^\infty
   \exp\!\left(-2\pi r^2
    \frac{\kappa^2\mu^2}{q^2}u^2\sin\delta\right)
   \frac{du}{u^\theta}.
 \tag{8.8}
\]

Euler summation of the `r` sum, followed by one integration in `u`, has two
main pieces: the first contains `S(0)` and the second contains `S(theta)`.
Using (S-arith), `sin(delta) asymp delta`, and `x<=G=X^a` gives

\[
 \Sigma_1\ll
 \frac1{\delta^{1/2}\theta x^\theta\log X},
 \tag{8.9}
\]

provided `(a+2)c<=1/4`.  The discarded Euler-summation endpoint is bounded
with `|beta_n|<=1`; this is the place where the stronger quarter-power room,
rather than only a half-power comparison of the two displayed main pieces,
is used.

For the off-diagonal put

\[
 P=\pi\left(\frac{m^2\kappa^2}{\lambda^2}
             +\frac{n^2\mu^2}{\nu^2}\right)\sin\delta,
 \quad
 Q=\pi\left|\frac{m^2\kappa^2}{\lambda^2}
             -\frac{n^2\mu^2}{\nu^2}\right|\cos\delta.
\]

The second mean-value theorem, applied to real and imaginary parts, gives

\[
 \left|\int_x^\infty e^{-Pu^2+iQu^2}\frac{du}{u^\theta}\right|
 \ll\frac{e^{-Px^2}}{x^\theta Q}.
 \tag{8.10}
\]

Factoring the difference of squares reduces the denominator to the integer
gap `|m*kappa*nu-n*lambda*mu|`.  On either side of the diagonal the elementary
harmonic estimate

\[
 \sum_{n<m\kappa\nu/(\lambda\mu)}
  \frac1{m\kappa\nu-n\lambda\mu}
 \ll 1+\frac{\log(mX)}{\lambda\mu}
\]

and the remaining Gaussian sums yield

\[
 \Sigma_2\ll \frac{X^4}{x^\theta}\log^2\frac1\delta.
 \tag{8.11}
\]

Because `c<1/8`, (8.11) is smaller by a fixed power of `delta` than (8.9)
as `delta` tends to zero.  Thus, uniformly for `1<=x<=G`,

\[
 \boxed{
 J(x,\theta)\ll
 \frac1{\delta^{1/2}\theta x^\theta\log X}.}
 \tag{8.12}
\]

Take, for example, `theta=1/4`.  Since
`-partial_x J(x,theta)=|g(x)|^2x^{-theta}`, integration by parts in (8.12)
gives

\[
 \int_1^G|g(x)|^2\,dx
 \ll\frac{\log G}{\delta^{1/2}\log X},
 \qquad
 \int_G^\infty\frac{|g(x)|^2}{\log^2x}\,dx
 \ll\frac1{\delta^{1/2}\log G\log X}.
 \tag{8.13}
\]

The elementary residue term in (7.4) obeys
`psi_X(0)=O(X)` and `psi_X(1)=O(log X)` and satisfies the same required
integrated bounds under `c<1/8`.

Finally the Fourier transform of an interval gives

\[
 \int_{\mathbb R}\left|\int_t^{t+h}F(u)\,du\right|^2dt
 \le 2h^2\int_0^{1/h}|f(y)|^2dy
     +8\int_{1/h}^\infty\frac{|f(y)|^2}{y^2}dy.
 \tag{8.14}
\]

Under `y=log x`, its split point is
`G=e^(1/h)=X^a`.  Inserting (8.13) into (8.14), and using
`h=1/(a log X)`, proves exactly (S2):

\[
 \int_{\mathbb R}\left|\int_t^{t+h}F(u)\,du\right|^2dt
 \ll\frac{h}{\delta^{1/2}\log X}.
\]

## 9. Paper derivation of S3 and S4

### 9.1 Global square mass

Plancherel applied to the exact pair (7.5) gives

\[
 \int_{\mathbb R}|F(t)|^2dt=\int_{\mathbb R}|f(y)|^2dy.
\]

Use (7.4), `y=log x`, and the reality symmetry to reduce the nonconstant
part to an integral of `|g(x)|^2`.  Take

\[
 \theta=\left(\log\frac1\delta\right)^{-1}
\]

in (8.12).  On `1<=x<=delta^(-2)` the factor `x^theta` is bounded by an
absolute constant, so

\[
 \int_1^{\delta^{-2}}|g(x)|^2\,dx
 \ll \frac{\log(1/\delta)}{\delta^{1/2}\log X}.
 \tag{9.1}
\]

For `x>delta^(-2)`, (8.7) has real Gaussian decay
`exp(-A*delta^2*x^2)` after the elementary inequality
`sin(delta) asymp delta` is combined with the support of the mollifier.
The resulting tail is exponentially small.  The residue term contributes
`O(X^2 log^2 X)`, which is absorbed in (9.1) because `c<1/8`.  This proves
(S3a).

For every fixed `t`, Cauchy--Schwarz gives

\[
 \left(\int_t^{t+h}|F(u)|\,du\right)^2
 \le h\int_t^{t+h}|F(u)|^2\,du.
\]

Integrating in `t` and applying Tonelli, each `u` is covered by a set of
starts of length exactly `h`.  Therefore

\[
 \int_{\mathbb R}\left(\int_t^{t+h}|F(u)|\,du\right)^2dt
 \le h^2\int_{\mathbb R}|F(u)|^2du,
\]

and (S3b) follows from (S3a).

### 9.2 Lower first moment

Let `delta=1/T`, `X=T^c`, and abbreviate `psi=psi_X`.  On a rectangle with
vertical sides `Re s=2` and `Re s=1/2` and horizontal sides at heights
comparable to `T/2` and `T`, the function

\[
 \zeta(s)\psi(s)^2
\]

is an **auxiliary S4 function**, not the reflected S1 Mellin integrand.
It is holomorphic on this rectangle: the pole at one lies below the
rectangle.  On `Re s=2`,

\[
 \zeta(s)\psi(s)^2=1+\sum_{n\ge2}\frac{a_n}{n^s},
 \qquad |a_n|\le d_3(n),
\]

so termwise integration gives

\[
 \int_{2+iT/2}^{2+iT}\zeta(s)\psi(s)^2\,ds
 =\frac{iT}{2}+O(1).
 \tag{9.2}
\]

This right-edge statement is now stronger than the displayed asymptotic in
Lean.  `SelbergFirstMomentRightEdgeFinite.lean` separates the unique
zero-frequency triple `(1,1,1)` and integrates every other frequency
exactly; the estimate `sum n^(-2) <= 2` in each of the three variables gives

\[
 \left\|\int_a^b
   \bigl(P_{N,X}(t)-1\bigr)\,dt\right\|
 \le \frac{16}{\log 2}.
\]

`SelbergFirstMomentRightEdge.lean` then proves uniform convergence of the
zeta partial sums on the right line, bounds both each zeta partial sum and
the mollifier by `2`, and applies dominated convergence.  Consequently the
actual auxiliary product satisfies, for every real `a,b` and `X>=2`,

\[
 \boxed{\left\|\int_a^b
   \bigl(\zeta(2+it)\psi_X(2+it)^2-1\bigr)\,dt\right\|
 \le \frac{16}{\log 2}.}
 \tag{9.2-L}
\]

Thus the right-edge main-term gate of S4 is closed without a new axiom.

Both horizontal edges admit a simpler bound than the convexity estimate
previously recorded here.  For `1/2<=sigma<=2`, `T<=|t|<=2*T`, apply the
already proved uniform first Abel approximation at the real cutoff `x=4*T`:

\[
 \zeta(s)=\sum_{n\le\lfloor4T\rfloor}n^{-s}
   +\frac{(4T)^{1-s}}{s-1}+O((4T)^{-\sigma}).
\]

The finite sum is at most `2*sqrt(floor(4*T))<=4*sqrt(T)`.  The pole term is
at most `2*sqrt(T)` because `norm(s-1)>=|t|>=T`, and the remainder is
`O(1)<=O(sqrt(T))`.  Hence, uniformly throughout the whole horizontal
segment,

\[
 |\zeta(\sigma+it)|\ll\sqrt T.
\]

The elementary strip bound `|psi_X(s)|<=2*sqrt(X)` therefore gives

\[
 \left|\int_{1/2}^2\zeta(\sigma+it)\psi_X(\sigma+it)^2\,d\sigma\right|
 \ll X\sqrt T.                                      \tag{9.2-H}
\]

This avoids a new convexity theorem entirely.  Since `X=T^(1/32)`, the
horizontal cost is `O(T^(17/32))=o(T)`.  (The earlier shorthand `O(X)` for
the lower edge would apply only to a bounded-height edge, not to the present
dyadic rectangle.)  This is now formalized as
`exists_norm_intervalIntegral_selbergFirstMomentAuxiliary_horizontal_le`,
with the strip zeta and mollifier estimates exposed as separate reusable
theorems.  Its axiom audit contains only the standard Lean/Mathlib axioms.
Cauchy's theorem and (9.2) consequently give

\[
 \left|\int_{T/2}^{T}
   \zeta(\tfrac12+it)\psi(\tfrac12+it)^2\,dt\right|
 \gg T.
 \tag{9.3}
\]

There is no complex-valued identification of this auxiliary product with
the S1 integrand.  Instead, on the critical line one has the exact modulus
identity

\[
 |F_{\delta,X}(t)|
 =\frac1{2\sqrt{2\pi}}
   |\Gamma_{\mathbb R}(\tfrac12+it)|
   e^{(\pi/4-\delta/2)t}
   |\zeta(\tfrac12+it)\psi(\tfrac12+it)^2|.       \tag{9.4}
\]

Indeed `|Z(t)|=|zeta(1/2+it)|` and both mollifier products have modulus
`|psi(1/2+it)|^2`.  The exact algebraic part of (9.4) is the theorem
`abs_selbergCompletedMollifiedF_eq_gamma_tilt_mul_abs_sqrtZeta`; no
Stirling estimate is used in that theorem.

Uniform Stirling on `T/2<=t<=T`, together with
`exp(-delta*t/2) asymp 1`, shows

\[
 |F(t)|\asymp
 t^{-1/4}|\zeta(\tfrac12+it)\psi(\tfrac12+it)^2|.
\]

The one-sided estimate actually needed here is now formalized as
`exists_pos_rpow_neg_quarter_le_norm_GammaR_mul_selbergTilt`.  Its proof
integrates the already formalized Bernoulli-remainder digamma expansion:
the differentiated error is `O(t^(-2))`, hence has bounded integral, while
the real part of `(z-1/2) Log z-z` has the elementary lower bound
`-pi*t/4-(log t)/4-O(1)`.  No unproved Stirling axiom or exact asymptotic
constant is introduced.

Thus (9.3) and the triangle inequality imply

\[
 \int_0^T|F(t)|\,dt
 \ge C T^{-1/4}
 \left|\int_{T/2}^{T}
   \zeta(\tfrac12+it)\psi(\tfrac12+it)^2\,dt\right|
 \gg T^{3/4},
\]

which is (S4a).  Finally Tonelli gives

\[
 \int_0^T\int_t^{t+h}|F(u)|\,du\,dt
 \ge h\int_h^T|F(u)|\,du.
\]

The omitted initial interval is harmless but must be checked.  On
`0<=t<=h`, the completed zeta factor is bounded, the tapered coefficients
satisfy `|beta_n|<=1`, and hence

\[
 |\psi_X(\tfrac12+it)|
 \le \sum_{n<X}n^{-1/2}\ll X^{1/2}.
\]

The exponential tilt is bounded on this interval, so
`integral_0^h |F(t)| dt << h*X`.  With `X=T^(1/32)` and
`h asymp 1/log T`, this is `o(T^(3/4))`.  Therefore

\[
 \int_0^T\int_t^{t+h}|F(u)|\,du\,dt
 \gg hT^{3/4},
\]

proving (S4b).

## 10. Closing the good-window argument

For `t in (0,T)` write

\[
 A(t)=\int_t^{t+h}|F(u)|\,du,
 \qquad
 B(t)=\left|\int_t^{t+h}F(u)\,du\right|.
\]

Always `B(t)<=A(t)`, and outside

\[
 E=\{t\in(0,T):B(t)<A(t)\}
\]

there is equality.  Therefore

\[
 \int_E A(t)\,dt
 \ge \int_0^T A(t)\,dt-\int_0^T B(t)\,dt.
 \tag{10.1}
\]

By S4b, the first term on the right is `>>h*T^(3/4)`.  By Cauchy--Schwarz
and S2, with `delta=1/T`,

\[
 \int_0^T B(t)\,dt
 \le T^{1/2}\left(\int_{\mathbb R}B(t)^2dt\right)^{1/2}
 \ll \frac{h^{1/2}T^{3/4}}{(\log X)^{1/2}}.
 \tag{10.2}
\]

On the other hand, Cauchy--Schwarz and S3b give

\[
 \int_E A(t)\,dt
 \le m(E)^{1/2}
      \left(\int_{\mathbb R}A(t)^2dt\right)^{1/2}
 \ll m(E)^{1/2}hT^{1/4}
      \left(\frac{\log T}{\log X}\right)^{1/2}.
 \tag{10.3}
\]

Combining (10.1)--(10.3) and substituting
`log X=c log T`, `h=(a log X)^(-1)`, yields

\[
 m(E)^{1/2}
 \ge C_1c^{1/2}T^{1/2}-C_2(ac)^{1/2}T^{1/2}.
 \tag{10.4}
\]

Fix `c` first.  Then choose `a>0` small enough that
`C_2*sqrt(a*c)<=C_1*sqrt(c)/2`, while retaining
`(a+2)c<=1/4`.  Equation (10.4) gives

\[
 m(E)\ge C_3T.
 \tag{10.5}
\]

For `t in E`, strict triangle inequality for the real continuous function
`F` forces both signs in `(t,t+h)`.  At the two strict-sign sample points the
mollifier square is automatically nonzero; the positive gamma and
exponential factors therefore force opposite strict signs of the Hardy
function.  Continuity gives a Hardy zero between them, and real analyticity
shows that some intervening zero has odd multiplicity.  Possible zeros of
the mollifier itself do not create this conclusion and are not counted.

Partition `(0,T)` into intervals `I_n=(nh,(n+1)h)`.  At least
`m(E)/h` of these intervals meet `E`.  If `I_n` meets `E`, the corresponding
odd zero lies in `(nh,(n+2)h)`.  Any zero belongs to at most two such doubled
intervals, so

\[
 N_{0,\mathrm{odd}}(T)
 \ge \frac12\frac{m(E)}h+O(1)
 \gg T\log T.
\]

This completes the Selberg implication at paper level, conditional only on
the detailed analytic estimates S1--S4 established in Sections 7--9.  The
remaining pre-Lean task is an independent audit of those sections, especially
the slit-domain continuation in (8.6) and the horizontal contour estimate in
(9.3).

## 11. Independent dependency and parameter audit

The second pass checks the proof without using the repository's current
one-sided zeta approximation.

### Fourier/Mellin step

Pass.  The angular condition `|arg z|<pi/4` gives strict exponential decay
on both horizontal ends.  Shifting from `Re s=c>1` to `Re s=1/2` crosses
only the zeta pole at one.  The Gaussian Mellin inversion is valid because
`Re(z^(-2))>0`.  The finite mollifier introduces no convergence problem.

### Square-root branch in (8.6)

Pass, with an explicit standard dependency.  The needed domain is the strip
`Re w>=1` with a slit from the pole at `w=1`.  Zeta has no zero there.  Fixing
the Euler-product branch for `Re w>1` therefore determines the continuation
on the slit strip.  Near `w=1`, `1/sqrt(zeta(w))` is `O(|w-1|^(1/2))`; away
from the pole on `Re w=1`, the classical reciprocal bound is more than
sufficient for the integral in (8.6).  No unproved zero-free region is used.

### Arithmetic factorization

Pass.  The identity (8.2) follows from the Jordan-totient convolution, all
weights are nonnegative after the square is formed, and (8.4) is an exact
Euler-product comparison.  The final `r` sum in (8.5) is `O(log X)` uniformly
down to `theta=0`; no hidden factor `1/theta` remains in (S-arith).

### Diagonal and off-diagonal ranges

Pass away from the endpoint.  The diagonal endpoint requires
`(a+2)c<=1/4`; the off-diagonal error requires `c<1/8`.  Fix once and for all

\[
 c=\frac1{32}.
\]

After the constants in (10.4) are known, choose `0<a<=1` small enough for
the good-window inequality.  Then

\[
 (a+2)c\le\frac3{32}<\frac14,
\]

so every analytic range condition has strict room.  No limiting endpoint is
used.

### Global square mass

Pass.  Reality of `F` gives the required symmetry of the inverse transform.
The range `x>delta^(-2)` is exponentially small because
`sin(delta)/X^2 >> delta^2` for `c<1/2`.  The residue contribution
`O(X^2 log^2 X)` is `o(delta^(-1/2))` for the fixed `c=1/32`.

### Lower first moment

Pass at paper level, with the object distinction now explicit.  Apply the
rectangle to the auxiliary product `zeta(s) psi(s)^2` directly between
heights `T/2` and `T`; this
prevents an invalid subtraction of two unrelated lower bounds.  The right
edge has main term `iT/2+O(1)`.  Each horizontal edge is
`O(X*sqrt(T))=O(T^(17/32))=o(T)` by the uniform first Abel approximation
and the elementary mollifier bound.  Uniform Stirling then supplies the factor `T^(-1/4)` on
that dyadic height interval.  The exact critical-line modulus bridge back to
the reflected completed function is proved in Lean; the right-edge main
term is now proved in Lean with the explicit remainder `16/log 2`.
The horizontal-edge estimate is now proved in Lean via the uniform first Abel
approximation.  The uniform lower Stirling bound is now proved in Lean from
the existing digamma expansion.  The remaining S4 work is the contour
identity/lower-first-moment assembly and its Tonelli/end-interval transfer,
not a missing analytic estimate.

### Sign change and multiplicity

Pass.  Strict inequality between the absolute integral and the absolute
value of the signed integral forces both signs.  The gamma and exponential
factors are positive; the mollifier square is merely nonnegative, but at
strict-sign sample points it is nonzero.  Hence the two samples transfer to
opposite signs of Hardy's function.  A sign change of a real analytic
function crosses an odd-order zero, and the doubled-window packing charges
each ordinate at most twice.

### Paper-level verdict

The Selberg derivation is unconditional at paper level, subject only to the
standard classical inputs listed below.  This is not yet a repository-level
theorem: S4 still requires assembly of the proved contour estimates,
followed by S5 and the final odd-zero assembly.  Its external analytic inputs
are all established theorems:

* the zero-free line `zeta(1+it) != 0` and a reciprocal bound there;
* the uniform first Abel approximation for zeta in `1/2<=sigma<=2`;
* uniform Stirling estimates for Gamma;
* Cauchy's theorem, Perron inversion, Gaussian Mellin inversion, and
  Plancherel.

It uses neither RH nor any zero-density hypothesis, Farmer's long-mollifier
conjecture, `MWKF(3)`, a Bettin--Chandee conjecture, nor the Zeta23 bridge.
Lean formalization is therefore admissible for the Selberg slice and has
closed S1, S12, S13, S-arith, the full two-sided S2 off-diagonal estimate,
and the signed integrated diagonal asymptotic.

The object-level `J` bridge is now also closed through the following exact
stages.  The physical theta kernel at `log u` equals the original
nonconstant theta kernel; its weighted norm square equals the complete pair
series pointwise.  A uniform positive Gaussian majorant makes the complete
six-index family absolutely integrable, so Fubini gives

\[
 (J(x,\theta):\mathbf C)
 =\sum_{\kappa,\lambda,\mu,\nu}\sum_{m,n\ge1}
   \int_x^\infty \mathcal P_{m,n;\kappa,\lambda,\mu,\nu}(u)\,du.
\]

This series has been partitioned exactly into the mutually exclusive cases
`m*kappa*nu = n*lambda*mu`, `<`, and `>`.  The two strict-inequality pieces
have been reindexed and identified, including the simultaneous-swap
conjugation on the reverse side, with the already bounded physical positive
and reverse off-diagonal sums.  Thus no numerical majorant is being mistaken
for `J` at this interface.

The equality case is now also closed.  Lean proves the standard gcd-ray
parametrization

\[
 m\kappa\nu=n\lambda\mu
 \quad\Longleftrightarrow\quad
 m=r\frac{\lambda\mu}{g},\qquad
 n=r\frac{\kappa\nu}{g},\qquad
 g=(\kappa\nu,\lambda\mu),\ r\ge1,
\]

and identifies its coefficient and damping exactly with
`selbergDiagonalPhysicalOriginalSum`.  Consequently the actual diagonal,
forward, and reverse pieces assemble into the true `J`, and the uniform
bound (S2-J) is proved for that object rather than for a detached majorant.

The Fourier-mass transfer has now also been closed through the following
object-level stages.  The low-frequency estimate follows from the true `J`
at `theta=1/log G`.  The high-frequency estimate is obtained without an
invalid dyadic extrapolation beyond the proved `x<=G` range: averaging
`theta*J(G,theta)` over `0<=theta<=1/2` gives the exact positive kernel

\[
 K(v)=\frac{1-e^{-v/2}(1+v/2)}{v^2},
 \]

and `K(v)>=(1-2/e)/v^2` for `v>=2`.  Lean proves the required Tonelli
identity, both resulting bounds for the nonconstant inverse Fourier kernel,
and the exact logarithmic substitutions under `x=exp y`.

The completed mollified function is now proved directly to lie in both
`L1` and `L2`; the `L2` proof uses the contour-derived exponential tail and
a compact-middle bound, not Plancherel.  Its classical Fourier transform is
identified pointwise with the explicit S1 kernel with normalization

\[
 \mathcal F_{\rm ml}F(w)=\sqrt{2\pi}\,f(2\pi w),
\]

and the abstract Mathlib `L2` Fourier transform is identified with the same
kernel almost everywhere.  Finally the elementary residue coefficient is
bounded and its pointwise square is proved exactly:

\[
 |R(y)|^2=\frac14 e^{-y}
   |\phi(1)\phi(0)|^2.
\]

The residue integrals themselves require no further analytic input.  Put

\[
 L=\log(X^a)=a\log X,
 \qquad D=\delta^{-1/2}.
\]

The tapered coefficients have absolute value at most one, hence

\[
 |\phi(0)|\le X,
 \qquad |\phi(1)|\le 1+\log X,
 \qquad |\phi(1)\phi(0)|\le X(1+\log X)\le X^2.
\]

Since `X<=delta^(-c)` and `c<1/8`, monotonicity of real powers gives

\[
 X^4\le\delta^{-4c}\le\delta^{-1/2}=D.
\]

Consequently, using `L>=2`,

\[
 \int_0^L |R(y)|^2\,dy
 \le \frac14X^4\int_0^\infty e^{-y}\,dy
 \le D,
 \tag{S2-res-low}
\]

and

\[
 \int_L^\infty \frac{|R(y)|^2}{y^2}\,dy
 \le \frac14\frac{X^4}{L^2}
      \int_L^\infty e^{-y}\,dy
 \le \frac{D}{L^2}.
 \tag{S2-res-high}
\]

Because `L=a*log X`, these are exactly the same parameter scales as the
nonconstant estimates, with an admissible constant depending only on the
fixed parameter `a`:

\[
 D\le \frac1a D\frac{L}{\log X},
 \qquad
 \frac{D}{L^2}=\frac1a\frac{D}{L\log X}.
\]

Thus the residue low/high mass estimates are closed at paper level.  This
calculation also shows why no extra mollifier-length restriction is needed:
the already strict gate `c<1/8` supplies precisely `4c<1/2`.

Lean now formalizes this entire residue calculation: the coefficient fourth
power bound, its absorption into `delta^(-1/2)`, the pointwise exponential
envelope, both integrals in (S2-res-low) and (S2-res-high), and the final
parameter-scale interfaces with the explicit common witness `C=1/a`.

The remaining S2 work is now the assembly step: combine the residue with the
nonconstant kernel, transport the low/high ranges through `y=2*pi*w`, invoke
the sliding-window Fourier-energy estimate, and absorb the parameters into
the target S2 bound.  The exact consistent choice is

\[
 H=\frac{2\pi}{L}=\frac{2\pi}{a\log X}.
\]

Indeed Mathlib uses the frequency `w` in `exp(-2*pi*i*t*w)`, whereas the
explicit Mellin kernel uses the angular frequency `y=2*pi*w`.  Thus the
rectangular split `|w|=1/H` becomes `|y|=L`.  The low-frequency Jacobian
exactly cancels the factor `2*pi` in
`|Fhat(w)|^2=2*pi*|f(2*pi*w)|^2`; the high weighted integral acquires
`4*pi^2`.  After reflection of the negative half-line (valid because the
original `F` is real), the safe bound is precisely `(S2-Plancherel)`.

This also corrects the later shorthand occurrences `H=1/(a log X)`: those
use angular-frequency notation and are not literally compatible with the
Mathlib-normalized transform.  The fixed factor `2*pi` changes none of the
S2--S5 asymptotic conclusions, but it must be retained in the formal proof.
The first assembly layer is now formalized in
`SelbergExplicitFourierMass.lean`: it proves the pointwise inequality
`|R+N|^2 <= 2|R|^2+2|N|^2`, supplies genuine integrability for both pieces
on the low and weighted-high ranges, and combines their existential
constants into the full explicit-kernel positive-frequency bounds.  The
second layer is also formalized.  The reusable module
`RealFourierEnergySymmetry.lean` proves conjugate reflection for the Fourier
transform of a real-valued complex function and exact two-sided integral
splittings.  `SelbergFourierEnergyTransport.lean` then proves

\[
 \int_{|w|\le A}|\widehat F(w)|^2\,dw
 =2\int_0^{2\pi A}|f(y)|^2\,dy
\]

and

\[
 \int_{A<|w|}\frac{|\widehat F(w)|^2}{w^2}\,dw
 =8\pi^2\int_{2\pi A}^{\infty}\frac{|f(y)|^2}{y^2}\,dy.
\]

These identities are proved for the actual Mathlib `L2` Fourier
representative by first identifying it almost everywhere with the classical
transform.  The final assembly is now formalized in
`SelbergSlidingSecondMoment.lean`.  With
`L=log(X^a)` and `H=2*pi/L`, it proves uniformly on every finite interval

\[
 \int\left|\int_t^{t+H}F(u)\,du\right|^2dt
 \le C\frac{H\,\delta^{-1/2}}{\log X}.
\]

The explicit witness produced by the proof is
`4*pi*C_low + 16*pi*C_high`; this is exactly the absorption of the two
terms in `(S2-Plancherel)`.  Thus S2 is closed in Lean.  The next work is
S3, then S4, followed by instantiating S5 and the odd-multiplicity packing
theorem.
Thus the Lean development has not yet proved the final Selberg
positive-proportion theorem, despite the unconditional paper-level route
above.

## 12. Sources checked

* E. C. Titchmarsh, revised by D. R. Heath-Brown, *The Theory of the
  Riemann Zeta-function*, second edition, §§10.9--10.22.
* S. Bettin, V. Chandee, M. Radziwill, *The mean square of the product of
  the Riemann zeta function with Dirichlet polynomials*, especially
  Proposition 1 and §§3.1--3.4.
* A. Selberg, *On the zeros of Riemann's zeta-function*, 1942, as cited and
  reproduced in the Titchmarsh account above.
