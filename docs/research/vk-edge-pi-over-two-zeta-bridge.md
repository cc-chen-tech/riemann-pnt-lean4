# VK-edge `pi / 2` gap: zeta bridge audit

## Purpose

The finite-spectrum theorem in
`vk-edge-pi-over-two-proof-record.md` proves a strict abstract gap above
`pi / 2`. This note identifies the exact additional analytic statement needed
to turn that gap into a theorem about `psi(x)-x`.

No unconditional zeta improvement is claimed here.

## The tempting but invalid shortcut

At a fixed truncation height `T`, the maximal-real-part zero package is a
finite exponential polynomial. The repository already separates this package
from lower-real-part zeros and proves a fixed-height positive real-part gap.

It is not valid to let `x` tend to infinity with `T` fixed. The usual
pointwise truncated explicit formula has an error containing an `x/T`-scale
term. To make that error smaller than `x^beta`, `T` must grow with `x`.
Once `T` grows, the maximal package and its size can change.

Bellotti's `O_A(1)` theorem controls zeros near the moving
Vinogradov--Korobov edge. It does not say that, for one fixed
`beta_0 < 1`, the number of zeros with real part at least `beta_0` remains
bounded as `T` tends to infinity.

Therefore the fixed-height Lean package alone cannot transfer the new
finite-spectrum constant to `psi`.

## Why the original Revesz scalar transform is insufficient

Revesz compares one scalar Gaussian-Mellin transform in two ways:

```text
residue lower bound <= transform <=
  (4 / pi) K |rho_0| (1 + o(1)),
```

where `K` bounds `|psi(x)-x| / x^beta` on the localization interval. The
residue lower bound tends to `2`, giving

```text
K >= (pi / 2 - o(1)) / |rho_0|.
```

Bounding the same scalar transform more accurately by the same absolute-value
step cannot use the finite-spectrum theorem: the factor `4/pi` is already the
dual form of the sharp coefficient inequality. A new argument must retain
several phases, or construct a finite-dimensional spectral projection, before
taking an absolute value.

## Sufficient local finite-package theorem

The following analytic statement would be sufficient.

Let

```text
Delta(x) = psi(x) - x.
```

For each large logarithmic scale `Y`, suppose there are:

1. a real exponent `beta_Y`;
2. a finite positive-ordinate zero package `Z_Y` with
   `1 <= #Z_Y <= M_A`, counted with analytic multiplicity in its coefficients;
3. a scale `B_Y > 0`;
4. a real exponential polynomial

   ```text
   P_Y(u)
     = 2 Re(sum_{rho in Z_Y} a_(rho,Y) exp(i Im(rho) u));
   ```

5. an interval `I_Y` whose length tends to infinity;

such that:

```text
max_{rho in Z_Y} |a_(rho,Y)| >= B_Y,
```

and

```text
sup_{u in I_Y}
  |exp(-beta_Y (Y+u)) Delta(exp(Y+u)) - P_Y(u)|
    = o(B_Y).                                  (A)
```

After normalizing a coefficient of size at least `B_Y`, the finite-spectrum
theorem gives

```text
||P_Y||_infinity
  >= L_(M_A) B_Y,

L_M
  = 1 /
    (2/pi
      - sin(1/(4(2M+1))) / (pi(2M+1)))
  > pi/2.
```

A finite exponential polynomial is uniformly almost periodic. For each fixed
package, every interval longer than a package-dependent recurrence modulus
contains a point arbitrarily close to its global sup norm. Therefore (A)
implies

```text
sup_{u in I_Y}
  exp(-beta_Y (Y+u)) |Delta(exp(Y+u))|
    >= (L_(M_A) - o(1)) B_Y.                  (B)
```

only under the additional condition

```text
length(I_Y)
  >= recurrenceModulus(P_Y, desiredAccuracy).  (C)
```

The fact that `length(I_Y)` tends to infinity is not enough when `P_Y` itself
varies with `Y`: its recurrence modulus may grow even faster. Thus a valid
envelope-local proof must establish (C), either from a uniform frequency
separation/Diophantine estimate or from an explicit recurrence bound for the
selected package.

## Recommended construction: envelope-local packages

The most plausible way to prove (A) is not to keep one truncation height
fixed. Use the zero envelope

```text
omega(x)
  = inf_{rho = beta+i gamma, gamma>0}
      ((1-beta) log x + log gamma).
```

At a given scale, retain only zeros whose envelope values are within a fixed
small additive window of `omega(x)`. The desired package theorem has three
parts:

1. **Finite near-minimizers.** Bellotti's edge zero-density theorem bounds the
   number of near-minimizing edge zeros by `M_A`.
2. **Exponential suppression.** Zeros outside the additive envelope window
   contribute a fixed exponential factor less.
3. **Uniform tail control.** The total contribution of the suppressed zeros,
   horizontal contour, pole terms, and endpoint correction is `o(B_Y)`.

This is a quantitative strengthening of the Pintz envelope decomposition.
It avoids requiring that one fixed zero remain the unique rightmost zero at
all larger heights.

If the target zero `rho_0` ceases to be an envelope minimizer because another
zero has larger real part or a better height tradeoff, the new minimizer has a
larger natural contribution. A given-zero lower bound may then follow after a
zero-dependent starting threshold, but this comparison must be written
explicitly.

## Alternative construction: vector-valued Revesz transform

The second possible route is to replace the one-scalar Revesz comparison by a
finite family of translated Gaussian-Mellin transforms:

```text
S_h(Delta),  h in H_Y.
```

The residue side should reconstruct the local polynomial `P_Y`, rather than
only one power sum. The upper side must be bounded as a single
finite-dimensional operator on the real error function. The required operator
norm is the dual extremal constant corresponding to `L_(M_A)`, not the
single-coefficient `4/pi` bound.

This route requires:

1. a finite interpolation matrix for the local ordinates;
2. control of its inverse, with the starting scale allowed to depend on small
   ordinate gaps;
3. a joint kernel norm below `2/pi` by the explicit finite-spectrum margin;
4. Gaussian contour errors uniform over all transforms in the family.

This is more local to the given zero but technically less developed than the
envelope route.

## Global transfer via Abel coefficients

The global `limsup` problem no longer requires the finite-package
approximation below. A separate Mellin--Abel argument reads the boundary
Fourier coefficients of the full PNT error directly. Bellotti's bounded edge
count then guarantees that one of the first `M_A+1` odd multiples of the
target ordinate is missing on the target real-part line.

Combining that missing coefficient with the fixed-cardinality defect argument
proves a strict constant above `pi/2`. The full proof is in
`vk-edge-pi-over-two-abel-transfer.md`.

The finite-package problem was initially expected to be necessary for the
stronger localization claim. The pole-annihilation construction in
`vk-edge-pi-over-two-localized-transfer.md` bypasses it.

## Two-frequency localized transform

The Abel proof supplies a more focused route to localization than the full
envelope decomposition. If `n gamma_0` is the missing odd boundary frequency,
use the dual polynomial

```text
q_n(theta)
  = cos(theta) - epsilon_n t_n cos(n theta),

t_n = sin(1/(4n)).
```

Its normalized `L1` norm is strictly smaller than `2/pi`:

```text
mean |q_n|
  <= 2/pi - t_n/(pi n).
```

In the Revesz Gaussian-Mellin setup, replace the scalar conjugate-paired
transform at `rho_0` by a phase-adjusted linear combination of the transforms
at

```text
rho_0
```

and

```text
w_n = beta_0 + i n gamma_0.
```

The phase and magnitude can be chosen so that the main integral kernel is
exactly `|rho_0| q_n(gamma_0 log x-alpha_0)`. The conditional upper estimate
then contains the improved factor

```text
2 mean |q_n|
  < 4/pi.
```

Because `w_n` is not a zero, the second transform has no central residue.
The target and its conjugate still provide the two unit residues in the first
transform.

The initially identified localized lemma was:

> Prove a weighted Cassels/Turan lower bound for the combined residue sum,
> retaining `2-o(1)` despite the signed coefficient of the auxiliary
> transform.

The original Cassels lemma handles an unweighted sum of conjugate pure powers.
The combined transform introduces fixed coefficients in the auxiliary residue
sum. A valid proof must either extend Cassels to these coefficients or choose
the Gaussian parameter by a separate finite almost-periodic averaging
argument.

This weighted lemma is no longer required. Instead, multiply each Gaussian
Mellin transform by a fixed polynomial that equals one at the center and
vanishes at every unwanted local pole shift. The target transform retains
exactly its central conjugate residue pair, while the auxiliary transform has
no central residue and all its local residues are annihilated. Fixed
polynomial multipliers add only `O(m^(-1/2))` relative `L1` error to the
Gaussian kernel; their polynomial growth is absorbed by the same Gaussian
contour and far-zero estimates. The audited proof is in
`vk-edge-pi-over-two-localized-transfer.md`.

## Superseded envelope blockers

The envelope route needs both:

> A multiplicity-aware, envelope-local explicit formula that approximates the
> normalized prime-counting error by at most `M_A` effective zero frequencies
> with a remainder smaller than the explicit finite-spectrum margin.

and a recurrence bound of the form (C).

The margin can be very small:

```text
L_M - pi/2 is of order M^(-2).
```

Thus an unspecified `o(1)` is acceptable asymptotically, but every source of
error must genuinely tend to zero after normalization. A fixed positive loss
in a spectral projection can erase the improvement.

## Decision

Gate F1 is closed at the abstract Fourier level. The global Abel version of
Gate Z1 is closed, modulo Bellotti's stated theorem. The power-interval
localized version is now derived with the fixed interval `[Y,Y^7]`, modulo
Bellotti's zero count and Revesz's simultaneous zero-avoiding contour lemmas.

The envelope and weighted-Cassels routes remain useful alternative approaches,
but they are not blockers for the pole-annihilation proof. Historical priority
and external specialist review are still open, so the result must not yet be
advertised as a new theorem in the literature.
