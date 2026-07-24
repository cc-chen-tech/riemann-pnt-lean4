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
package, every sufficiently long interval contains a point arbitrarily close
to its global sup norm. Hence (A) implies

```text
sup_{u in I_Y}
  exp(-beta_Y (Y+u)) |Delta(exp(Y+u))|
    >= (L_(M_A) - o(1)) B_Y.                  (B)
```

The recurrence length may depend on the actual frequencies. This dependence
can be absorbed into the starting scale; it does not have to enter a power
interval exponent.

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

## Current hard blocker

The missing theorem is not another finite-frequency norm estimate. It is:

> A multiplicity-aware, envelope-local explicit formula that approximates the
> normalized prime-counting error by at most `M_A` effective zero frequencies
> with a remainder smaller than the explicit finite-spectrum margin.

The margin can be very small:

```text
L_M - pi/2 is of order M^(-2).
```

Thus an unspecified `o(1)` is acceptable asymptotically, but every source of
error must genuinely tend to zero after normalization. A fixed positive loss
in a spectral projection can erase the improvement.

## Decision

Gate F1 is closed at the abstract Fourier level. Gate Z1 remains open.

The next mathematical task on this branch is to prove the finite
near-minimizer decomposition for the Pintz envelope, including a remainder
smaller than

```text
(L_(M_A) - pi/2) B_Y.
```

Until that theorem is proved, the repository must not claim a zeta
oscillation constant above `pi/2`.
