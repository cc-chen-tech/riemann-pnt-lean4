# Independent review of the short-interval L2 zero-forcing gate

## Verdict

The zero-forcing gate at `a=2/3` passes this independent derivation.
Precisely, let `w, nu` be fixed nonnegative smooth functions with compact
support in `(1,2)`, neither identically zero, and put

```text
J(X) = X integral integral
  |E(X t + u X^(2/3)) - E(X t)|^2 w(t) nu(u) dt du,

E(x) = psi(x)-x.
```

If `rho=beta+i gamma` is a zeta zero and `beta>2/3`, then, for every

```text
0 < epsilon < 2(beta-2/3),
```

the estimate

```text
J(X) << X^(2 beta + 1/3 - epsilon)
```

is impossible.  Consequently there is a sequence `X_j -> infinity` such
that

```text
J(X_j) >= X_j^(2 beta + 1/3 - o(1)).
```

The proof fixes the alleged zero itself.  It does not use a rightmost zero,
a global real-part cap, a finite-height zero-free region, a finite visible
cluster, or zero-density input.

## 1. Test functions and weighted duality

Because `w` and `nu` are nonnegative, smooth, and nonzero, there are open
intervals `I,J` compactly contained in `(1,2)` and constants `c_w,c_nu>0`
such that

```text
w >= c_w on I,       nu >= c_nu on J.
```

Choose smooth compactly supported functions

```text
phi in C_c^infinity(I; C),
chi in C_c^infinity(J; R),
```

and define

```text
L(X) = integral integral
  [E(X t+u X^(2/3))-E(X t)] phi(t) chi(u) dt du.
```

Extending `phi` and `chi` by zero, weighted Cauchy--Schwarz gives the exact
bound

```text
|L(X)|^2
  <= (J(X)/X) * integral integral
       |phi(t) chi(u)|^2/(w(t) nu(u)) dt du
  = C_(phi,chi,w,nu) J(X)/X.
```

The quotient is bounded on the chosen supports.  Thus

```text
J(X) << X^p   implies   L(X) << X^((p-1)/2).
```

## 2. Exact movement of the additive difference

Set

```text
delta = X^(-1/3).
```

Since `X t + u X^(2/3)=X(t+u delta)`, changing variables
`y=t+u delta` only in the first term gives

```text
L(X) = integral E(X y) B_delta(y) dy,

B_delta(y)
  = integral chi(u)[phi(y-u delta)-phi(y)] du.
```

There is no Taylor expansion of `E`, which is discontinuous.  Taylor's
formula is applied only to the smooth function `phi`:

```text
phi(y-u delta)-phi(y)
  = -u delta phi'(y)
    + u^2 delta^2 integral_0^1
        (1-v) phi''(y-vu delta) dv.
```

Choose `chi` nonnegative and nonzero.  Since `J` is contained in `(1,2)`,

```text
mu_1 = integral u chi(u) du > 0.
```

It follows that

```text
L(X) = -mu_1 delta M_phi(X) + R(X),

M_phi(X) = integral E(X y) phi'(y) dy.
```

The remainder kernel is supported in a fixed compact subinterval of
`(0,infinity)` and is uniformly bounded after division by `delta^2`.
The elementary Chebyshev estimate `psi(x)=O(x)` therefore gives

```text
R(X)=O(delta^2 X)=O(X^(1/3)).
```

Even the weaker coefficientwise estimate `psi(x)=O(x log(2x))` would give
`R(X)=O(X^(1/3) log X)`, which is still sufficient below.

Dividing by `delta=X^(-1/3)` yields

```text
M_phi(X)
  << X^(1/3) |L(X)| + X^(2/3)
```

with an optional logarithm in the second term if only the weaker elementary
bound is used.

Now suppose, for contradiction, that

```text
J(X) << X^p,
p = 2 beta + 1/3 - epsilon.
```

Then

```text
X^(1/3)|L(X)|
  << X^((p-1)/2+1/3)
   = X^(beta-epsilon/2).
```

If `epsilon<2(beta-2/3)`, then `beta-epsilon/2>2/3`, so the Taylor remainder
is smaller, including its possible logarithm.  Hence

```text
M_phi(X) << X^(beta-epsilon/2).
```

## 3. Mellin transform computed from definitions

For `Re(s)>1`, absolute convergence and Tonelli give

```text
F(s) = integral_1^infinity E(x) x^(-s-1) dx
     = -(1/s) zeta'(s)/zeta(s) - 1/(s-1).
```

Indeed,

```text
integral_1^infinity psi(x)x^(-s-1) dx
  = sum_n Lambda(n) integral_n^infinity x^(-s-1) dx
  = (1/s) sum_n Lambda(n)n^(-s)
  = -(1/s) zeta'(s)/zeta(s),
```

and the transform of `x` is `1/(s-1)`.

For the smoothed error, again initially in `Re(s)>1`, put

```text
I_phi(s) = integral_1^infinity M_phi(X) X^(-s-1) dX.
```

Changing variables `z=Xy` gives

```text
I_phi(s)
  = integral phi'(y)y^s
      [integral_y^infinity E(z)z^(-s-1) dz] dy
  = K_phi(s) F(s) + H_phi(s),

K_phi(s) = integral phi'(y)y^s dy
         = -s integral phi(y)y^(s-1) dy,

H_phi(s) = -integral phi'(y)y^s
  [integral_1^y E(z)z^(-s-1) dz] dy.
```

Both variables in `H_phi` range over compact subsets of `(0,infinity)`.
The functions `y^s` and `z^(-s-1)` are entire in `s`, uniformly on compact
sets, so `H_phi` is entire.  This verifies rather than assumes the lower-end
correction.

If `M_phi(X)=O(X^theta)`, its defining Mellin integral is holomorphic in
`Re(s)>theta`.  Uniqueness of analytic continuation then forces
`K_phi(s)F(s)+H_phi(s)` to have no pole there.

## 4. Selecting a test that sees the chosen zero

Let `rho` be the fixed alleged zero.  Its multiplicity `m` is a positive
integer, and

```text
Res_(s=rho) F(s) = -m/rho.
```

The number `rho` is nonzero.  Choose a point `y_0` in `I`.  Continuity of
`y^(rho-1)` permits a smaller interval `I_0` around `y_0` on which

```text
|y^(rho-1)-y_0^(rho-1)| < |y_0^(rho-1)|/2.
```

For any nonnegative nonzero bump `phi` supported in `I_0`,

```text
integral phi(y)y^(rho-1) dy != 0,
```

and therefore

```text
K_phi(rho) = -rho integral phi(y)y^(rho-1) dy != 0.
```

Thus `K_phi F+H_phi` has a genuine pole at `rho`.  Taking

```text
theta=beta-epsilon/2 < beta
```

contradicts the holomorphy obtained from the assumed bound for `J`.

Multiplicity cannot cancel the pole.  Distinct conjugate or same-real-part
frequencies occur at distinct points of the Mellin plane and cannot cancel a
local pole at the fixed `rho`.  Since no supremum over real parts was taken,
non-attainment of a rightmost real part is irrelevant.

## 5. From failure of Big-O to an explicit sequence

Let

```text
q = 2 beta + 1/3,
epsilon_j = min(1/j, beta-2/3).
```

For all sufficiently large `j`, `0<epsilon_j<2(beta-2/3)`.  The preceding
argument says that `J(X)=O(X^(q-epsilon_j))` is false.  Consequently, for
every `C>0` and every `X_0`, there is an `X>=X_0` with

```text
J(X) > C X^(q-epsilon_j).
```

Recursively choose

```text
X_j >= max(exp(j), X_(j-1)+1)
```

with `C=1`.  Then `X_j -> infinity`, `epsilon_j -> 0`, and

```text
J(X_j) >= X_j^(q-epsilon_j)
       = X_j^(2 beta+1/3-o(1)).
```

This diagonal step uses only the precise meaning of failure of an eventual
Big-O estimate.

## 6. Dependency and boundary audit

Inputs used:

- the definition of `psi` and the Dirichlet series for `-zeta'/zeta` in
  `Re(s)>1`;
- elementary growth `psi(x)=O(x)` (or the weaker `O(x log x)`);
- local pole order of `zeta'/zeta` at the fixed zero;
- smooth compactly supported test functions, Cauchy--Schwarz, Taylor's
  formula, and elementary Mellin-transform arguments.

Inputs not used:

- RH or an RH-conditional Selberg integral;
- a PNT power error;
- `globalRealPartBound`;
- a finite-height zero-free certificate;
- a finite or visible zero cluster;
- Carlson, Ingham, or Guth--Maynard density estimates.

At `beta=2/3`, the allowed range

```text
0 < epsilon < 2(beta-2/3)
```

is empty.  The argument therefore produces no contradiction on the boundary,
as required.

## Admission decision

Gate Z is accepted as a paper theorem for the fixed exponent `a=2/3`, subject
to later external mathematical review.  This decision authorizes the Gate C
Fourier/Vaughan feasibility audit.  It does not authorize a Lean zero-free
interface because the prime-side upper bound remains open.
