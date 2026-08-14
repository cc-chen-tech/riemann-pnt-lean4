# Signed short-interval L2 route at two thirds

## Claim boundary

This note implements the paper-first checkpoint for excluding zeta zeros with
real part strictly greater than `2/3`.  It does **not** claim that the required
prime-side mean square has been proved.

The audit closes the following pieces.

1. The model-zero exponent is exactly `2 beta + 2 a - 1`.
2. At `a = 2/3`, a Mellin-pole argument upgrades the model calculation to a
   genuine zero-side obstruction without a rightmost-zero hypothesis, a
   finite-height hypothesis, or a visible-cluster witness.
3. The prime-side energy has an exact finite signed-correlation expansion.
   The diagonal and rounding terms satisfy the target scale.
4. Every currently identified unconditional input still leaves the same
   signed off-diagonal term at power `7/3` rather than `5/3`.  The exact fixed
   power deficit is `2/3`.

Therefore Gate Z and the algebraic/harmless part of Gate A have complete
paper derivations in this audit, but still require independent mathematical
review.  Gate C remains open as one structured signed off-diagonal estimate.
No new Lean interface is introduced at this checkpoint.

## 1. Definition and target

Let `w` and `nu` be fixed nonnegative smooth functions, normalized to have
integral one and compactly supported in `(1,2)`.  Put

```text
D_a(X;t,u) = psi(X t + u X^a) - psi(X t) - u X^a
```

and

```text
J_a(X) = X integral integral |D_a(X;t,u)|^2 w(t) nu(u) dt du.
```

This is the stated integral after `x = X t`.  The only prime-side target in
this route is

```text
for every eta > 0, J_(2/3)(X) <<_eta X^(5/3 + eta).
```

The quantifier `for every eta > 0` and the strict inequality on the zero real
part are both essential.  Nothing in this route addresses a zero exactly on
`Re(s)=2/3`.

## 2. Gate Z: the zero-side response

### 2.1 Model calculation

For the explicit-formula model term

```text
E_rho(x) = -x^rho / rho,       rho = beta + i gamma,
```

uniformly for `t,u` in compact subsets of `(1,2)` and `0<a<1`,

```text
E_rho(X t + u X^a) - E_rho(X t)
  = -u X^a (X t)^(rho-1) + O_rho(X^(beta+2a-2)).
```

The factor `rho` from differentiation cancels the `1/rho` in the explicit
formula.  Squaring and integrating over an `x`-interval of length comparable
to `X` gives

```text
X * X^(2a) * X^(2beta-2) = X^(2beta+2a-1).
```

At `a=2/3` this is

```text
X^(2beta+1/3).
```

Its excess over the target `X^(5/3+eta)` is

```text
2 beta - 4/3 - eta.
```

Thus one must choose `0 < eta < 2 beta - 4/3`; at `beta=2/3` there is no
positive choice.

### 2.2 A linear functional controlled by the energy

Because `w` and `nu` are nonzero nonnegative smooth weights, each is positive
on some open subinterval of `(1,2)`.  Choose smooth compactly supported
functions `phi` and `chi` inside those positivity sets, and set

```text
L(X) = integral integral D_(2/3)(X;t,u) phi(t) chi(u) dt du.
```

Weighted Cauchy--Schwarz gives

```text
|L(X)|^2 <= C_(phi,chi,w,nu) J_(2/3)(X) / X.
```

In particular, the target mean square implies, for every `eta>0`,

```text
L(X) << X^(1/3 + eta/2).
```

### 2.3 Moving the additive difference to the test function

Write `E(x)=psi(x)-x` and `delta=X^(-1/3)`.  A change of variables in the
first occurrence of `E` gives the exact identity

```text
L(X)
  = integral E(X y)
      [integral chi(u) (phi(y-u delta)-phi(y)) du] dy.
```

Let `mu_1 = integral u chi(u) du`, chosen nonzero.  Taylor expansion of the
smooth test function, not of the discontinuous function `E`, gives

```text
L(X) = -mu_1 delta M_phi(X) + O(delta^2 X log(2X)),

M_phi(X) = integral E(X y) phi'(y) dy.
```

Only the elementary bound `E(x)=O(x log(2x))` is used in the remainder.  At
`a=2/3`, division by `delta` turns the remainder into `O(X^(2/3) log X)`.
Consequently the proposed mean square implies

```text
for every epsilon>0, M_phi(X) <<_epsilon X^(2/3+epsilon).
```

The equality of the Taylor-remainder exponent and the desired boundary at
`a=2/3` is important.  This first-order argument is not being claimed for
arbitrary `a>2/3`.

### 2.4 Mellin pole and anti-cancellation

For `Re(s)>1`,

```text
F(s) = integral_1^infinity E(x) x^(-s-1) dx
     = -(zeta'/zeta)(s)/s - 1/(s-1).
```

The Mellin transform of `M_phi`, initially in the same half-plane, is

```text
K_phi(s) F(s) + H_phi(s),

K_phi(s) = integral phi'(y) y^s dy
         = -s integral phi(y) y^(s-1) dy,
```

where `H_phi` is entire and comes only from the bounded lower-end correction
created by starting the `X`-integral at one.

Fix any zeta zero `rho=beta+i gamma` of multiplicity `m` with `beta>2/3`.
Choose `phi` so that `K_phi(rho)` is nonzero; a sufficiently narrow bump in
any interval where `w>0` does this.  The pole of `F` at `rho` has residue
`-m/rho`, so it cannot be cancelled by `H_phi`.  On the other hand, the bound

```text
M_phi(X) << X^(2/3+epsilon)
```

makes its Mellin transform holomorphic in `Re(s)>2/3+epsilon`.  Taking
`epsilon<beta-2/3` is a contradiction.

This argument handles, without extra hypotheses:

- multiplicity, because the residue is multiplied by the positive integer
  `m`;
- conjugate zeros and several frequencies with the same real part, because
  distinct frequencies are distinct Mellin poles;
- a rightmost real part that is not attained, because the proof fixes the
  alleged zero itself rather than taking a supremum;
- infinitely many higher zeros, because no finite explicit-formula
  truncation or visible-cluster selection is used.

More quantitatively, if `rho` has real part `beta>2/3`, then for every

```text
0 < epsilon < 2(beta-2/3)
```

one cannot have

```text
J_(2/3)(X) << X^(2beta+1/3-epsilon).
```

Otherwise the same calculation would give
`M_phi(X)<<X^(beta-epsilon/2)`, contradicting the pole at `rho`.  Letting
`epsilon` decrease along a diagonal sequence yields arbitrarily large `X_j`
with

```text
J_(2/3)(X_j) >= X_j^(2beta+1/3-o(1)).
```

This is Gate Z in the strength needed for the strict `2/3` contradiction.

## 3. Gate A: exact signed-correlation identity

Put `H=X^a` and `b(n)=Lambda(n)-1`.  For real `x` and `h>=0`, define

```text
P(x,h) = sum_(x<n<=x+h) b(n),
R(x,h) = floor(x+h)-floor(x)-h.
```

Then the exact finite identity is

```text
psi(x+h)-psi(x)-h = P(x,h)+R(x,h),
```

with `|R(x,h)|<1`.

Define the two-variable kernel

```text
K_X(m,n)
  = integral_1^2 nu(u) integral_X^(2X) w(x/X)
      1_(x<m<=x+uH) 1_(x<n<=x+uH) dx du.
```

Then

```text
integral integral |P(x,uH)|^2 w(x/X) nu(u) dx du
  = sum_(m,n) b(m)b(n) K_X(m,n)
  = sum_r sum_n b(n)b(n+r) K_X(n,n+r).
```

The sums are finite: only integers in `[X,2X+2H]` can occur.

### Correction to the one-variable-kernel shorthand

For general smooth `w(x/X)`, the exact kernel depends on both `n` and `r`.
It is therefore `K_X(n,n+r)`, not a weight `W_X(r)` independent of `n`.
A one-variable shift weight is available only after an additional interior
approximation or a special translation-invariant choice of the `x`-weight;
its boundary error would have to be proved separately.

### 3.1 Diagonal

For every relevant `n`, `K_X(n,n)=O(H)`.  The elementary estimate
`Lambda(n)<=log n` gives

```text
sum_(n asymp X) b(n)^2 << X log^2 X.
```

Hence the diagonal is

```text
O(X H log^2 X).
```

At `H=X^(2/3)` this is `O(X^(5/3) log^2 X)`, exactly on the acceptance line.

### 3.2 Rounding and the cross term

The rounding square contributes `O(X)`.  Once the centered square is bounded
by `O(XH polylog X)`, Cauchy--Schwarz makes the cross term at most

```text
O(X sqrt(H) polylog X),
```

which is smaller.  Equivalently, the inequality

```text
|P+R|^2 <= 2|P|^2+2|R|^2
```

is sufficient for the desired upper bound.  Thus no rounding or endpoint
term exceeds the target.

### 3.3 The single remaining arithmetic term

The open term is

```text
S_off(X,H)
  = sum_(r != 0) sum_n b(n)b(n+r) K_X(n,n+r).
```

The needed estimate is the signed, one-sided bound

```text
S_off(X,X^(2/3)) <<_eta X^(5/3+eta).
```

Taking absolute values coefficient by coefficient gives only

```text
X H^2 polylog X = X^(7/3) polylog X,
```

so it loses the exact factor `H=X^(2/3)` that the route must recover through
signed cancellation.

## 4. Gate E: exponent ledger

The ledger records powers of `X`; logarithmic and subpower factors are shown
separately.

| input or operation | available scale at `H=X^a` | at `a=2/3` | deficit from `5/3` | audit result |
|---|---:|---:|---:|---|
| target / RH scale benchmark | `X H polylog X` | `X^(5/3) polylog X` | `0` | benchmark only; RH is not an input |
| diagonal | `X H log^2 X` | `X^(5/3) log^2 X` | `0` | accepted unconditionally |
| floor and endpoints | `X polylog X` | `X polylog X` | none | accepted unconditionally |
| coefficientwise absolute value | `X H^2 polylog X` | `X^(7/3) polylog X` | `2/3` | rejected |
| classical Parseval/large-sieve use with the window kernel bounded by `H^2` | `X H^2 polylog X` | `X^(7/3) polylog X` | `2/3` | no signed shift saving |
| Saffari--Vaughan type unconditional Selberg-integral estimate | `X H^2` times a subpower saving | `X^(7/3-o(1))` | `2/3` at power level | insufficient |
| repository Selberg modules | no theorem for this prime short-interval variance | none | not assignable | unrelated critical-line/mollifier targets |
| Carlson/Ingham zero-density counts | zero count only | none | not assignable | no correlation or cross-term upper bound |
| Guth--Maynard pointwise short-interval consequence | after translating its prime-count result, at power level the error is at best `H` times subpower/polylog factors | square gives `X H^2` times a subpower saving | `2/3` at power level | consequence alone is insufficient |
| Guth--Maynard large-value theorem | candidate structured Dirichlet-polynomial input | none until a block reduction is proved | not assignable | do not credit an exponent prematurely |

The classical Selberg-integral scale quoted above is the known
`X H^2` scale with a subpower saving in long-enough short intervals, not the
RH-conditional `X H log^2 X` scale.  Guth--Maynard's current paper proves a
new large-values theorem and derives a pointwise prime theorem for interval
length `x^(17/30+epsilon)`; neither statement is itself the weighted variance
required here:

- [Guth--Maynard, arXiv:2405.20552v2](https://arxiv.org/abs/2405.20552)
- [An RH-conditional explicit Selberg mean-value estimate](https://arxiv.org/abs/2206.00433)

The arithmetic audit therefore leaves exactly one structured excess term,
`S_off`, rather than several independent fixed-power failures.  This permits
Gate C to continue, but does not close it.

## 5. Gate C preregistration

The first decomposition attempt must use Vaughan's identity with

```text
U=V=X^(1/3).
```

The acceptance rule is fixed before estimating the blocks:

1. keep `b(n)=Lambda(n)-1` signed through the sum over shifts;
2. prove every grouped Type I and Type II contribution is at most
   `X^(5/3+eta)`;
3. do not replace the whole shifted product by its coefficientwise absolute
   value;
4. record the exact exponent of every failed grouped block;
5. use a third-order Heath--Brown decomposition only if all other groups close
   and the sole remaining obstruction is a balanced trilinear block;
6. if two independent groups remain above `5/3` by fixed powers, stop this
   decomposition rather than adding conditional interfaces.

No current repository theorem supplies the required additive signed
off-diagonal estimate.  In particular, the multiplicative Dirichlet-polynomial
large-value theorem must first be connected to the precise kernel
`K_X(n,n+r)`; merely citing it does not bound `S_off`.

## 6. Closing implication, conditional only on Gate C

If Gate C proves

```text
for every eta>0, J_(2/3)(X) <<_eta X^(5/3+eta),
```

then a zero with `beta>2/3` permits a choice

```text
0 < eta < 2 beta - 4/3.
```

Gate Z forces arbitrarily large values on the scale
`X^(2beta+1/3-o(1))`, while Gate C gives at most `X^(5/3+eta)`; the powers are
strictly incompatible.  Existing nonvanishing on `Re(s)>=1` covers the outer
boundary.  The result would exclude the strict half-plane `Re(rho)>2/3`, not
the boundary line.

## 7. Carlson-growth backup audit

The backup remains disabled until an `S`-relative persistence theorem is
proved.  The repository audit already shows that the existing result produces
only one new zero and does not persist after inserting it into `S`:

- `docs/research/exceptional-zero-growth-budget-audit.md`.

The oscillation papers are relevant evidence for seed-forced oscillation, but
ordinary `Omega_+/-` does not prove that the oscillation survives deletion of
the seed packet:

- [Schlage--Puchta](https://arxiv.org/abs/1912.00853)
- [Pintz](https://doi.org/10.1134/S0081543817010163)

### Density-curve correction

The line

```text
(8/3)(1-sigma)
```

crosses Carlson's `4 sigma(1-sigma)` at `sigma=2/3`, with different
derivatives, so that crossing is not tangential.  However, this line is not
Ingham's exact classical density exponent.  The exact exponent recorded by
Guth--Maynard is

```text
3(1-sigma)/(2-sigma).
```

At `sigma=2/3` it equals `3/4`, whereas Carlson equals `8/9`.  Future packet
growth comparisons must therefore define `d(sigma)` as the minimum of the
actual available density exponents (including the relevant parameter ranges),
not label the `8/3` comparison line as Ingham's theorem.

The current Guth--Maynard paper also records the sharper curve

```text
15(1-sigma)/(3+5sigma)
```

and, after combining regimes with Ingham, the uniform linear consequence
`(30/13)(1-sigma)`.  At `sigma=2/3` the exact Ingham value `3/4` is still
smaller than both `15/19` and `10/13`.  The audit script records all four
curves separately and takes their pointwise minimum only as a bookkeeping
candidate, not as a substitute for checking each theorem's range.

If persistence is eventually proved and one generation raises height by at
most `k` while producing at least `c` independent packets, the lower growth
exponent remains

```text
g = log(c)/log(k),
```

and success requires `g>d(sigma)` for some optimized
`sigma in (2/3,beta)`.

## 8. Dependency audit and Lean admission rule

The Gate Z proof above uses only:

- the definition of `psi` and its Mellin relation to `-zeta'/zeta`;
- elementary growth `psi(x)=O(x log x)` for the Taylor remainder;
- weighted Cauchy--Schwarz and compactly supported smooth tests;
- the local pole and multiplicity of `zeta'/zeta` at the alleged zero.

It does not use RH, a PNT power error, `globalRealPartBound`, a finite zero
set, a finite-height zero-free computation, or a visible-cluster witness.

Gate A is a finite algebraic identity plus elementary diagonal bounds.  Gate
C is still missing.  Consequently the planned Lean declarations

```text
ShortIntervalPsiL2Bound a
shortIntervalPsiL2Bound_excludes_zero_right
noZerosStrictlyRightOfTwoThirds
```

must not be added yet.  They become admissible only after the signed
off-diagonal bound has a complete paper proof and an independent dependency
audit.

## 9. Reproducible finite checks

The script

```text
python3 -m experiments.rh.short_interval_signed_l2_audit
```

prints the exact exponent ledger.  Its tests check:

- the model exponent `2beta+1/3`;
- zero contradiction margin at `beta=2/3`;
- the exact `2/3` absolute-value deficit;
- the signed finite correlation expansion;
- the `psi`/centered-sum/floor decomposition;
- the distinction between exact Ingham and the `8/3` comparison line;
- the packet-growth formula `log(c)/log(k)`.

These are finite identity checks only.  They are not evidence for the open
upper bound.
