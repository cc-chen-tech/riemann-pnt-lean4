# Gate C Fourier and Vaughan feasibility audit

## Verdict

The exact Fourier representation and the exact Vaughan decomposition both
close algebraically.  The requested prime-side upper bound does not close
with the audited unconditional inputs.

At `H=X^(2/3)`, three disjoint frequency regimes remain bounded only at

```text
X H^2 X^o(1) = X^(7/3+o(1)),
```

whereas the acceptance line is `X H X^o(1)=X^(5/3+o(1))`.  Each regime has
fixed power deficit `2/3`.  Vaughan's identity reorganizes the coefficients
but does not, using the current large-sieve and mean-value inputs, supply the
missing factor `H`.  Moreover, separately squaring its grouped Type I and
Type II pieces destroys cross-piece cancellation already needed at frequency
zero.

The preregistered stop rule is therefore triggered: there are multiple
independent fixed-power failures.  Guth--Maynard and third-order
Heath--Brown escalation are not activated.  This is a failure certificate
for the audited decomposition, not a proof that every possible signed
correlation method must fail.

## 1. Exact weighted Fourier identity

Put

```text
b(n) = Lambda(n)-1,
W_X(x) = w(x/X),
H = X^(2/3).
```

Only integers in `(X,2X+2H]` can occur, so truncate `b` to that finite set and
write

```text
B_X(alpha) = sum_n b(n) exp(-2 pi i n alpha).
```

For `h>0`, define

```text
kappa_h(y) = 1_[-h,0)(y).
```

Then the centered short-window sum is the finite convolution

```text
P_h(x) = sum_(x<n<=x+h) b(n)
       = sum_n b(n) kappa_h(x-n).
```

Use the continuous Fourier-transform convention

```text
f_hat(alpha) = integral_R f(x) exp(-2 pi i x alpha) dx.
```

Direct calculation gives

```text
kappa_h_hat(alpha)
  = (exp(2 pi i h alpha)-1)/(2 pi i alpha),
kappa_h_hat(0)=h,

W_X_hat(xi) = X w_hat(X xi).
```

Plancherel, applied before taking any absolute values of coefficient sums,
gives

```text
integral_R W_X(x)|P_h(x)|^2 dx
 = integral_R integral_R
     B_X(alpha) conjugate(B_X(beta))
     kappa_h_hat(alpha) conjugate(kappa_h_hat(beta))
     X w_hat(X(beta-alpha)) d alpha d beta.
```

Averaging `h=uH` against `nu` yields the exact Gate C expression

```text
C(X,H)
 = integral_R integral_R
     B_X(alpha) conjugate(B_X(beta))
     A_H(alpha,beta)
     X w_hat(X(beta-alpha)) d alpha d beta,

A_H(alpha,beta)
 = integral_1^2 nu(u)
     kappa_(uH)_hat(alpha)
     conjugate(kappa_(uH)_hat(beta)) du.
```

Absolute convergence follows from the rapid decay of `w_hat`, the bound

```text
|kappa_(uH)_hat(alpha)| << min(H,1/|alpha|),
```

and the finiteness of `B_X`.

### Why the representation is genuinely two-frequency

For every `A>0`,

```text
X |w_hat(X(beta-alpha))|
  <<_A X(1+X|beta-alpha|)^(-A).
```

Thus `beta` is localized within `O(1/X)` of `alpha`, but it is not equal to
`alpha`.  Replacing this approximate identity by a delta mass requires
control of the variation of `B_X` on the uncertainty scale `1/X`.  The
generic derivative estimate for `B_X` is too large to make that replacement
at cost `X^(5/3+eta)`.

Equivalently, after folding the periodic polynomial `B_X` to the unit torus,
the exact multiplier is the periodized double kernel

```text
M_(X,H)(alpha,beta)
 = sum_(k,l in Z)
     A_H(alpha+k,beta+l)
     X w_hat(X[(beta+l)-(alpha+k)]).
```

There is no exact one-variable weight `W_X(r)` or diagonal frequency
multiplier for general nonconstant `w`.

## 2. Exact finite check of the double coupling

The audit tool implements the cyclic analogue with DFT convention

```text
f_hat(k)=sum_j f(j) exp(-2 pi i j k/q).
```

If `P=b*kappa` on the finite cycle and `W_j` is a position weight, then

```text
sum_j W_j |P_j|^2
 = q^(-2) sum_(k,l)
     P_hat(k) conjugate(P_hat(l)) W_hat(l-k).
```

For constant `W`, only `W_hat(0)` survives and this reduces to ordinary
Parseval.  For a nonconstant weight, off-diagonal frequency terms are
generically nonzero.  Tests verify the identity both for synthetic signed
coefficients and for the actual finite sequence `Lambda(n)-1`, `2<=n<18`.
These tests certify only the algebraic representation.

## 3. Frequency exponent ledger

The factor `X w_hat(X(beta-alpha))` has bounded mass in `beta`, so at the
power-bookkeeping level the window envelope is

```text
min(H^2,|alpha|^(-2)).
```

This statement is used only as an upper-bound ledger after retaining the
exact double formula above.

### 3.1 Very low frequency: `|alpha| <= X^(-1)`

Partial summation and the classical PNT error give, uniformly in this range,

```text
|B_X(alpha)|
  << X exp(-c sqrt(log X)) polylog X.
```

The frequency volume is `X^(-1)` and the window multiplier is `H^2`.
Therefore the available contribution is

```text
H^2 * X^(-1) * X^2 exp(-2c sqrt(log X)) polylog X
  = X H^2 exp(-2c sqrt(log X)) polylog X
  = X^(7/3-o(1)).
```

To reach `XH`, this band alone would need

```text
|B_X(alpha)| << X/sqrt(H) * X^o(1)
             = X^(2/3+o(1))
```

on the very-low-frequency scale.  That is already a power-scale centered
prime-sum estimate of the same strength as the desired zero-free target; the
classical PNT subpower saving does not provide it.

### 3.2 Transition frequency: `X^(-1) < |alpha| < H^(-1)`

The window multiplier is still `H^2`.  The classical continuous large-sieve
or finite-frequency Montgomery--Vaughan estimate supplies at best total
spectral mass

```text
integral |B_X(alpha)|^2 d alpha << X polylog X
```

for the audited use.  It does not give a factor equal to the length of a
subunit frequency interval for an arbitrary length-`X` polynomial.  Hence

```text
transition contribution << X H^2 polylog X = X^(7/3+o(1)).
```

The missing input is spectral non-concentration strong enough to save one
factor `H` while retaining the signs of `Lambda-1`.

### 3.3 High frequency: `H^(-1) <= |alpha| <= 1`

On a dyadic band `|alpha| asymp A`, the window contributes `A^(-2)`.
Using the same available mean-value estimate on each band gives

```text
band contribution << A^(-2) X polylog X.
```

The dyadic sum in this range is dominated by `A=H^(-1)` and is again

```text
X H^2 polylog X = X^(7/3+o(1)).
```

After unfolding the periodic polynomial, frequencies beyond unit size have
additional `|alpha|^(-2)` decay and do not change this dominant power.  The
desired `XH` would follow from a localized estimate whose spectral mass
on a band of length `A` is `O(A X polylog X)`.  No such prime-coefficient
local non-concentration theorem is present in the repository or supplied by
the generic Montgomery--Vaughan interface.

### Ledger summary

| regime | audited input | exponent | target | deficit |
|---|---|---:|---:|---:|
| very low | classical PNT error and partial summation | `7/3-o(1)` | `5/3` | `2/3` at power level |
| transition | continuous large sieve / generic mean value | `7/3+o(1)` | `5/3` | `2/3` |
| high | dyadic Montgomery--Vaughan plus `A^(-2)` | `7/3+o(1)` | `5/3` | `2/3` |

These are disjoint frequency regimes.  Improving one does not bound either
of the other two.

## 4. Vaughan identity verified before estimation

Use the standard convention

```text
Lambda
 = mu_<=U * log
   - Lambda_<=V * mu_<=U * 1
   + 1 * mu_>U * Lambda_>V
   + Lambda_<=V.
```

It follows directly from `Lambda=mu*log`, `log=Lambda*1`, and `mu*1=delta`.
The finite audit evaluates all four Dirichlet convolutions and verifies this
identity pointwise for `1<=n<=200`, with `U=V=5`, before any analytic
estimate is assigned.  The centered coefficient is obtained only afterward:

```text
b(n) = [four Vaughan components] - 1.
```

For the asymptotic audit set

```text
U=V=X^(1/3).
```

On `n asymp X`, the final `Lambda_<=V(n)` term vanishes.  The first two
convolutions are Type I objects with a small factor or small-factor product;
the third is the Type II object with both the Moebius and von Mangoldt
factors above `X^(1/3)`.  All coefficient sequences are bounded by
`X^o(1)` after dyadic decomposition and have the standard length-scale
`L2` norms `length^(1/2) X^o(1)`.

## 5. Why the grouped Vaughan estimate stops

Applying the decomposition to `B_X` gives schematically

```text
B_X = B_TypeI + B_TypeII - B_1
```

on the target dyadic interval.  At very low frequency, the three pieces can
individually have main-term size of order `X polylog X`; their signed sum is
the centered prime polynomial controlled only by the PNT error.  Therefore

```text
|B_X|^2 <= 3(|B_TypeI|^2+|B_TypeII|^2+|B_1|^2)
```

throws away a cross-piece cancellation that is already indispensable at
`alpha=0`.  With coefficientwise or generic mean-value estimates, both the
grouped Type I and Type II energies retain the scale

```text
X H^2 X^o(1) = X^(7/3+o(1)).
```

Keeping their cross terms instead returns to the original signed shifted
correlation `S_off`; Vaughan's identity alone has not estimated it.

The block ledger is therefore:

| grouped object | coefficient information used | available exponent | deficit | missing theorem |
|---|---|---:|---:|---|
| Type I plus centering, very low band | divisor bounds plus classical PNT | `7/3` | `2/3` | power-scale centered prime-sum cancellation |
| nonbalanced Type II, transition band | `L2` coefficient norms plus large sieve | `7/3` | `2/3` | signed spectral non-concentration saving `H` |
| balanced Type II, high band | Montgomery--Vaughan mean value | `7/3` | `2/3` | localized bilinear mean square saving `H` |

The exponent `7/3` is the best bound derived from the explicitly audited
inputs here.  It is not asserted to be an unconditional lower bound or the
best result obtainable by every future treatment of these blocks.

The exact identity is also recorded in
[Helfgott's ternary Goldbach treatment](https://arxiv.org/abs/1501.05438).

## 6. Stop-rule and Guth--Maynard decision

There are three disjoint fixed-power failures, not one unique balanced block.
The preregistered rule therefore requires stopping the Vaughan decomposition.

Guth--Maynard's theorem estimates the number of separated large values of a
multiplicative Dirichlet polynomial

```text
sum_(N<n<=2N) a_n n^(it).
```

The exact Gate C formula instead contains a continuously integrated additive
polynomial `B_X(alpha)` and a two-frequency kernel.  A Perron transformation,
layer-cake argument, one-separated discretization, and coefficient
normalization would all be additional theorems.  More importantly, even a
successful bridge for the balanced Type II block would leave the independent
very-low and transition failures above.  Consequently the unique-failure
precondition is false and no Guth--Maynard exponent is credited.

The same reasoning prevents escalation to a third-order Heath--Brown
identity: the obstruction is not a sole balanced trilinear block.

The current Guth--Maynard theorem and its parameter conditions are recorded
in [arXiv:2405.20552v2](https://arxiv.org/abs/2405.20552).

## 7. Failure certificate

The attempted route would need at least two genuinely new inputs:

1. **Very-low-frequency theorem.**  A power-scale estimate equivalent in
   strength to

   ```text
   B_X(alpha) << X^(2/3+eta),   |alpha| <= X^(-1),
   ```

   or an integrated signed substitute that gives the same `XH` contribution.

2. **Localized signed spectral theorem.**  A Type I/II-stable estimate that
   distributes the `L2` mass of the centered prime polynomial proportionally
   across frequency bands and saves the full factor `H=X^(2/3)` without
   separately squaring away the cancellation between Vaughan components.

A third specialized bilinear theorem may be needed for the balanced high
band, but it is not meaningful to isolate it before the first two inputs
exist.

Because at least two independent new inputs are missing, adding more
conditional energy interfaces or moving to cubic decomposition would not
constitute progress on Gate C.

## 8. Claim and dependency boundary

Closed in this audit:

- the exact continuous double-frequency identity;
- the necessity of retaining the nonconstant-weight frequency coupling;
- finite synthetic and actual-von-Mangoldt identity checks;
- the exact four-term Vaughan identity;
- the exponent ledger under the named existing inputs.

Not closed:

- `J_(2/3)(X) <<_eta X^(5/3+eta)`;
- any of the two new theorems in the failure certificate;
- exclusion of zeta zeros with real part greater than `2/3`.

No RH input, PNT power error, global zero real-part cap, finite-height
certificate, visible-cluster witness, Carlson persistence assumption, or
Guth--Maynard estimate is smuggled into the result.  No Lean interface is
admissible at this stage.
