# Actual local multiplicity to weighted Occupancy

## Existing production input

The repository already defines

```lean
PrimeNumberTheorem.ExplicitFormulaAux.localZeroMultiplicity
```

at
`PrimeNumberTheorem/QuantitativeGoodHeight.lean`.  For `A >= 4`, it is the
total analytic multiplicity of actual nontrivial zeta zeros satisfying

\[
  A-\frac14\le |\Im\rho|\le A+\frac54.
\]

The same module proves

```lean
exists_localZeroMultiplicity_le_log_bound
```

with conclusion

\[
  \operatorname{localZeroMultiplicity}(A)
  \le B(1+\log(A+6)).
\]

This is stronger than a distinct-ordinate count: every zero is already
weighted by `analyticOrderNatAt riemannZeta rho`.

No new Jensen theorem or Riemann--von Mangoldt asymptotic is needed for the
weighted-Schur row bound.

## 1. Unit signed-ordinate adapter

Let `u >= 15/4`.  Set

\[
  A=u+\frac14.
\]

Then

\[
  [u,u+1]
  \subset
  \left[A-\frac14,A+\frac54\right]
  =[u,u+3/2].
\]

Consequently every family of actual zeta zeros whose absolute ordinates lie
in `[u,u+1]` has total analytic multiplicity at most

\[
  B\left(1+\log\left(u+\frac{25}{4}\right)\right).
\]

For a signed interval contained in the positive half-line, apply this directly.
For a signed interval contained in the negative half-line, reflect it by
`gamma -> |gamma|`.  Intervals meeting zero contain no member of a dyadic
shell `T <= |gamma| < 2T` when `T >= 4`, after intersecting with the shell.

Thus a single theorem can state that every signed interval of length at most
one, intersected with an actual dyadic shell at `T >= 4`, has multiplicity
mass at most

\[
  U(T)=B(1+\log(2T+8)).
\]

The harmless `+8` avoids endpoint bookkeeping.

## 2. Long Fejer observation window

This adapter uses a long observation window in the logarithmic variable.  It
must not be confused with the short triangle used to desmooth the cubic
explicit formula.

For the target interval

\[
  x\in[X,X^{1+\varepsilon}],
\]

put

\[
  u_0=\left(1+\frac\varepsilon2\right)\log X,
  \qquad
  L=\frac\varepsilon2\log X.
\]

The translated normalized triangle

\[
  W_{u_0,L}(u)
  =\frac1L\left(1-\frac{|u-u_0|}{L}\right)_+
\]

has support exactly

\[
  [\log X,(1+\varepsilon)\log X].
\]

Its frequency kernel is a phase times

\[
  \left(\frac{\sin(Lv/2)}{Lv/2}\right)^2,
\]

so its absolute value is at most

\[
  \min\left(1,\frac4{L^2v^2}\right).
\]

Translation does not change the absolute kernel bound.

## 3. Formalization-friendly row constant

Fix one frequency `gamma_i`.  Assume `L >= 1`.  Partition the remaining
frequencies into

\[
  B_0=\{j:|\gamma_j-\gamma_i|<1/L\}
\]

and

\[
  B_k=\{j:k/L\le|\gamma_j-\gamma_i|<(k+1)/L\},
  \qquad k\ge1.
\]

The near set is covered by two intervals of length `1/L`, hence has analytic
multiplicity at most `2U(T)`.  Each `B_k` is also covered by two such
intervals.  Therefore

\[
\begin{aligned}
  \sum_jm_j
  \min\left(1,\frac4{L^2(\gamma_i-\gamma_j)^2}\right)
  &\le 2U(T)+8U(T)\sum_{k\ge1}\frac1{k^2}\\
  &\le 18U(T).
\end{aligned}
\]

The last line uses the elementary bound

\[
  \sum_{k\ge1}\frac1{k^2}\le2,
\]

which can be formalized by telescoping

\[
  \frac1{k^2}\le\frac2{k(k+1)}.
\]

The constant `18` is intentionally preferred to an exact `pi^2` constant.
It removes an irrelevant special-function dependency while preserving the
polynomial and logarithmic exponents.

## 4. Why the existing mean-square theorem is not enough

`PrimeNumberTheorem.DirichletPolynomial.finiteExponentialSum_meanSquare_le`
already expands the interval mean square and bounds each off-diagonal integral
by a reciprocal frequency gap.  Its interface assumes

```lean
Set.InjOn omega S
```

and therefore does not directly apply when distinct zeta zeros have the same
ordinate.  Grouping equal ordinates before using it would require a separate
fiber estimate and would obscure analytic multiplicity.

The multiplicity-weighted Schur theorem should instead permit repeated
frequencies.  Its diagonal and equal-frequency terms are absorbed by the
weighted row mass.  This is not merely a convenience: it prevents an
unjustified simplicity assumption.

## 5. Actual-zeta energy ledger

For a dyadic strip

\[
  Z=\{\rho:\sigma_L\le\Re\rho<\sigma_R,
              T\le|\Im\rho|<2T\},
\]

Carlson supplies

\[
  \sum_{\rho\in Z}m(\rho)
  \ll T^{q(\sigma_L)}(1+\log T)^4.
\]

The reciprocal square in the explicit-formula coefficients gives

\[
  \sum_{\rho\in Z}
  \frac{m(\rho)}{|\rho|^2}
  \ll T^{q(\sigma_L)-2}(1+\log T)^4.
\]

The actual weighted row bound contributes `U(T)`, hence one further logarithm:

\[
  \mathcal E_Z
  \ll
  X^{2\kappa_\lambda(\sigma_R-\beta)}
  T^{q(\sigma_L)-2}
  (1+\log T)^5.
\]

Here

\[
  \kappa_\lambda(a)=
  \begin{cases}
    a,&a\le0,\\
    \lambda a,&a\ge0,
  \end{cases}
\]

is the correct support function for `x in [X,X^lambda]`.

There is no maximum-multiplicity logarithm and no polynomial Occupancy
exponent.  The only local loss is the actual multiplicity-weighted
`O(log T)` zero count.

## 6. Deleting the target cluster

Let `S` be any finite target cluster.  Restricting `Z` to `Z \ S` decreases:

- the weighted row sum;
- the linear reciprocal-square coefficient mass;
- the resulting nonnegative majorant.

The same block estimate therefore holds with the same constant.  This is the
only interface needed between the capacity side and the owner of the sharp
finite-cluster lower bound.

## 7. Minimal Lean theorem chain

The next production slice should be narrow.

1. A generic finite weighted-Schur inequality allowing repeated frequencies.
2. A subset-monotonicity corollary.
3. A unit signed-ordinate mass adapter from
   `exists_localZeroMultiplicity_le_log_bound`.
4. A finite-bin row estimate with the explicit constant `18`.
5. An actual dyadic Carlson energy theorem with polynomial exponent
   `q(sigma_L)-2` and log loss five.
6. The same actual theorem after deletion of an arbitrary finite set.

The slice must not reprove the sharp energy lower bound, Gram separation, or
the final sign-selection theorem.
