# Actual cubic Carlson quantitative moving-tail design

## Scope

This slice closes the gap between fixed-coefficient summability and a dyadic
cut that moves with the PNT scale. It changes only the density/transfer layer.
It does not modify Sharp oscillation, half-isolated Gram/Schur arguments,
`ZeroForcedOscillationComplementaryBound.lean`, or VK-edge modules.

## Theorem chain

For

- `r(sigma) = exp ((q(sigma) - 6) log 2)`,
- `N_gamma(m) = floor (log (m^gamma) / log 2)`,
- block majorant `C (n+1)^5 r(sigma)^(n+1)`,

the module proves the shifted-tail estimate

`tail(N) <= C (N+2)^5 r(sigma)^(N+1) K(sigma)`,

where `K(sigma)` is the convergent fifth-logarithmic geometric series. The
successor in the tail means that the boundary block belongs to the low layer.
No dyadic block is lost.

The floor inequalities then give, eventually,

- `r(sigma)^(N_gamma(m)+1) <= m^(gamma*(q(sigma)-6))`,
- `N_gamma(m)+2 <= (gamma/log 2 + 2) log m`.

After target-amplitude normalization, the exact majorant is

`const * m^e * (log m)^5`,

with

`e = 2*(tau-beta) + gamma*(q(sigma)-6)`.

A generic fixed-log-power absorption theorem proves convergence to zero when
`e < 0`. The joint two-height corollary uses one parameter package and keeps
three distinct cuts:

- `gammaLow`: low probing height,
- `gammaHigh`: Carlson balanced split,
- `alpha`: outer contour height.

## Exponent and logarithm ledger

- Carlson contributes `log^4`.
- Linear-to-square multiplicity control contributes one additional `log`.
- The total loss remains exactly `log^5`; this slice adds no further
  multiplicity or logarithmic loss.
- The reciprocal-cubic square mass supplies denominator power `6`.
- Since `q(sigma) <= 1`, the dyadic polynomial contribution is at most `-5`.
- `e < 0` is strictly decaying and absorbs `log^5`.
- `e = 0` is critical: the formal result does not claim decay.
- `e > 0` is not controlled by this transfer.

## Deliberate boundary

The new conclusion concerns the concrete Carlson `log^5` model majorant with
coefficient scale varying with `m`. It does not yet exchange the existing
pointwise-in-`x` eventual certificate threshold with the diagonal choice
`x = m`. The next slice must expose a uniform certificate threshold or prove a
direct diagonal actual-zeta block estimate before connecting this result to a
smoothed explicit formula. No unconditional Omega theorem or RH consequence is
claimed here.

## Audit plan

The production module has five public definitions and ten public theorems.
The Contract module gives fifteen exact typed examples. The AxiomAudit module
prints axioms for all ten theorems, and the allowlist registers all ten names.
