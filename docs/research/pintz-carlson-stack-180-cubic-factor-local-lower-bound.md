# Stack 180: Local lower bound for the cubic de-smoothing factor

## Goal

Prove that the explicit local factor isolated in Stack 179 does not erase the
ordinary reciprocal-zero amplitude for a fixed nonzero zero frequency.

## Theorem chain

1. The derivative of the complex exponential at zero gives

   ```text
   (exp(q) - 1) / q -> 1
   ```

   through nonzero complex `q` tending to zero.
2. Multiplication by a fixed nonzero `rho` is a homeomorphism of the punctured
   complex neighborhood of zero.  Therefore

   ```text
   ((exp(rho * h) - 1) / (rho * h))^2 -> 1
   ```

   through nonzero `h` tending to zero.
3. The factor norm is eventually strictly greater than `1/2`.
4. Combining this with Stack 179's exact normalized second-difference identity
   proves

   ```text
   (1/2) * norm(exp(rho * u) / rho)
     < norm(Delta_h^2 (exp(rho * .) / rho^3)(u) / h^2)
   ```

   for all sufficiently small nonzero complex `h`.

## Claim boundary

The result is local for one fixed nonzero `rho`.  It does not provide a single
step size uniform over a moving or unbounded zero cluster.  It does not prove
the second-Riesz Perron formula, compare finite differences with
`chebyshevPsi`, or bound the corresponding contour remainder.  In particular,
it is an amplitude-retention lemma, not an unconditional Omega theorem.
