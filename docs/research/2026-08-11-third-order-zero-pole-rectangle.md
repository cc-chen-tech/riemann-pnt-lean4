# Third-order zero-pole rectangle formula

## Result

The genuine third-order explicit-formula kernel now has a closed
axis-parallel rectangle formula with a negative left edge:

    a < 0 < c,    W > 0.

When every genuine nonzero pole on the compact rectangle is strictly in its
interior, there are finitely many poles, including zero, such that

    boundary integral = 2*pi*i * sum(residue(p)).

For each nonzero zeta zero p, the residue retains the cubic Perron scale

    -multiplicity(p) * x^p / p^3.

The cubic principal coefficient at zero remains

    -zeta'(0) / zeta(0).

## Zero-pole assembly

The zero-pole regularization decomposes the kernel into an analytic remainder,
a finite simple-pole sum, and quadratic and cubic principal parts at zero.
This slice proves the required four-edge integrability and then uses:

- the existing finite simple-pole rectangle formula;
- vanishing of the closed boundary integral of z^(-2);
- vanishing of the closed boundary integral of z^(-3).

Therefore the higher principal parts do not alter the residue sum, even though
they are essential in the local meromorphic decomposition.

## Scope

This closes the negative-left-edge rectangle identity itself. It does not yet
identify the simple residue at zero in closed form, connect the corrected
residue sum to the second-smoothed Chebyshev function, bound the Carlson
medium/high zero tail, prove an Omega theorem, or imply RH.
