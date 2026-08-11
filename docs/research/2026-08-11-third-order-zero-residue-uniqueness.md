# Third-order zero-residue uniqueness

This slice identifies the previously abstract simple-pole coefficient at zero in
the third-order zero-pole regularization.

The new theorem assumes that the compact regularization set `K` is a
neighborhood of zero. This strengthening is necessary: membership `0 ∈ K`
alone does not expose a punctured neighborhood on which Laurent coefficients
can be compared.

The proof removes the finitely many nonzero poles, absorbs their analytic local
contribution into the remainder, and compares the resulting Laurent model with
the intrinsic expansion of the genuine zeta kernel. Successive multiplication
by `z^3`, `z^2`, and `z` identifies the cubic, quadratic, and simple-pole
coefficients. In particular,

```text
residue 0 = iteratedDeriv 2 (thirdOrderZeroCore x) 0 / 2.
```

This is an identification theorem for the zero pole in the smoothed explicit
formula. It does not assert an Omega theorem, RH, or any new zero-free region.
