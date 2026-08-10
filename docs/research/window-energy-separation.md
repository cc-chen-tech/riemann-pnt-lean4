# Window energy separation

## Quantitative finite criterion

Let `G` be a finite window and `K` a natural cutoff.

For a main sequence with threshold `c` and pointwise cap `C`, the verified
criterion

```text
card(G) * c^2 + K * (C^2 - c^2)
  < sum_G main(m)^2
```

with `0 <= c < C` forces more than `K` points satisfying

```text
c <= |main(m)|.
```

For a complementary sequence and positive threshold `loss`, the criterion

```text
sum_{extension-bad points} extension(m)^2 < K * loss^2
```

forces fewer than `K` extension-bad points.

Combining the two inequalities gives the strict cardinality advantage required
by `HasFarWindowCardAdvantage`.

## Mathematical boundary

The module proves finite real inequalities only.  In the zeta application,
one still needs:

```text
a local lower square-sum estimate for the seed cluster;
a usable pointwise cap for that cluster;
an upper square-sum estimate for the normalized extension.
```

It does not supply these analytic estimates and does not assert an
unconditional oscillation theorem.
