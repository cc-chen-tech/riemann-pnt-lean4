# Selected-height two-height full-tail design

## Motivation

A fixed polynomial contour height need not be a good height: it may pass
arbitrarily close to a zeta zero.  Therefore the polynomial remainder
certificate in stack40 cannot be manufactured from a good-height theorem.

The correct repair is to use a selected height `H x` satisfying

```text
0 <= H x <= x ^ alpha
```

eventually, while retaining the polynomial envelope for zero counting.

## Low canonical layer

Split the selected layer at `x ^ gamma`.

- The low-ordinate subset is still counted by global zero multiplicity at
  `x ^ gamma`.
- The high-annulus subset lies below `H x <= x ^ alpha`, so it is counted by
  global zero multiplicity at `x ^ alpha`.
- Its kernel still gains the denominator `x ^ gamma`.

Thus the stack37 majorants and exponent margins are unchanged.

## High canonical layer

Under the same real-part cap, every selected high-layer zero lies in

```text
actualPositiveCarlsonStrip sigma tau (x ^ alpha)
```

because its ordinate is at most `H x <= x ^ alpha`.  Stack36 therefore
controls the selected high layer without a new density estimate.

## Full tail

The selected positive tail is assembled from the two canonical layers.
Conjugation and the arbitrary-height real-ordinate theorem then give the
complete selected-height outside-cluster tail.

## Claim boundary

This stack does not choose `H`.  It proves the tail theorem for any eventually
nonnegative selected height dominated by the polynomial envelope.  The next
stack will instantiate it with an actual good-height remainder certificate.
