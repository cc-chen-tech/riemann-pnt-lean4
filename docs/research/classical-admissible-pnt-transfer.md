# Classical admissible PNT transfer

## Completed actual chain

The theorem
`exists_classicalAdmissibleSelectedHeight_relativePNT_tendsto_zero`
combines the following proved inputs at one selected height:

```text
classical zeta zero-free region
  -> height-dependent right edge
  -> constrained optimal rate min(1, sqrt(b))
  -> unit-window analytic good height
  -> complete multiplicity-weighted finite zero sum / m -> 0
  -> contour remainder / m -> 0
  -> fixed explicit-formula terms / m -> 0
  -> relativeChebyshevPsi0Error(m) -> 0.
```

The conclusion is

```text
(chebyshevPsi0(m) - m) / m -> 0
```

along natural samples.

## What is new in this route

This is not merely an invocation of the repository's pre-existing PNT
asymptotic theorem.  The proof passes through:

- an actual selected good height at the constrained optimizer;
- the actual finite zeta-zero sum with analytic multiplicities;
- the actual natural-point truncated explicit-formula certificate;
- the exact dynamic margin `rate * alpha < b`.

The zero sum and contour remainder use the same selected height, so there is
no hidden interchange of existential good heights.

## Boundary

This theorem is an upper-bound transfer from the proved classical zero-free
region.  It does not use Carlson density because the global classical
right-edge cap already controls every zero in the truncation.

The next density-specific step is to replace that global cap by a stripwise
height-dependent profile and sum the resulting layer budgets with Carlson.
No oscillation or RH conclusion is asserted here.
