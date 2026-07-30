# Natural sampling of a far amplitude witness

The module `ZeroDensityLayerBudgetNaturalSamplingTransfer.lean` gives the
precise bridge needed to sample a real-variable far witness at natural
arguments.

For a real function `f`, amplitude `A`, and `q < 1`, it is enough that

```text
A(floor x) / A(x) -> 1
|f(floor x) - f(x)| / A(x) -> 0
```

with `A(x) > 0` eventually.  Then

```text
HasFarTargetAmplitudeWitness f A
```

implies

```text
HasFarNaturalPointTargetAmplitudeWitness
  (fun m => f m)
  (fun m => q * A m).
```

The result keeps every strict fraction `q < 1`; it does not hide a fixed
constant loss.

The module also proves automatically that

```text
targetZeroPowerAmplitude beta (floor x)
  / targetZeroPowerAmplitude beta x -> 1,
```

including after multiplication by any fixed nonzero coefficient.  Thus the
only remaining analytic sampling limit for the actual package is the
normalized variation of its finite visible zero sum over a unit interval.
