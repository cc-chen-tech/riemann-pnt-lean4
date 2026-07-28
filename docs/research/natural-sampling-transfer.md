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
constant loss.  The remaining analytic task is to prove the two normalized
limits for the actual finite equal-real-part zeta-zero package.
