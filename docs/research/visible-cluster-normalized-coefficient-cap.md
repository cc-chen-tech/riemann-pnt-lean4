# Visible-cluster normalized coefficient cap

For a finite visible cluster `E` with

```text
rho.re <= beta  for every rho in E,
```

the existing coefficient-mass estimate gives, for natural `m >= 1`,

```text
|dynamicVisibleClusterPNTMain T E m|
  <= finiteVisibleClusterCoefficientMass(E)
       * targetZeroPowerAmplitude beta m.
```

The target amplitude is positive there, so the new verified theorem divides
through and obtains the eventual normalized cap

```text
|dynamicVisibleClusterPNTMain T E m
    / targetZeroPowerAmplitude beta m|
  <= finiteVisibleClusterCoefficientMass(E).
```

Consequently, reduced `HasFarWindowEnergyBudgets` for this normalized seed
automatically produce `HasFarWindowEnergySeparation`.  The pointwise cap is no
longer an independent analytic hypothesis.
