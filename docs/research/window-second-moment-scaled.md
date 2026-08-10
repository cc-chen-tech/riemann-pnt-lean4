# Scaled window second-moment bridge

The verified bridge starts from a normalized remainder

```text
u(m) = remainder(m) / amplitude(m)
```

and assumes:

```text
threshold > 0
eventually 0 < amplitude(m)
HasFarWindowSecondMomentAdvantage good u threshold.
```

It concludes:

```text
HasFarWindowCardAdvantage
  good
  (fun m => threshold * amplitude(m) <= |remainder(m)|).
```

The proof chooses every finite window beyond both the requested lower bound
and the eventual-positivity cutoff.  Division by the amplitude is therefore
order preserving throughout that window.

For the zeta application, `amplitude(m)` is
`targetZeroPowerAmplitude beta m`, which is already known to be eventually
positive on natural points.  A zeta-specific normalized second-moment estimate
is still an external analytic input.
