# Scaled window energy separation

Suppose both the main and extension sequences are normalized by the same
eventually positive amplitude.  The verified scaling theorem transports

```text
mainThreshold <= |main / amplitude|
extensionThreshold <= |extension / amplitude|
```

to the unnormalized predicates

```text
mainThreshold * amplitude <= |main|
extensionThreshold * amplitude <= |extension|.
```

Every finite window is selected beyond the eventual-positivity cutoff, so both
division implications preserve order.

Combining this with `HasFarWindowEnergySeparation` gives a direct route from
normalized main/extension energy budgets to the unnormalized cardinality
advantage consumed by the visible-cluster anti-cancellation transfer.
