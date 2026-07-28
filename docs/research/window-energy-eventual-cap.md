# Window energy budgets with eventual cap

`HasFarWindowEnergyBudgets` retains only the two local quantitative inputs:

```text
card(G) * c^2 + K * (C^2 - c^2) < sum_G main(m)^2

sum_{extension-bad points} extension(m)^2 < K * loss^2.
```

The pointwise main bound `|main(m)| <= C` is supplied separately as an
eventual statement.  The verified synchronization theorem selects every
window beyond both the requested lower endpoint and the cap cutoff, producing
`HasFarWindowEnergySeparation`.

This separation is useful for the zeta application because the main cap is a
deterministic consequence of finite coefficient mass, whereas the two energy
budgets are the genuine local analytic inputs.
