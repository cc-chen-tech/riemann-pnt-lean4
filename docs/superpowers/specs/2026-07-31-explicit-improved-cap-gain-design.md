# Explicit Improved Cap Gain Design

## Goal

Convert the implicit improved cap threshold into a closed rational expression
in `beta` and quantify exactly how much of the old canonical-to-`beta` gap is
recovered.

## Canonical density exponent

At

```text
c(beta) = (3 * beta - 1) / 2,
```

the Carlson density exponent is

```text
Q(beta) = 3 * (3 * beta - 1) * (1 - beta).
```

Therefore the improved threshold becomes

```text
thetaGlobal(beta)
  = beta - (1 - beta) * Q(beta)^2 / (Q(beta) + 1).
```

## Gain factorization

Subtracting the old canonical threshold gives

```text
thetaGlobal(beta) - c(beta)
  = (1 - beta) * (1 - Q(beta)) * (2 * Q(beta) + 1)
      / (2 * (Q(beta) + 1)).
```

Every factor has a controlled sign for `2 / 3 < beta < 1`.

## Relative gain

Normalize by the full old gap `beta - c(beta)`. The recovered fraction is

```text
(1 - Q(beta)) * (2 * Q(beta) + 1) / (Q(beta) + 1),
```

and lies strictly between zero and one.

## Boundary

These formulas quantify the internal Carlson-model optimization. They do not
alter the external zero-density input.
