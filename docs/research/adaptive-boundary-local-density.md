# Adaptive local-density input at a target zero boundary

## Required growth rate

Let `gap(m)` be the real-part separation between a target zero and the
visible complementary zeros.  Let `densityLogCost(m)` be the logarithm of
the effective local zero-count cost used to majorize that complement.

The exact target-normalized logarithmic margin is

```text
gap(m) * log m - densityLogCost(m).
```

The new admissibility condition requires this quantity to tend to positive
infinity.  It then yields

```text
exp (densityLogCost(m) - gap(m) * log m) -> 0.
```

In particular, admissibility necessarily implies eventually

```text
densityLogCost(m) < gap(m) * log m.
```

Pointwise strict inequality alone is not claimed to be sufficient.

## A usable sufficient condition

For any fixed `epsilon > 0`, it is sufficient that

```text
gap(m) * log m -> infinity
```

and eventually

```text
densityLogCost(m)
  <= (1 - epsilon) * gap(m) * log m.
```

This makes the missing local zero-density input quantitative and auditable:
it must save a fixed fraction of the available gap-logarithm budget.

## Relation to the classical Carlson route

Taking

```text
densityLogCost(m) = q * logHeight(m)
```

recovers definitionally the existing moving-density margin

```text
gap(m) * log m - q * logHeight(m).
```

The boundary-slope-floor theorem shows why the classical Carlson choice has
insufficient flexibility when the actual gap tends to zero.  A successful
replacement must supply a genuinely smaller local cost, not merely move the
same global Carlson strip threshold.

## Formalization boundary

The module instantiates the majorant with the selected gap of the actual
dynamic equal-real-part zeta-zero package.  It does not prove an estimate for
`densityLogCost`, formalize Guth--Maynard, establish the full complementary
zero-sum domination, prove an unconditional Omega theorem, or imply RH.
