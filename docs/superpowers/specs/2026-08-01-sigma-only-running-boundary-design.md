# Sigma-Only Running-Boundary Transfer Design

## Objective

Remove `alpha`, `epsilon`, and `beta0` from the Stack 115 interface.  Starting
only from a Carlson threshold `1/2 < sigma < 1`, construct all numerical
parameters needed by the canonical-good-height running-boundary transfer.

## Parameters

Reuse the balanced good-height exponent

```text
alpha(sigma) = (1 - sigma) / 2
```

and choose

```text
epsilon(sigma) = (1 - sigma) / 4.
```

Let

```text
B(sigma) = max(realOrdinatePNTZeroBottleneck,
               sigma + alpha(sigma) + epsilon(sigma))
beta0(sigma) = (B(sigma) + 1) / 2.
```

Since every component of `B` is strictly below one, `B < beta0 < 1`.
Consequently:

- `0 < alpha <= 1` and `0 < epsilon`;
- every real-ordinate nontrivial zero has real part `< beta0`;
- `sigma - beta0 + alpha + epsilon < 0`;
- `1 - beta0 < alpha`.

The last inequality follows because
`sigma + 2 * alpha = 1` and `epsilon > 0`.

## Unified theorem

Specialize Stack 115 with these definitions.  The public theorem accepts only
`sigma`, `eta`, `c`, `loss`, the strip inequalities, and positive/negative
main-package witnesses for the resulting explicit running boundary.

## Claim boundary

This closes all truncation-height and moving-boundary numerical parameters.
The positive and negative anti-cancellation witnesses remain explicit and are
not manufactured by the transfer layer.  No unconditional Omega theorem or RH
claim follows.

Only `ZeroDensityLayerBudget*`, matching contract/audit files, and task
documents are modified.  Protected complementary-bound and Sharp/VK-edge files
remain untouched.

## Verification

Compile implementation, contract, and axiom audit sequentially with the
existing overlay.  The permitted axiom set is `propext`, `Classical.choice`,
and `Quot.sound`.
