# Pintz-Carlson-explicit-formula balanced transfer: audited theorem chain

This note records the exact formal boundary of the actual-zeta balanced
transfer chain integrated into `main`. It is a theorem-chain
audit, not an RH claim and not an unconditional oscillation claim.

## 1. Common PNT object

All final transfers act on the same genuine relative Chebyshev error:

```lean
relativeChebyshevPsi0Error
```

The finite visible main term is:

```lean
dynamicVisibleClusterPNTMain
```

The common decomposition has the form

```text
actual relative PNT error
  = visible finite zero cluster
  + signed outside-cluster zero complement
  + real-axis term
  + selected-height contour remainder.
```

The zero contributions use the actual zeta kernel and analytic multiplicity.
Carlson density controls the aggregated outside-cluster positive-zero tail.
Conjugation transfers that control to the complete nonreal zero sum. The
real-ordinate term remains explicit and is not silently discarded.

## 2. Dynamic Carlson residual theorem

The automatic canonical two-strip theorem is:

```lean
selectedUniformGoodHeightActualCarlsonCanonicalTwoStripPNTClusterResidual_automatic
```

It removes the earlier abstract bucket input and the manually supplied
positive norm lower bound. The low strip is the canonical predicate
`rho.re <= sigma`; the high strip is treated by the actual Carlson dyadic
tail.

The balanced specialization is:

```lean
selectedUniformGoodHeightActualCarlsonBalancedPNTClusterResidual_automatic
```

Its conclusion is:

```text
relativeChebyshevPsi0Error - dynamicVisibleClusterPNTMain
  = o(targetZeroPowerAmplitude beta)
```

along natural points, where the selected polynomial height exponent is

```text
alpha = (1 - sigma) / 2.
```

## 3. Exact truncation-height certificate

The contour and low-strip powers require the strict window

```text
1 - beta < alpha < beta - sigma.
```

The formal exact feasibility theorem is:

```lean
actualCarlsonHeightWindow_nonempty_iff
```

It proves:

```text
(exists alpha, 1 - beta < alpha and alpha < beta - sigma)
  iff
(1 + sigma) / 2 < beta.
```

The robust margin is:

```text
min (alpha - (1 - beta)) ((beta - sigma) - alpha).
```

The midpoint is the unique optimizer. The quantitative stability identity is:

```lean
actualCarlsonHeightRobustMargin_eq_balanced_sub_abs
```

which proves:

```text
robustMargin(beta, sigma, alpha)
  = (2 * beta - 1 - sigma) / 2
      - abs(alpha - (1 - sigma) / 2).
```

Thus moving the truncation exponent by `d` loses exactly `abs d` from the
minimum power margin.

## 4. Forward upper and lower transfers

### Empty cluster: zero gap to PNT upper bound

```lean
selectedUniformGoodHeightActualCarlsonBalancedPNTUpperTransfer_automatic
```

With `S = empty`, a global strict real-part gap gives:

```text
relativeChebyshevPsi0Error = o(targetZeroPowerAmplitude beta)
```

along natural points.

This theorem does not derive the strict zero gap from Carlson density. The gap
is an explicit input.

### Finite cluster: conditional unsigned lower transfer

```lean
selectedUniformGoodHeightActualCarlsonBalancedPNTLowerTransfer_automatic
```

An external far-point witness for the visible finite cluster survives in the
actual PNT error with the standard factor `1 / 2` used to absorb the
target-negligible complement.

### Finite cluster: conditional signed lower transfer

```lean
selectedUniformGoodHeightActualCarlsonBalancedPNTSharpSignedTransfer_automatic
```

External positive and negative visible-cluster witnesses with coefficient
`c` transfer to actual PNT witnesses with every coefficient `q` satisfying

```text
0 <= q < c.
```

Neither lower theorem constructs the finite-cluster witness. In particular,
the local pi/2 anti-cancellation theorem belongs to the separate sharp
oscillation task.

## 5. Quantitative reverse transfers

The two-sided reverse theorem is:

```lean
selectedUniformGoodHeightActualCarlsonBalancedPNTEventualUpper_forces_emptyCluster_automatic
```

If the actual PNT error is eventually bounded by `q A_beta`, while any
nonempty visible cluster would have a `c A_beta` far-point witness and
`q < c`, then the cluster is empty.

The one-sided versions are:

```lean
selectedUniformGoodHeightActualCarlsonBalancedPNTEventualUpper_forces_emptyCluster_of_positiveWitness_automatic

selectedUniformGoodHeightActualCarlsonBalancedPNTEventualLower_forces_emptyCluster_of_negativeWitness_automatic
```

They require only the corresponding one-sided PNT bound and signed cluster
witness.

These reverse theorems do not imply RH. They are conditional exclusion
principles with explicit zero-gap and cluster-witness inputs.

## 6. Remaining mathematical hypotheses

The actual Carlson-explicit-formula residual machinery is internalized, but
the following assumptions remain external:

1. `S` is a finite conjugation-invariant cluster.
2. Every actual positive zero outside `S` and to the right of the Carlson
   low strip has real part strictly below `beta`.
3. Every real-ordinate nontrivial zero outside `S` has real part strictly
   below `beta`.
4. For lower or reverse oscillation conclusions, the visible cluster supplies
   the required unsigned or signed far-point witness.
5. Balanced feasibility requires `(1 + sigma) / 2 < beta`.

Assumption 2 is the main density/oscillation boundary. Carlson density bounds
how many zeros occur in strips; it does not by itself make every zero outside
a fixed finite cluster satisfy a strict pointwise real-part gap.

If another zero has the same real part as the target and is not in `S`, it is
not target-negligible under the present pointwise-gap theorem. It must be
included in the visible cluster or handled by a separate anti-cancellation
argument.

## 7. Validation boundary

Each module in this chain has:

1. a focused `lake -Kjobs=1 build`;
2. a contract file checking the exported declarations;
3. a focused axiom audit.

The audited declarations report only:

```text
[propext, Classical.choice, Quot.sound]
```

No Guth-Maynard theorem, zero-reproduction tree, unconditional Omega theorem,
or RH theorem is asserted by this chain.
