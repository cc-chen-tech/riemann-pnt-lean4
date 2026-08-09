# Exceptional-zero right-strip localization audit

## Existing adjacent endpoint

The dynamic packet stack already contains a strong maximal-layer theorem:

```text
exists_uniformDynamicMaximalLayerAbsorption_of_fullMovingGaussianL2_gt
```

Under its explicit large-energy inequality, it returns a bucket packet `P`
such that

```text
P.Nonempty
Disjoint S P
P ⊆ nontrivialZerosFinset T
S.card < (S ∪ P).card
∀ rho ∈ P, rho.re = dynamicMaximalComplementRealPart S T.
```

Thus the packet extraction, duplicate removal, strict cardinality increase,
and maximal-real-part localization are already proved.  Gate B should not
reimplement them.

## Why it does not yet compose with the Sharp lower bound

The maximal-layer theorem requires

```text
2 * (
  2 * eta
  + real-band drift budget
) + 2 * outside-band energy bound
  < full moving complement energy
```

at

```text
beta = dynamicMaximalComplementRealPart S T.
```

The available unconditional Sharp theorem instead gives a positive lower
bound

```text
C(rho, epsilon)
  < full moving complement energy
```

only for

```text
S = ∅
beta = rho.re
```

on a selected sufficiently late height.

The current library does not prove any of the following required bridges:

1. the Sharp lower bound persists for the updated finite set `S`;
2. the lower bound transfers from the fixed anchor `rho.re` to
   `dynamicMaximalComplementRealPart S T`;
3. the positive lower bound dominates the maximal-layer real-band drift
   budget;
4. it dominates the outside-band energy term uniformly along the iteration.

Therefore the antecedent of the maximal-layer extraction theorem cannot be
constructed from the current Sharp endpoint.

## Carlson membership still needs positive ordinate

The maximal-layer packet proves an exact real-part identity, so

```text
sigma < dynamicMaximalComplementRealPart S T
```

would imply `sigma < rho.re` for every packet member.

However the packet is built from `|rho.im|` buckets.  Its members are not
oriented to positive ordinate, while
`ZeroDensity.zeroDensityZerosFinset sigma T` requires

```text
0 < rho.im
sigma < rho.re.
```

No current packet endpoint returns the positive-ordinate membership directly.
A conjugation-closed state could plausibly orient each nonreal packet pair,
but the required closure and nonreal-zero bridge are not part of the current
theorem signature.

## Minimum upstream theorem that would unlock Gate B

A directly composable result should have the following output shape:

```text
∀ finite S,
  S ⊆ ZeroDensity.zeroDensityZerosFinset sigma T_old
  -> sufficiently late admissible window
  -> ∃ T_new P,
       T_old < T_new
       ∧ P.Nonempty
       ∧ Disjoint S P
       ∧ P ⊆ ZeroDensity.zeroDensityZerosFinset sigma T_new.
```

Alternatively, the existing maximal-layer theorem becomes usable if upstream
analysis supplies all of:

```text
sigma < dynamicMaximalComplementRealPart S T
the maximal-layer large-energy antecedent
positive-ordinate orientation of the extracted packet.
```

Once either output exists, Gate B only needs the already proved update

```text
S' = S ∪ P
```

and no new analytic argument.

## Claim boundary

The maximal-layer packet machinery is real and substantial, but its
large-energy antecedent is not supplied by the current Sharp theorem.
Right-strip iterative growth, a Carlson contradiction, zero exclusion, and
the Riemann hypothesis remain unproved.
