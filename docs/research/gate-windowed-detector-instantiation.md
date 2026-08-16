# Gate instantiation via the windowed detector: paper specification

## Status

Specification of goal step (4): how the L1-L3 windowed detector closes the
gate inputs `hbranch` and `hgap` (and hence the whole exclusion of
`Re rho > 2/3`).  Complements `windowed-detector-lean-spec.md` and the
L1-L3 documents.  No theorem claims.

## Counterfactual setup

Assume a non-trivial zero `rho_0 = beta + i gamma_0` with `2/3 < beta < 1`,
`gamma_0 > 0` (the seed).  Fix

```text
sigma  in (2/3, beta)          (Carlson threshold),
gap    in ((1-h') gamma0 / lambda,  beta - sigma)   (feasible by L3),
T0, H  with  H = X^(gamma0 h'),  h' in (0,1),
delta  with  2 delta <= H / q_count  (window separation),
```

where `q_count` is the target branching degree per node.

## Instantiation of the six gate inputs

| gate input | instantiation |
|------------|---------------|
| `hroots` | `roots T = {rho_0}` (the seed); nonempty for all `T` |
| `hbranch` | for each node `rho` in layer `n` and each separated window
  `[T0, T0+H]` in the layer band, the L3 conclusion gives a top-layer
  (real part `beta`) zero in that window; `q(T) = H / (2 delta) = T^(h'-kappa)` |
| `hdisjoint` | windows separated by `2 delta` are disjoint
  (`topLayerWindow_disjoint_of_imag_separation`, already proved) |
| `C` | `windows n T` = the separated window index set at layer `n`,
  `cluster n i` = the L3-produced zero in window `i`,
  `windowStart n i` = the window lower edge, `localContribution = 1` |
| `hlower` | each produced zero has `Re = beta > sigma`, imaginary part in
  the window; counted into `zeroDensityCount sigma (T+H)` via the existing
  `disjointWindowFamilyLowerCount_eventually_le_zeroDensity` bridge |
| `hgap` | `q(T)^depth = T^((h'-kappa) depth)` vs the Carlson majorant
  `C (T+H)^(4 sigma (1-sigma)) log^4`; closes once
  `(h' - kappa) * depth > 4 sigma (1-sigma)` |

## Layer arithmetic (why depth stays bounded)

Layer `n` nodes have imaginary parts in a band of width `H` above the
previous layer (the L3 windows), so the `n`-th layer lies in
`[gamma_0, gamma_0 + n H]`; requiring `n H <= T0` bounds the depth by
`T0 / H = T^(1 - h')` — no constraint for fixed depth in the gate
statement.  With `kappa = 0` (constant `delta`), the growth exponent is
`h'` and the gate closes for `h' * depth > 4 sigma (1-sigma) < 8/9`;
for example `h' = 0.6` needs `depth > 0.889/0.6 ~ 1.5`, i.e. depth 2
suffices.

## Remaining analytic obligations (after L1-L3)

1. The L3 conclusion must be uniform over the finite window family (the
   L3 hypotheses hold for each window with the same constants).
2. `hlower`'s ambient set: the produced zeros are genuine non-trivial
   zeros (`RiemannHypothesis.IsNontrivialZero`), which is part of the L3
   conclusion.
3. The seed layer: the directed iteration starts from `rho_0`; the first
   L3 application needs the seed's own oscillation signal as input, which
   is exactly the vk-edge `[Y, Y^7]` strict `pi/2 + delta` witness
   (`vk-edge-pi-over-two-carlson-transfer.md`) — that module is the
   seed-signal supplier and must be imported read-only.

## Resulting main theorem (goal step 5, shape)

```text
theorem no_nontrivial_zero_re_gt_two_thirds :
    ∀ ρ, RiemannHypothesis.IsNontrivialZero ρ → ρ.re ≤ 2/3
```

by contradiction: a seed with `2/3 < beta` supplies the six inputs
(instantiation above), `amplificationGate` yields `False`, and
`amplificationGate_excludes_seed` finishes.  Axiom audit must print only
the base axioms once all inputs are theorems.

## Boundaries

Specification only; promotion order L1 -> L2 -> L3 -> this instantiation
-> the main theorem.
