# L3 defect record: node self-contamination kills the directed windowed detector

## Status

This records a mathematical defect found while checking the L3 paper
specification (`windowed-detector-L3-threshold.md`).  The defect is
fundamental for the *directed* use of the windowed detector; it does not
affect the L1/L2 analytic lemmas themselves.

## The defect

The L3 decomposition claimed the "outside top layer" contribution (A) is
negligible versus the seed with ratio

```text
~ C' (T1/T0)^2 log^3 T1 / H.
```

Rechecking with `H = X^(gamma0 h')`, `T1 ~ X^gamma0`:

```text
(T1/T0)^2 / H ~ X^(2 gamma0) / X^(gamma0 h') = X^(gamma0 (2 - h')) -> infinity
```

for every `h' < 2`.  **A is NOT negligible; the L3 feasibility check was
wrong.**

The deeper reason: the detection frequency `gamma'` is eta-avoided from
every window-exterior zero, including the *node itself* (its imaginary
part is the window's left endpoint).  The node's own contribution to the
response is `~ X^(lambda beta)/|gamma' - gamma_node| >= X^(lambda beta)/eta`
with `1/eta ~ T1 log T1 / H`, i.e. huge and *known*: the response is large
because the node exists, so a large response cannot force a NEW zero
inside the window.  The "response exceeds the complementary envelope"
argument is contaminated by the node's own term.

This is the quantitative form of the earlier Gap 2 (no imaginary-part
control), and it is not repairable by eta-avoidance alone: subtracting the
node's own term needs a lower bound for the residual frequency content of
`psi(x)-x` at `gamma'`, which the vk-edge sup-norm witness does not
provide (it is frequency-blind).

## Consequence

The windowed-detector route for the *directed branching* (`hbranch` with
strictly higher imaginary parts) is **closed until a new mechanism
supplies a frequency-resolved lower bound for the residual**.  The L1/L2
lemmas remain valid analytic tools and may be reused by other routes.

## Replacement route (single-layer forcing, partial result)

See `single-layer-forcing-beta-14-17.md`: one layer of the coherent
energy forcing already contradicts Carlson for seed real parts
`beta > 14/17`, with NO directed iteration, NO windowed detector, and NO
dynamic separation.

## Boundaries

Defect record; L1/L2 drafts unchanged, L3 directed use withdrawn.
