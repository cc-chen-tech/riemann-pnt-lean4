# Pintz-Carlson concrete instantiation audit

## Scope

This note separates the analytic variables needed to instantiate the abstract
dynamic transfer machine. It is deliberately not a claim of a new numerical
PNT error exponent, a formalization of Guth-Maynard density estimates, or a
proof of RH.

The relevant existing project inputs are:

- `Pintz.tendsto_pintzZeroEnvelope_atTop`;
- `Pintz.exists_eventually_two_mul_sqrt_le_zeroEnvelope`;
- `carlson_zeroDensity_isBigO`;
- `constructPintzCarlsonUnifiedDynamicZeroTransfer`;
- `constructPintzCarlsonUnifiedDynamicZeroTransferSigned`.

## Two variables that must not be identified

Write

```text
E(x) = inf_rho ((1 - Re rho) log x + log(Im rho)).
```

The current `pintzZeroEnvelope` is an instance of `E`. Its proved growth

```text
E(x) >= 2 sqrt(c log x)
```

eventually implies decay of individual zero terms of the form `exp(-E(x))`.
It is not a truncation height.

Write `H(x)` for the height at which the explicit formula is truncated.
Carlson controls the number of zeros up to this second variable:

```text
N(sigma, H) = O(H^(4 sigma (1 - sigma)) (log H)^4)
```

for each fixed `1/2 < sigma < 1`.

Consequently a sound transfer must retain both arguments:

```text
Pintz envelope:      E(x)
truncation schedule: H(x)
zero count:          N(sigma, H(x))
kernel weight:       W(x, sigma, H(x))
```

The bridge is a product estimate, not an equality between `E` and `H`:

```text
layerTerm(x, sigma, H(x))
  <= W(x, sigma, H(x)) * N(sigma, H(x)).
```

## Fixed-strip Carlson chain

For a finite strip set `{sigma_i}`, the existing Carlson theorem can be used
strip by strip.

1. Extract constants `C_i` and thresholds `T_i` from
   `carlson_zeroDensity_isBigO`.
2. Use `H(x) -> infinity` to obtain `H(x) >= T_i` eventually.
3. Define

   ```text
   M_i(T) = C_i T^(4 sigma_i (1 - sigma_i)) (log T)^4.
   ```

4. Prove the eventual count bound

   ```text
   N(sigma_i, H(x)) <= M_i(H(x)).
   ```

5. Factor each layer estimate as

   ```text
   layerTerm_i(x, H(x))
     = (W_i(x, H(x)) * M_i(H(x)))
       * (N(sigma_i, H(x)) / M_i(H(x))).
   ```

6. Prove the normalized density factor is eventually bounded by `1`.
7. Prove the genuinely analytic condition

   ```text
   W_i(x, H(x)) * M_i(H(x)) -> 0.
   ```

Steps 5-7 instantiate `CarlsonKernelMajorantLayerAdapter`. Finiteness of the
strip set then turns stripwise decay into decay of the total layer budget.

## Required growth inequality

Suppose a strip kernel admits the schematic estimate

```text
W_i(x, H) <= exp(-A_i(x)) * H^(-b_i) * (log H)^(-d_i).
```

Carlson gives exponent

```text
a_i = 4 sigma_i (1 - sigma_i).
```

The sufficient decay condition is therefore

```text
exp(-A_i(x))
  * H(x)^(a_i - b_i)
  * (log H(x))^(4 - d_i)
  -> 0.
```

This is the quantitative condition that candidate schedules must satisfy.
The statement `H(x) -> infinity` alone is insufficient when `a_i > b_i`.

After taking logarithms, a convenient sufficient form is

```text
A_i(x)
  - (a_i - b_i) log H(x)
  - (4 - d_i) log log H(x)
  -> infinity.
```

This inequality is the correct place to combine Pintz envelope growth with a
Carlson density exponent. For example, if `A_i(x)` is bounded below by a
positive multiple of `E(x)`, then the proved lower bound
`E(x) >= 2 sqrt(c log x)` supplies an explicit budget against the growth of
`H(x)`.

## Candidate-height optimization

The formal optimizer currently chooses exactly from a finite grid. A concrete
instantiation must provide candidates `H_j(x)` such that:

- every `H_j(x)` is positive;
- the grid is nonempty;
- every candidate is eventually in the required zero-free regime;
- the minimum candidate tends to infinity;
- each candidate satisfies the stripwise growth inequality above;
- the explicit-formula cost is bounded by the modeled layer, truncation, and
  compact terms.

The finite-grid optimizer then gives:

- exact minimality among the candidates;
- an additive-slack comparison with any globally admissible height;
- eventual zero-freeness of the selected height;
- divergence of the selected height.

It does not yet prove that the selected height is the continuous global
minimizer over all positive real heights.

## Absolute and signed lower bounds

The absolute transfer needs:

```text
HasFarNormWitness main amplitude
remainder(x) -> 0
lowerError(x) = main(x) + remainder(x).
```

The signed transfer needs the stronger input:

```text
HasFarSignedWitnesses main amplitude.
```

A finite rightmost zero package can supply an absolute far witness through the
existing anti-cancellation layer, but signed recurrence is an additional
analytic input. A single zero or finite cluster also does not contradict a
zero-density upper bound: density estimates constrain growth in the number of
zeros as height increases, whereas a fixed finite package contributes only a
bounded count.

## Shortest remaining concrete theorem chain

The next non-wrapper Lean work should establish these items in order:

1. A fixed-strip adapter from `carlson_zeroDensity_isBigO` to an eventual
   majorant along any schedule `H(x) -> infinity`.
2. A kernel lemma proving the logarithmic growth inequality implies
   `W_i(x, H(x)) * M_i(H(x)) -> 0`.
3. A finite family constructor assembling those fixed-strip adapters into
   `CarlsonKernelMajorantLayerAdapter`.
4. A concrete candidate family `H_j(x)` and explicit-formula cost inequality.
5. A connection from the actual Pintz envelope to the kernel exponent
   `A_i(x)`.
6. An absolute far-witness instantiation, followed separately by the stronger
   signed-witness instantiation if recurrence information is available.

Only after items 1-6 are supplied does the top-level constructor become a
concrete PNT upper-bound and oscillation theorem rather than an abstract
transfer theorem.

## Ownership boundary

This work does not modify or duplicate
`ZeroForcedOscillationComplementaryBound.lean`, its audits/contracts, the
`research/zero-forced-oscillation-next` worktree, or VK-edge modules. Any
future bridge to the canonical complementary-bound theorem must be added by
composition from the density/transfer side.
