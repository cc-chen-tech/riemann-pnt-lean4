# VK-edge Cosine-Model Annihilator Remediation Plan

## Scope

This plan records the PR #26 review remediation. Work remains isolated on
`research/vk-edge-target-annihilator` and is stacked on the corrected PR #25
head.

## Tasks

- [x] Rebase onto the corrected residual-amplification branch.
- [x] Rename the source, contract, audit, and research records from
  target-pair terminology to cosine-model terminology.
- [x] Rename public symbols to `cosinePairModel`,
  `normalizedCosineModelPair`, and `normalizedPsiModelResidual`.
- [x] Keep the detector model-first, then add a separate exact
  explicit-formula identification module for a genuine conjugate zero pair.
- [x] Keep the exact three-scale PNT-error identity as an arithmetic identity,
  and isolate the explicit-formula interpretation in the companion bridge.
- [x] Prove explicit inclusion of the three shifted inner-interval points in
  `[a - |h|, b + |h|]`.
- [x] Prove positive inner detector energy implies a pointwise square lower
  bound on the expanded interval, with explicit factor `72`.
- [x] Specialize the transfer to `normalizedPsiModelResidual`.
- [x] Replace bare theorem checks with complete exact-type contracts.
- [x] Add every new public theorem to the PR-specific and central axiom
  audits.
- [x] Run the focused source, contract, and audit build.
- [x] Run the central allowlist check.
- [x] Run the forbidden-term scan and `git diff --check`.
- [x] Run `./scripts/verify-baseline.sh`.
- [ ] Commit, push with lease, and update Draft PR #26.

## Mathematical boundary

The branch proves a model annihilator, an inner-to-outer analytic transfer,
and an exact identification of the model and residual with the corresponding
finite-height explicit-formula expressions. It does not bound the residual
components, produce positive detector energy, or imply an additional zero,
Carlson contradiction, unconditional PNT oscillation theorem, or RH.
