# Strict-margin optimal-rate recovery implementation plan

1. Prove `theta <= sqrt theta` on `[0,1]`.
2. Compare both branches of the constrained balanced rate.
3. Derive the explicit `q > 1` recovery inequality at `theta = 1/q`.
4. Instantiate the automatic actual PNT grid theorem at that theta.
5. Return the grid rate lower bound and real PNT error majorant together.
6. Add contract and axiom audit, build sequentially, and publish a draft PR.
