# Strict-margin grid full-budget transfer implementation plan

1. Import the Stack 126 balanced-rate grid approximation.
2. Define the strict classical zero-free rate `theta * b / k` and prove its
   positivity, strict margin, and balanced-profile identity.
3. Define arbitrary-rate and `1 / q` grid full-budget analytic envelopes.
4. Prove the arbitrary-rate envelope is bounded by the grid envelope at the
   Stack 126 envelope-optimal rate.
5. Define the eventual actual-budget domination interface.
6. Transfer domination to the Stack 125 pointwise minimum and the real
   relative `psi0` error.
7. Add contract and axiom-audit modules.
8. Build the implementation, contract, and audit directly with the existing
   Lean overlay and one low-priority process.
9. Commit documentation and implementation separately, push the branch, and
   open a bounded draft PR stacked on Stack 126.
