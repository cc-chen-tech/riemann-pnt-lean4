# Stack134 Implementation Plan

1. Add the standalone natural-point `sqrt(log m) / m` limit.
2. Prove decay of the rate-independent residual.
3. Normalize the concrete full envelope into two polynomial-exponential terms
   and the residual, then prove convergence at every positive target rate.
4. Add the automatic Stack133 corollary that carries both real-error domination
   and majorant convergence.
5. Compile implementation, contract, and axiom audit with one low-priority Lean
   process at a time; publish as a bounded PR after the audit is clean.
