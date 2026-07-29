# VK-edge ordinary local L2 implementation plan

1. Add a failing contract for the ordinary-moment definition, the Gaussian
   envelope, the generic transfer lemma, and the zeta endpoint.
2. Expose explicit polynomial-Gaussian envelope constants and prove the
   completed-square Gaussian supremum estimate.
3. Prove explicit projected-kernel and paired-kernel pointwise bounds.
4. Define the ordinary local second moment and prove the generic
   weighted-to-ordinary transfer.
5. Combine the existing zeta weighted lower bound with the paired-kernel
   pointwise bound.
6. Add the arbitrary-epsilon logarithmic-window endpoint.
7. Add contract and axiom-audit targets, run focused builds, baseline
   verification, and source scans.
8. Record whether any current unconditional local mean-square upper bound
   contradicts the new lower bound.
