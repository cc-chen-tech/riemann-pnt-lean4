# Actual strict-margin grid full-PNT envelope implementation plan

1. Define the contour, zero-free, and residual coefficient functions.
2. Reduce the actual selected contour remainder to the existing closed-form
   depth-zero majorant.
3. Combine the Stack 128 finite-zero estimate with the exact actual explicit
   formula decomposition.
4. Identify the result with the Stack 127 arbitrary-rate envelope.
5. Apply the Stack 126 envelope-optimal grid rate and its `1 / q` guarantee.
6. Add contract and axiom audit.
7. Build sequentially and publish as a draft PR stacked on Stack 128.
