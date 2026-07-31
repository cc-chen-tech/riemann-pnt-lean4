# Actual strict-margin finite-zero majorant implementation plan

1. Import the Stack 127 strict-margin transfer module and the existing generic
   classical finite-zero decay calculation.
2. Define the closed strict-margin relative finite-zero majorant.
3. Prove the selected actual candidate height lies below `exp (k u)` and is
   eventually at least four.
4. Apply the generic dynamic-height zero-free-width theorem at rate
   `theta * b / k`.
5. Convert the uniform finite-zero estimate to the explicit
   `9 C u^2 exp (-(theta * b / k) u)` relative bound.
6. Obtain common `b, C` automatically for every rate in a finite grid.
7. Add contract and axiom audit, build all targets sequentially, and publish a
   draft PR stacked on Stack 127.
