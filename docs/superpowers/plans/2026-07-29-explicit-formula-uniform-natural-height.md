# Uniform natural-height implementation plan

1. Lock the full common-height theorem type in a failing contract.
2. Reuse the common moving-right truncated theorem.
3. For each natural sample, remove the left-edge and finite-trivial-zero
   truncations by their proved limits, keeping the selected height fixed.
4. Audit axioms and run focused and baseline verification.
5. Submit as a stacked PR without adding real-window interpolation.
