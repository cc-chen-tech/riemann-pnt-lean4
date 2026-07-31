# Explicit-formula normalized window remainder

Status: implemented and locally contract-checked.

1. Select one good height at the power scale `T ~ exp(a / 2)`.
2. Derive a deterministic envelope uniform for `y in [a, a + L]`.
3. Prove the envelope tends to zero for `1 / 2 < beta < 1`.
4. Combine the selection and envelope into an eventual uniform theorem.
5. Lock the exact public types with a contract and audit all public theorems.

The next mathematical layer is separate: bound the complementary finite zero
cluster and contour package strongly enough to use this approximation theorem
inside the localized oscillation argument.
