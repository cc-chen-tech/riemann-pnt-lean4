import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-!
# The logarithmic Leibniz rule for Dirichlet convolution

Pointwise multiplication of an arithmetic function by `log n` is a
derivation for Dirichlet convolution.  This elementary identity is the
global arithmetic counterpart of the Euler operator used in the local
square-root zeta calculation.
-/

/-- Multiplication by the arithmetic logarithm satisfies the Leibniz rule
for Dirichlet convolution. -/
theorem arithmeticFunction_pmul_log_mul
    (f g : ArithmeticFunction ℝ) :
    (f * g).pmul ArithmeticFunction.log =
      f.pmul ArithmeticFunction.log * g +
        f * g.pmul ArithmeticFunction.log := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  rw [ArithmeticFunction.pmul_apply,
    ArithmeticFunction.add_apply,
    ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply,
    ArithmeticFunction.log_apply,
    Finset.sum_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  rcases Nat.mem_divisorsAntidiagonal.mp hij with
    ⟨hprod, _⟩
  have hmul0 : ij.1 * ij.2 ≠ 0 := by
    rw [hprod]
    exact hn
  have hi0 : ij.1 ≠ 0 :=
    left_ne_zero_of_mul hmul0
  have hj0 : ij.2 ≠ 0 :=
    right_ne_zero_of_mul hmul0
  have hlog :
      Real.log (n : ℝ) =
        Real.log (ij.1 : ℝ) +
          Real.log (ij.2 : ℝ) := by
    rw [← hprod, Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hi0)
        (by exact_mod_cast hj0)]
  simp only [ArithmeticFunction.pmul_apply,
    ArithmeticFunction.log_apply]
  rw [hlog]
  ring

end HardyTheorem
