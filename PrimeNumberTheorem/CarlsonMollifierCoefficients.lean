import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Complex.Basic

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The coefficient sequence of the zeta Dirichlet polynomial truncated at `N`. -/
def truncatedZetaArithmetic (N : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ∈ Finset.Icc 1 N then 1 else 0, by simp⟩

/-- The coefficient sequence of the Möbius mollifier truncated at `X`. -/
def truncatedMobiusArithmetic (X : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ∈ Finset.Icc 1 X
    then (ArithmeticFunction.moebius n : ℂ) else 0, by simp⟩

/-- Coefficient of the product of the truncated zeta polynomial and Möbius
mollifier, expressed as a finite Dirichlet convolution. -/
def mollifiedTruncatedCoefficient (X N n : ℕ) : ℂ :=
  (truncatedZetaArithmetic N * truncatedMobiusArithmetic X) n

/-- Below both cutoffs, Möbius inversion is exact: every positive coefficient
except the constant coefficient vanishes. -/
theorem mollifiedTruncatedCoefficient_eq_one_apply {X N n : ℕ}
    (hn : 0 < n) (hnX : n ≤ X) (hnN : n ≤ N) :
    mollifiedTruncatedCoefficient X N n = if n = 1 then 1 else 0 := by
  unfold mollifiedTruncatedCoefficient
  rw [ArithmeticFunction.mul_apply]
  calc
    (∑ p ∈ n.divisorsAntidiagonal,
        truncatedZetaArithmetic N p.1 * truncatedMobiusArithmetic X p.2) =
        ∑ p ∈ n.divisorsAntidiagonal,
          (ArithmeticFunction.zeta : ArithmeticFunction ℂ) p.1 *
            (ArithmeticFunction.moebius : ArithmeticFunction ℂ) p.2 := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp1div := Nat.fst_mem_divisors_of_mem_antidiagonal hp
      have hp2div := Nat.snd_mem_divisors_of_mem_antidiagonal hp
      have hp1pos : 0 < p.1 := Nat.pos_of_mem_divisors hp1div
      have hp2pos : 0 < p.2 := Nat.pos_of_mem_divisors hp2div
      have hp1n : p.1 ≤ n := Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hp1div)
      have hp2n : p.2 ≤ n := Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hp2div)
      have hp1ne : p.1 ≠ 0 := Nat.ne_of_gt hp1pos
      have hp1one : 1 ≤ p.1 := hp1pos
      have hp2one : 1 ≤ p.2 := hp2pos
      simp [truncatedZetaArithmetic, truncatedMobiusArithmetic,
        Finset.mem_Icc, hp1ne, hp1one, hp2one,
        hp1n.trans hnN, hp2n.trans hnX]
    _ = ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
          (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) n := by
      rw [ArithmeticFunction.mul_apply]
    _ = (1 : ArithmeticFunction ℂ) n := by
      rw [ArithmeticFunction.coe_zeta_mul_coe_moebius]
    _ = if n = 1 then 1 else 0 := ArithmeticFunction.one_apply

end CarlsonZeroDensity
end PrimeNumberTheorem
