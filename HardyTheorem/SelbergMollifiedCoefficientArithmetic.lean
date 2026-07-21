import HardyTheorem.SelbergMollifiedDirichlet
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-!
# Arithmetic of the collected Selberg-mollified coefficients

When `k` lies below both truncation lengths, every factorization of `k`
occurs in the collected coefficient.  Its coefficient is therefore the full
divisor sum of the tapered Moebius coefficients.  Moebius inversion then
identifies this sum exactly with `vonMangoldt k / log X` away from `k = 1`.
-/

/-- Below both truncation lengths, the admissible factor pairs are exactly all
positive multiplicative factorizations of `k`. -/
theorem selbergMollifiedDirichletPairs_eq_divisorsAntidiagonal
    {N X k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) (hkX : k ≤ X) :
    selbergMollifiedDirichletPairs N X k = k.divisorsAntidiagonal := by
  classical
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpProd, hprod⟩
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨hprod, by omega⟩
  · intro hp
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hprod, hk0⟩
    have hpProdNe : p.1 * p.2 ≠ 0 := by simpa [hprod] using hk0
    rcases mul_ne_zero_iff.mp hpProdNe with ⟨hp10, hp20⟩
    have hp1pos : 1 ≤ p.1 := Nat.one_le_iff_ne_zero.mpr hp10
    have hp2pos : 1 ≤ p.2 := Nat.one_le_iff_ne_zero.mpr hp20
    have hp1dvd : p.1 ∣ k := ⟨p.2, hprod.symm⟩
    have hp2dvd : p.2 ∣ k := ⟨p.1, by simpa [Nat.mul_comm] using hprod.symm⟩
    have hp1le : p.1 ≤ N := (Nat.le_of_dvd (by omega) hp1dvd).trans hkN
    have hp2le : p.2 ≤ X := (Nat.le_of_dvd (by omega) hp2dvd).trans hkX
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hp1pos, hp1le⟩,
          Finset.mem_Icc.mpr ⟨hp2pos, hp2le⟩⟩,
        hprod⟩

/-- In the complete divisor range, the collected coefficient is the full
divisor sum of Selberg's tapered Moebius coefficients. -/
theorem selbergMollifiedDirichletCoeff_eq_sum_divisors
    {N X k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) (hkX : k ≤ X) :
    selbergMollifiedDirichletCoeff N X k =
      ∑ d ∈ k.divisors, selbergMoebiusCoeff X d := by
  classical
  rw [selbergMollifiedDirichletCoeff,
    selbergMollifiedDirichletPairs_eq_divisorsAntidiagonal hk1 hkN hkX]
  exact Nat.sum_divisorsAntidiagonal'
    (fun _ d => selbergMoebiusCoeff X d)

/-- The sum of the Moebius function over the divisors of a non-unit is zero. -/
theorem sum_moebius_divisors_eq_zero {k : ℕ} (hk : 1 < k) :
    (∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ)) = 0 := by
  have hconv := congrArg (fun f : ArithmeticFunction ℝ => f k)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  change (((ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
    ArithmeticFunction.zeta) k) = (1 : ArithmeticFunction ℝ) k at hconv
  rw [ArithmeticFunction.coe_mul_zeta_apply] at hconv
  simpa [hk.ne'] using hconv

/-- Expanding the tapered coefficient separates the ordinary Moebius divisor
sum from the logarithmically weighted divisor sum. -/
theorem sum_selbergMoebiusCoeff_divisors_eq
    (X k : ℕ) :
    (∑ d ∈ k.divisors, selbergMoebiusCoeff X d) =
      (∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ)) -
        (∑ d ∈ k.divisors,
          (ArithmeticFunction.moebius d : ℝ) * Real.log d) / Real.log X := by
  classical
  calc
    (∑ d ∈ k.divisors, selbergMoebiusCoeff X d) =
        ∑ d ∈ k.divisors,
          ((ArithmeticFunction.moebius d : ℝ) -
            (ArithmeticFunction.moebius d : ℝ) * Real.log d / Real.log X) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [selbergMoebiusCoeff, selbergMoebiusWeight]
      ring
    _ = (∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ)) -
        ∑ d ∈ k.divisors,
          ((ArithmeticFunction.moebius d : ℝ) * Real.log d / Real.log X) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ)) -
        (∑ d ∈ k.divisors,
          (ArithmeticFunction.moebius d : ℝ) * Real.log d) / Real.log X := by
      rw [Finset.sum_div]

/-- The full divisor sum of Selberg's tapered Moebius coefficients is exactly
`vonMangoldt k / log X` for `k > 1`. -/
theorem sum_selbergMoebiusCoeff_divisors_eq_vonMangoldt_div_log
    {X k : ℕ} (hk : 1 < k) :
    (∑ d ∈ k.divisors, selbergMoebiusCoeff X d) =
      ArithmeticFunction.vonMangoldt k / Real.log X := by
  have hweighted :
      (∑ d ∈ k.divisors,
        (ArithmeticFunction.moebius d : ℝ) * Real.log d) =
        -ArithmeticFunction.vonMangoldt k := by
    simpa only [ArithmeticFunction.log_apply] using
      (ArithmeticFunction.sum_moebius_mul_log_eq (n := k))
  rw [sum_selbergMoebiusCoeff_divisors_eq,
    sum_moebius_divisors_eq_zero hk,
    hweighted]
  ring

/-- The constant coefficient remains one whenever both finite polynomials
contain their first term. -/
@[simp] theorem selbergMollifiedDirichletCoeff_one
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    selbergMollifiedDirichletCoeff N X 1 = 1 := by
  rw [selbergMollifiedDirichletCoeff_eq_sum_divisors
    (N := N) (X := X) (k := 1) (by simp) hN hX]
  simp

/-- In the complete range and away from the constant term, the collected
coefficient is `vonMangoldt k / log X`. -/
theorem selbergMollifiedDirichletCoeff_eq_vonMangoldt_div_log
    {N X k : ℕ} (hk : 1 < k)
    (hkN : k ≤ N) (hkX : k ≤ X) :
    selbergMollifiedDirichletCoeff N X k =
      ArithmeticFunction.vonMangoldt k / Real.log X := by
  rw [selbergMollifiedDirichletCoeff_eq_sum_divisors
    (N := N) (X := X) (k := k) hk.le hkN hkX]
  exact sum_selbergMoebiusCoeff_divisors_eq_vonMangoldt_div_log hk

end HardyTheorem
