import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.Convolution
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

/-- The finite Dirichlet polynomial obtained after multiplying the truncated
zeta sum by the truncated Möbius mollifier and collecting equal products. -/
noncomputable def mollifiedTruncatedPolynomial (X N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (N * X),
    mollifiedTruncatedCoefficient X N n / (n : ℂ) ^ s

private theorem lSeries_eq_sum_Icc_of_eq_zero_above
    (f : ArithmeticFunction ℂ) (B : ℕ) (s : ℂ)
    (hzero : ∀ n, B < n → f n = 0) :
    LSeries (fun n => f n) s =
      ∑ n ∈ Finset.Icc 1 B, f n / (n : ℂ) ^ s := by
  calc
    LSeries (fun n => f n) s =
        ∑ n ∈ Finset.Icc 1 B, LSeries.term (fun n => f n) s n := by
      rw [LSeries, tsum_eq_sum (s := Finset.Icc 1 B)]
      intro n hn
      by_cases hn0 : n = 0
      · simp [hn0]
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have hBn : B < n := by
          by_contra hnot
          exact hn (Finset.mem_Icc.mpr ⟨hn1, Nat.le_of_not_gt hnot⟩)
        simp [LSeries.term_of_ne_zero hn0, hzero n hBn]
    _ = ∑ n ∈ Finset.Icc 1 B, f n / (n : ℂ) ^ s := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [LSeries.term_of_ne_zero (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)]

private theorem lSeriesSummable_of_eq_zero_above
    (f : ArithmeticFunction ℂ) (B : ℕ) (s : ℂ)
    (hzero : ∀ n, B < n → f n = 0) :
    LSeriesSummable (fun n => f n) s := by
  apply summable_of_ne_finset_zero (s := Finset.Icc 1 B)
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hBn : B < n := by
      by_contra hnot
      exact hn (Finset.mem_Icc.mpr ⟨hn1, Nat.le_of_not_gt hnot⟩)
    simp [LSeries.term_of_ne_zero hn0, hzero n hBn]

private theorem truncatedZetaArithmetic_eq_zero_above (N n : ℕ) (hn : N < n) :
    truncatedZetaArithmetic N n = 0 := by
  simp [truncatedZetaArithmetic, Finset.mem_Icc, Nat.not_le_of_gt hn]

private theorem truncatedMobiusArithmetic_eq_zero_above (X n : ℕ) (hn : X < n) :
    truncatedMobiusArithmetic X n = 0 := by
  simp [truncatedMobiusArithmetic, Finset.mem_Icc, Nat.not_le_of_gt hn]

private theorem mollifiedTruncatedCoefficient_eq_zero_above
    (X N n : ℕ) (hn : N * X < n) :
    mollifiedTruncatedCoefficient X N n = 0 := by
  unfold mollifiedTruncatedCoefficient
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hpN : p.1 ≤ N
  · have hpX : X < p.2 := by
      by_contra hnot
      have hp2X : p.2 ≤ X := Nat.le_of_not_gt hnot
      have hprod : p.1 * p.2 = n := (Nat.mem_divisorsAntidiagonal.mp hp).1
      have : p.1 * p.2 ≤ N * X := Nat.mul_le_mul hpN hp2X
      omega
    rw [truncatedMobiusArithmetic_eq_zero_above X p.2 hpX, mul_zero]
  · have hNp : N < p.1 := Nat.lt_of_not_ge hpN
    rw [truncatedZetaArithmetic_eq_zero_above N p.1 hNp, zero_mul]

/-- Multiplying the two finite Dirichlet polynomials and grouping terms with
the same product gives the Dirichlet-convolution coefficients exactly. -/
theorem truncatedZeta_sum_mul_mobius_sum_eq_mollifiedTruncatedPolynomial
    (X N : ℕ) (s : ℂ) :
    (∑ m ∈ Finset.Icc 1 N, 1 / (m : ℂ) ^ s) *
        (∑ n ∈ Finset.Icc 1 X,
          (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s) =
      mollifiedTruncatedPolynomial X N s := by
  have hzeta : LSeriesSummable (fun n => truncatedZetaArithmetic N n) s :=
    lSeriesSummable_of_eq_zero_above _ N s (truncatedZetaArithmetic_eq_zero_above N)
  have hmobius : LSeriesSummable (fun n => truncatedMobiusArithmetic X n) s :=
    lSeriesSummable_of_eq_zero_above _ X s (truncatedMobiusArithmetic_eq_zero_above X)
  have hzeta_sum : LSeries (fun n => truncatedZetaArithmetic N n) s =
      ∑ m ∈ Finset.Icc 1 N, 1 / (m : ℂ) ^ s := by
    calc
      LSeries (fun n => truncatedZetaArithmetic N n) s =
          ∑ m ∈ Finset.Icc 1 N,
            truncatedZetaArithmetic N m / (m : ℂ) ^ s :=
        lSeries_eq_sum_Icc_of_eq_zero_above _ N s
          (truncatedZetaArithmetic_eq_zero_above N)
      _ = ∑ m ∈ Finset.Icc 1 N, 1 / (m : ℂ) ^ s := by
        apply Finset.sum_congr rfl
        intro m hm
        rcases Finset.mem_Icc.mp hm with ⟨hm1, hmN⟩
        simp [truncatedZetaArithmetic, Finset.mem_Icc, hm1, hmN, one_div]
  have hmobius_sum : LSeries (fun n => truncatedMobiusArithmetic X n) s =
      ∑ n ∈ Finset.Icc 1 X,
        (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s := by
    calc
      LSeries (fun n => truncatedMobiusArithmetic X n) s =
          ∑ n ∈ Finset.Icc 1 X,
            truncatedMobiusArithmetic X n / (n : ℂ) ^ s :=
        lSeries_eq_sum_Icc_of_eq_zero_above _ X s
          (truncatedMobiusArithmetic_eq_zero_above X)
      _ = ∑ n ∈ Finset.Icc 1 X,
          (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s := by
        apply Finset.sum_congr rfl
        intro n hn
        rcases Finset.mem_Icc.mp hn with ⟨hn1, hnX⟩
        simp [truncatedMobiusArithmetic, Finset.mem_Icc, hn1, hnX]
  have hproduct_sum :
      LSeries (fun n => (truncatedZetaArithmetic N * truncatedMobiusArithmetic X) n) s =
        mollifiedTruncatedPolynomial X N s := by
    simpa [mollifiedTruncatedPolynomial, mollifiedTruncatedCoefficient] using
      lSeries_eq_sum_Icc_of_eq_zero_above
        (truncatedZetaArithmetic N * truncatedMobiusArithmetic X) (N * X) s
        (mollifiedTruncatedCoefficient_eq_zero_above X N)
  rw [ArithmeticFunction.LSeries_mul' hzeta hmobius] at hproduct_sum
  rw [hzeta_sum, hmobius_sum] at hproduct_sum
  exact hproduct_sum

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

/-- After subtracting the constant term, the collected polynomial starts
strictly above both cutoffs' common range.  Thus the entire interval
`2 ≤ n ≤ min X N` has disappeared by exact Möbius cancellation. -/
theorem mollifiedTruncatedPolynomial_sub_one_eq_tail
    {X N : ℕ} (hX : 0 < X) (hN : 0 < N) (s : ℂ) :
    mollifiedTruncatedPolynomial X N s - 1 =
      ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
        mollifiedTruncatedCoefficient X N n / (n : ℂ) ^ s := by
  let f : ℕ → ℂ := fun n =>
    mollifiedTruncatedCoefficient X N n / (n : ℂ) ^ s
  let tail : Finset ℕ := Finset.Icc (min X N + 1) (N * X)
  let full : Finset ℕ := Finset.Icc 1 (N * X)
  have hprod : 1 ≤ N * X := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hN.ne' hX.ne')
  have hsubset : insert 1 tail ⊆ full := by
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hnTail
    · exact Finset.mem_Icc.mpr ⟨le_rfl, hprod⟩
    · rcases Finset.mem_Icc.mp hnTail with ⟨hnLower, hnUpper⟩
      exact Finset.mem_Icc.mpr ⟨(Nat.one_le_iff_ne_zero.mpr (by omega)), hnUpper⟩
  have hzero : ∀ n ∈ full, n ∉ insert 1 tail → f n = 0 := by
    intro n hnFull hnOutside
    rcases Finset.mem_Icc.mp hnFull with ⟨hnOne, hnUpper⟩
    have hnNe : n ≠ 1 := by
      intro hn
      exact hnOutside (Finset.mem_insert.mpr (Or.inl hn))
    have hnPos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hnOne
    have hnMin : n ≤ min X N := by
      by_contra hnot
      have hMinLt : min X N < n := Nat.lt_of_not_ge hnot
      have hnTail : n ∈ tail :=
        Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hMinLt, hnUpper⟩
      exact hnOutside (Finset.mem_insert_of_mem hnTail)
    have hcoeff := mollifiedTruncatedCoefficient_eq_one_apply hnPos
      (hnMin.trans (min_le_left X N)) (hnMin.trans (min_le_right X N))
    simp [f, hcoeff, hnNe]
  have hsum : (∑ n ∈ insert 1 tail, f n) = ∑ n ∈ full, f n :=
    Finset.sum_subset hsubset hzero
  have hOneNotTail : 1 ∉ tail := by
    simp [tail, Finset.mem_Icc]
    omega
  have hfOne : f 1 = 1 := by
    have hcoeff := mollifiedTruncatedCoefficient_eq_one_apply
      (X := X) (N := N) (n := 1) Nat.zero_lt_one hX hN
    simp [f, hcoeff]
  rw [Finset.sum_insert hOneNotTail, hfOne] at hsum
  unfold mollifiedTruncatedPolynomial
  change (∑ n ∈ full, f n) - 1 = ∑ n ∈ tail, f n
  rw [← hsum]
  ring

end CarlsonZeroDensity
end PrimeNumberTheorem
