import PrimeNumberTheorem.CarlsonZetaApproximation
import PrimeNumberTheorem.CarlsonMollifierCoefficients
import PrimeNumberTheorem.CarlsonDivisorSquare
import PrimeNumberTheorem.CarneiroLittmannKernelConstruction
import PrimeNumberTheorem.MobiusMollifier
import ZeroFreeRegion

open Complex
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The finite zeta Dirichlet polynomial at real cutoff `x`. -/
noncomputable def truncatedZetaPolynomial (x : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor x), 1 / (n : ℂ) ^ s

/-- Carlson's mollified zeta error. -/
noncomputable def mollifiedZetaError (X : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s * mobiusMollifier X s - 1

/-- In the half-plane of absolute convergence, the mollified zeta error is
zeta times the omitted tail of the complete Mobius Dirichlet series. -/
theorem mollifiedZetaError_eq_riemannZeta_mul_mobius_tail
    {X : ℕ} {s : ℂ} (hs : 1 < s.re) :
    mollifiedZetaError X s =
      riemannZeta s *
        (mobiusMollifier X s -
          LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s) := by
  have hproduct := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hproduct
  unfold mollifiedZetaError
  rw [← hproduct]
  ring

/-- On the fixed far-right half-plane `Re(s) >= 4`, the mollified zeta error
has the uniform numerical bound `5/9`. -/
theorem norm_mollifiedZetaError_le_five_ninth_of_four_le_re
    {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 4 ≤ s.re) :
    ‖mollifiedZetaError X s‖ ≤ (5 / 9 : ℝ) := by
  have hs1 : 1 < s.re := by linarith
  have htail :=
    norm_LSeries_moebius_sub_mobiusMollifier_le_zeta_tail hX hs1
  have hzetaReal := ZeroFreeRegion.riemannZeta_re_le_sigma_div_sub s.re hs1
  have hfrac : s.re / (s.re - 1) ≤ (4 / 3 : ℝ) := by
    apply (div_le_iff₀ (sub_pos.mpr hs1)).2
    nlinarith
  have htailThird :
      ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s -
          mobiusMollifier X s‖ ≤ (1 / 3 : ℝ) := by
    linarith
  have htailThird' :
      ‖mobiusMollifier X s -
          LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ ≤
        (1 / 3 : ℝ) := by
    calc
      ‖mobiusMollifier X s -
          LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ =
          ‖-(LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s -
            mobiusMollifier X s)‖ := by congr 1 <;> ring
      _ = ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s -
          mobiusMollifier X s‖ := norm_neg _
      _ ≤ (1 / 3 : ℝ) := htailThird
  have hzetaNorm : ‖riemannZeta s‖ ≤ (5 / 3 : ℝ) := by
    exact (ZeroFreeRegion.norm_riemannZeta_le_re_zeta_two_of_two_le_re s
      (by linarith)).trans ZeroFreeRegion.riemannZeta_two_re_le_five_thirds
  rw [mollifiedZetaError_eq_riemannZeta_mul_mobius_tail hs1, norm_mul]
  calc
    ‖riemannZeta s‖ *
        ‖mobiusMollifier X s -
          LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ ≤
        (5 / 3 : ℝ) * (1 / 3 : ℝ) :=
      mul_le_mul hzetaNorm htailThird' (norm_nonneg _) (by norm_num)
    _ = (5 / 9 : ℝ) := by norm_num

/-- On the far-right half-plane the mollified zeta error has a quantitative
decay bound, uniform in the mollifier cutoff.  The decay comes from the
absolutely convergent Mobius tail, while zeta itself is bounded by `5 / 3`. -/
theorem norm_mollifiedZetaError_le_five_thirds_div_sub_one_of_four_le_re
    {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 4 ≤ s.re) :
    ‖mollifiedZetaError X s‖ ≤ 5 / (3 * (s.re - 1)) := by
  have hs1 : 1 < s.re := by linarith
  have htail :=
    norm_LSeries_moebius_sub_mobiusMollifier_le_zeta_tail hX hs1
  have hzetaReal := ZeroFreeRegion.riemannZeta_re_le_sigma_div_sub s.re hs1
  have hdenPos : 0 < s.re - 1 := sub_pos.mpr hs1
  have htailBound :
      (riemannZeta (s.re : ℂ)).re - 1 ≤ 1 / (s.re - 1) := by
    calc
      (riemannZeta (s.re : ℂ)).re - 1 ≤
          s.re / (s.re - 1) - 1 := sub_le_sub_right hzetaReal 1
      _ = 1 / (s.re - 1) := by field_simp; ring
  have htailNorm :
      ‖mobiusMollifier X s -
          LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ ≤
        1 / (s.re - 1) := by
    calc
      ‖mobiusMollifier X s -
          LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ =
          ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s -
            mobiusMollifier X s‖ := norm_sub_rev _ _
      _ ≤ (riemannZeta (s.re : ℂ)).re - 1 := htail
      _ ≤ 1 / (s.re - 1) := htailBound
  have hzetaNorm : ‖riemannZeta s‖ ≤ (5 / 3 : ℝ) :=
    (ZeroFreeRegion.norm_riemannZeta_le_re_zeta_two_of_two_le_re s
      (by linarith)).trans ZeroFreeRegion.riemannZeta_two_re_le_five_thirds
  rw [mollifiedZetaError_eq_riemannZeta_mul_mobius_tail hs1, norm_mul]
  calc
    ‖riemannZeta s‖ *
        ‖mobiusMollifier X s -
          LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ ≤
        (5 / 3 : ℝ) * (1 / (s.re - 1)) :=
      mul_le_mul hzetaNorm htailNorm (norm_nonneg _)
        (by positivity)
    _ = 5 / (3 * (s.re - 1)) := by field_simp

/-- In particular, the mollified zeta error is strictly smaller than one on
the fixed far-right half-plane. -/
theorem norm_mollifiedZetaError_lt_one_of_four_le_re
    {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 4 ≤ s.re) :
    ‖mollifiedZetaError X s‖ < 1 :=
  (norm_mollifiedZetaError_le_five_ninth_of_four_le_re hX hs).trans_lt
    (by norm_num)

/-- Coefficients of the Möbius-cancelled tail on the vertical line
`Re s = sigma`. -/
noncomputable def mollifiedTailCoefficient
    (X N : ℕ) (sigma : ℝ) (n : ℕ) : ℂ :=
  mollifiedTruncatedCoefficient X N n *
    ((n : ℂ) ^ (sigma : ℂ))⁻¹

/-- The vertical-line tail coefficient is bounded by the divisor count times
the expected real decay `n⁻ˢ`. -/
theorem norm_mollifiedTailCoefficient_le
    (X N : ℕ) (sigma : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖mollifiedTailCoefficient X N sigma n‖ ≤
      (n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma) := by
  have hcoeff :=
    norm_mollifiedTruncatedCoefficient_le_card_divisorsAntidiagonal X N n
  have hdecay : ‖((n : ℂ) ^ (sigma : ℂ))⁻¹‖ = (n : ℝ) ^ (-sigma) := by
    rw [norm_inv, norm_natCast_cpow_of_pos hn]
    exact (Real.rpow_neg (Nat.cast_nonneg n) sigma).symm
  unfold mollifiedTailCoefficient
  rw [norm_mul, hdecay]
  exact mul_le_mul_of_nonneg_right hcoeff
    (Real.rpow_nonneg (Nat.cast_nonneg n) (-sigma))

/-- The weighted coefficient square sum in the conditional Hilbert bound is
dominated by a purely real divisor-square sum. -/
theorem mollifiedTailCoefficient_weightedSquareSum_le
    (X N : ℕ) (sigma : ℝ) :
    ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
        ((n : ℝ) + 1) * ‖mollifiedTailCoefficient X N sigma n‖ ^ 2 ≤
      ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
        ((n : ℝ) + 1) *
          ((n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma)) ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hnpos : 0 < n := by
    have hnLower := (Finset.mem_Icc.mp hn).1
    omega
  have hnorm := norm_mollifiedTailCoefficient_le X N sigma hnpos
  have hbound :
      0 ≤ (n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  nlinarith [norm_nonneg (mollifiedTailCoefficient X N sigma n)]

/-- The unweighted coefficient square sum is bounded by the unweighted
divisor-square majorant.  Keeping this term separate avoids inserting the
Hilbert weight into the diagonal part of the mean-square estimate. -/
theorem mollifiedTailCoefficient_squareSum_le_divisorSquareSum
    (X N : ℕ) (sigma : ℝ) :
    ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
        ‖mollifiedTailCoefficient X N sigma n‖ ^ 2 ≤
      ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
        ((n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma)) ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  have hnpos : 0 < n := by
    have hnLower := (Finset.mem_Icc.mp hn).1
    omega
  have hnorm := norm_mollifiedTailCoefficient_le X N sigma hnpos
  have hbound :
      0 ≤ (n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  nlinarith [norm_nonneg (mollifiedTailCoefficient X N sigma n)]

/-- The unweighted coefficient square sum is controlled by the same weighted
divisor-square majorant. -/
theorem mollifiedTailCoefficient_squareSum_le_weightedDivisorSquareSum
    (X N : ℕ) (sigma : ℝ) :
    ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
        ‖mollifiedTailCoefficient X N sigma n‖ ^ 2 ≤
      ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
        ((n : ℝ) + 1) *
          ((n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma)) ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  have hnpos : 0 < n := by
    have hnLower := (Finset.mem_Icc.mp hn).1
    omega
  have hnorm := norm_mollifiedTailCoefficient_le X N sigma hnpos
  have hbound :
      0 ≤ (n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hweight : 1 ≤ (n : ℝ) + 1 := by
    have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  nlinarith [norm_nonneg (mollifiedTailCoefficient X N sigma n),
    sq_nonneg ((n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma))]

/-- The Möbius-cancelled tail is a finite exponential sum with frequencies
`-log n` on every vertical line. -/
theorem mollifiedTruncatedTail_verticalLine_eq_finiteDirichletPolynomial
    (X N : ℕ) (sigma t : ℝ) :
    (∑ n ∈ Finset.Icc (min X N + 1) (N * X),
        mollifiedTruncatedCoefficient X N n /
          (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)) =
      DirichletPolynomial.finiteDirichletPolynomial
        (Finset.Icc (min X N + 1) (N * X))
        (mollifiedTailCoefficient X N sigma) t := by
  unfold DirichletPolynomial.finiteDirichletPolynomial
    DirichletPolynomial.finiteExponentialSum mollifiedTailCoefficient
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := by
    have hnLower := (Finset.mem_Icc.mp hn).1
    omega
  have hinv := inv_nat_cpow_verticalLine_eq_exp
    (Nat.ne_of_gt hnpos) sigma t
  rw [div_eq_mul_inv, ← one_div, hinv]
  rw [← mul_assoc]
  congr 1
  push_cast
  ring_nf

/-- Conditional mean-square estimate for the Möbius-cancelled tail.  Its only
analytic hypothesis is the weighted Hilbert-form inequality; all zeta,
Möbius, vertical-line, and interval bookkeeping is already discharged. -/
theorem mollifiedTruncatedTail_meanSquare_le_of_hilbert
    {X N : ℕ} {sigma a b C : ℝ} (hab : a ≤ b)
    (hHilbert : ∀ d : ℕ → ℂ,
      ‖DirichletPolynomial.hilbertForm
          (Finset.Icc (min X N + 1) (N * X)) d
          (fun n : ℕ => -Real.log n)‖ ≤
        C * ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          ((n : ℝ) + 1) * ‖d n‖ ^ 2) :
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          mollifiedTruncatedCoefficient X N n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      (b - a) * ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          ‖mollifiedTailCoefficient X N sigma n‖ ^ 2 +
        2 * C * ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          ((n : ℝ) + 1) * ‖mollifiedTailCoefficient X N sigma n‖ ^ 2 := by
  simp_rw [mollifiedTruncatedTail_verticalLine_eq_finiteDirichletPolynomial]
  unfold DirichletPolynomial.finiteDirichletPolynomial
  apply DirichletPolynomial.finiteExponentialSum_meanSquare_le_of_hilbert hab
  · intro m hm n hn hmn
    have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast (show 0 < m by
        have := (Finset.mem_Icc.mp hm).1
        omega)
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (show 0 < n by
        have := (Finset.mem_Icc.mp hn).1
        omega)
    have hlog : Real.log (m : ℝ) = Real.log (n : ℝ) := by linarith
    exact Nat.cast_injective (Real.log_injOn_pos hmpos hnpos hlog)
  · intro n hn
    positivity
  · exact hHilbert

/-- The concrete Carneiro--Littmann kernel removes the remaining Hilbert-form
hypothesis from the mean-square estimate for the Möbius-cancelled tail. -/
theorem mollifiedTruncatedTail_meanSquare_le_carneiroLittmann
    {X N : ℕ} {sigma a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          mollifiedTruncatedCoefficient X N n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      (b - a) * ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          ‖mollifiedTailCoefficient X N sigma n‖ ^ 2 +
        4 * Real.pi * ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          ((n : ℝ) + 1) * ‖mollifiedTailCoefficient X N sigma n‖ ^ 2 := by
  simpa only [mul_assoc, show 2 * (2 * Real.pi) = 4 * Real.pi by ring] using
    mollifiedTruncatedTail_meanSquare_le_of_hilbert
      (X := X) (N := N) (sigma := sigma) (C := 2 * Real.pi) hab
      (fun d =>
        DirichletPolynomial.norm_hilbertForm_Icc_neg_log_le_carneiroLittmann
          (show 0 < min X N + 1 by omega) d)

/-- The mollified tail mean square is reduced to one purely real weighted
divisor-square sum.  Estimating this sum is the remaining arithmetic input. -/
theorem mollifiedTruncatedTail_meanSquare_le_weightedDivisorSquareSum
    {X N : ℕ} {sigma a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          mollifiedTruncatedCoefficient X N n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ((b - a) + 4 * Real.pi) *
        ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          ((n : ℝ) + 1) *
            ((n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma)) ^ 2 := by
  let D : ℝ :=
    ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
      ((n : ℝ) + 1) *
        ((n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma)) ^ 2
  calc
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          mollifiedTruncatedCoefficient X N n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
        (b - a) * ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
            ‖mollifiedTailCoefficient X N sigma n‖ ^ 2 +
          4 * Real.pi * ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
            ((n : ℝ) + 1) * ‖mollifiedTailCoefficient X N sigma n‖ ^ 2 :=
      mollifiedTruncatedTail_meanSquare_le_carneiroLittmann hab
    _ ≤ (b - a) * D + 4 * Real.pi * D := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (mollifiedTailCoefficient_squareSum_le_weightedDivisorSquareSum
            X N sigma) (sub_nonneg.mpr hab)
      · exact mul_le_mul_of_nonneg_left
          (mollifiedTailCoefficient_weightedSquareSum_le X N sigma)
          (mul_nonneg (by norm_num) Real.pi_nonneg)
    _ = ((b - a) + 4 * Real.pi) * D := by ring

/-- The Carlson tail is controlled by a weighted fourfold-divisor sum.  This
is the form suited to a hyperbola-counting or Abel-summation estimate. -/
theorem mollifiedTruncatedTail_meanSquare_le_fourfoldDivisorCount
    {X N : ℕ} {sigma a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          mollifiedTruncatedCoefficient X N n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ((b - a) + 4 * Real.pi) *
        ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          ((n : ℝ) + 1) * (fourfoldDivisorCount n : ℝ) *
            ((n : ℝ) ^ (-sigma)) ^ 2 := by
  calc
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          mollifiedTruncatedCoefficient X N n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ((b - a) + 4 * Real.pi) *
        ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          ((n : ℝ) + 1) *
            ((n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma)) ^ 2 :=
      mollifiedTruncatedTail_meanSquare_le_weightedDivisorSquareSum hab
    _ ≤ ((b - a) + 4 * Real.pi) *
        ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          ((n : ℝ) + 1) * (fourfoldDivisorCount n : ℝ) *
            ((n : ℝ) ^ (-sigma)) ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · exact weightedDivisorSquareSum_le_fourfoldDivisorCount
          (show 0 < min X N + 1 by omega) sigma
      · exact add_nonneg (sub_nonneg.mpr hab)
          (mul_nonneg (by norm_num) Real.pi_nonneg)

/-- The exact Carlson mean-square reduction with the diagonal and Hilbert
terms kept separate.  The two divisor sums have different sharp endpoint
bounds, so combining them before partial summation loses the Carlson exponent. -/
theorem mollifiedTruncatedTail_meanSquare_le_separatedFourfoldDivisorSums
    {X N : ℕ} {sigma a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          mollifiedTruncatedCoefficient X N n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      (b - a) *
          ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
            (fourfoldDivisorCount n : ℝ) *
              ((n : ℝ) ^ (-sigma)) ^ 2 +
        4 * Real.pi *
          ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
            ((n : ℝ) + 1) * (fourfoldDivisorCount n : ℝ) *
              ((n : ℝ) ^ (-sigma)) ^ 2 := by
  calc
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          mollifiedTruncatedCoefficient X N n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      (b - a) * ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          ‖mollifiedTailCoefficient X N sigma n‖ ^ 2 +
        4 * Real.pi * ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          ((n : ℝ) + 1) * ‖mollifiedTailCoefficient X N sigma n‖ ^ 2 :=
      mollifiedTruncatedTail_meanSquare_le_carneiroLittmann hab
    _ ≤ (b - a) *
          ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
            ((n.divisorsAntidiagonal.card : ℝ) *
              (n : ℝ) ^ (-sigma)) ^ 2 +
        4 * Real.pi *
          ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
            ((n : ℝ) + 1) *
              ((n.divisorsAntidiagonal.card : ℝ) *
                (n : ℝ) ^ (-sigma)) ^ 2 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (mollifiedTailCoefficient_squareSum_le_divisorSquareSum X N sigma)
          (sub_nonneg.mpr hab)
      · exact mul_le_mul_of_nonneg_left
          (mollifiedTailCoefficient_weightedSquareSum_le X N sigma)
          (mul_nonneg (by norm_num) Real.pi_nonneg)
    _ ≤ (b - a) *
          ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
            (fourfoldDivisorCount n : ℝ) *
              ((n : ℝ) ^ (-sigma)) ^ 2 +
        4 * Real.pi *
          ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
            ((n : ℝ) + 1) * (fourfoldDivisorCount n : ℝ) *
              ((n : ℝ) ^ (-sigma)) ^ 2 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (divisorSquareSum_le_fourfoldDivisorCount
            (show 0 < min X N + 1 by omega) sigma)
          (sub_nonneg.mpr hab)
      · exact mul_le_mul_of_nonneg_left
          (weightedDivisorSquareSum_le_fourfoldDivisorCount
            (show 0 < min X N + 1 by omega) sigma)
          (mul_nonneg (by norm_num) Real.pi_nonneg)

/-- The sharp Carlson endpoint for the mollified tail.  The diagonal term is
controlled at the lower endpoint, while the Hilbert term is controlled at the
upper endpoint; keeping them separate is what preserves Carlson's exponent. -/
theorem mollifiedTruncatedTail_meanSquare_le_sharpDivisorEndpoint
    {X N : ℕ} {sigma a b : ℝ} (hab : a ≤ b)
    (hsupport : min X N + 1 ≤ N * X)
    (hsigma : 1 / 2 < sigma) (hsigma1 : sigma < 1) :
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          mollifiedTruncatedCoefficient X N n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      (b - a) * ((1 + Real.log (N * X)) ^ 3 *
        ((2 + 1 / (2 * sigma - 1)) *
          ((min X N + 1 : ℕ) : ℝ) ^ (1 - 2 * sigma))) +
        8 * Real.pi * ((1 + Real.log (N * X)) ^ 3 *
          ((2 + 1 / (2 - 2 * sigma)) *
            ((N * X : ℕ) : ℝ) ^ (2 - 2 * sigma))) := by
  have hseparated :=
    mollifiedTruncatedTail_meanSquare_le_separatedFourfoldDivisorSums
      (X := X) (N := N) (sigma := sigma) hab
  have hunweighted := unweightedFourfoldDivisorSum_le_sharp
    (show 0 < min X N + 1 by omega) hsupport hsigma
  have hweighted := weightedFourfoldDivisorSum_le_sharp
    (show 0 < min X N + 1 by omega) hsupport hsigma hsigma1
  calc
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          mollifiedTruncatedCoefficient X N n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      (b - a) *
          ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
            (fourfoldDivisorCount n : ℝ) *
              ((n : ℝ) ^ (-sigma)) ^ 2 +
        4 * Real.pi *
          ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
            ((n : ℝ) + 1) * (fourfoldDivisorCount n : ℝ) *
              ((n : ℝ) ^ (-sigma)) ^ 2 := hseparated
    _ ≤ (b - a) * ((1 + Real.log (N * X)) ^ 3 *
          ((2 + 1 / (2 * sigma - 1)) *
            ((min X N + 1 : ℕ) : ℝ) ^ (1 - 2 * sigma))) +
        4 * Real.pi *
          (2 * ((1 + Real.log (N * X)) ^ 3 *
            ((2 + 1 / (2 - 2 * sigma)) *
              ((N * X : ℕ) : ℝ) ^ (2 - 2 * sigma)))) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (by simpa only [Nat.cast_mul] using hunweighted) (sub_nonneg.mpr hab))
        (mul_le_mul_of_nonneg_left
          (by simpa only [Nat.cast_mul] using hweighted)
          (mul_nonneg (by norm_num) Real.pi_nonneg))
    _ = (b - a) * ((1 + Real.log (N * X)) ^ 3 *
          ((2 + 1 / (2 * sigma - 1)) *
            ((min X N + 1 : ℕ) : ℝ) ^ (1 - 2 * sigma))) +
        8 * Real.pi * ((1 + Real.log (N * X)) ^ 3 *
          ((2 + 1 / (2 - 2 * sigma)) *
            ((N * X : ℕ) : ℝ) ^ (2 - 2 * sigma))) := by ring

/-- The Carlson mollified tail mean square is bounded by an explicit endpoint
expression.  This combines the Hilbert-form reduction with the elementary
summatory estimate for the fourfold divisor function. -/
theorem mollifiedTruncatedTail_meanSquare_le_prefix_bound
    {X N : ℕ} {sigma a b : ℝ} (hab : a ≤ b)
    (hsigma : 1 / 2 < sigma) :
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          mollifiedTruncatedCoefficient X N n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ((b - a) + 4 * Real.pi) *
        (2 * ((min X N + 1 : ℕ) : ℝ) ^ (1 - 2 * sigma) *
          (((N * X : ℕ) : ℝ) * (1 + Real.log (N * X)) ^ 3)) := by
  calc
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          mollifiedTruncatedCoefficient X N n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ((b - a) + 4 * Real.pi) *
        ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          ((n : ℝ) + 1) * (fourfoldDivisorCount n : ℝ) *
            ((n : ℝ) ^ (-sigma)) ^ 2 :=
      mollifiedTruncatedTail_meanSquare_le_fourfoldDivisorCount hab
    _ ≤ ((b - a) + 4 * Real.pi) *
        (2 * ((min X N + 1 : ℕ) : ℝ) ^ (1 - 2 * sigma) *
          (((N * X : ℕ) : ℝ) * (1 + Real.log (N * X)) ^ 3)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [Nat.cast_mul] using
          (weightedFourfoldDivisorSum_le_prefix_bound
            (L := min X N + 1) (U := N * X) (sigma := sigma)
            (show 0 < min X N + 1 by omega) hsigma)
      · exact add_nonneg (sub_nonneg.mpr hab)
          (mul_nonneg (by norm_num) Real.pi_nonneg)

/-- The finite product in the mollified zeta approximation is exactly the
coefficient polynomial obtained from the truncated Dirichlet convolution. -/
theorem truncatedZetaPolynomial_mul_mobiusMollifier
    (X : ℕ) (x : ℝ) (s : ℂ) :
    truncatedZetaPolynomial x s * mobiusMollifier X s =
      mollifiedTruncatedPolynomial X (Nat.floor x) s := by
  unfold truncatedZetaPolynomial mobiusMollifier
  exact truncatedZeta_sum_mul_mobius_sum_eq_mollifiedTruncatedPolynomial
    X (Nat.floor x) s

/-- The mollified zeta error decomposes using the canonical zeta remainder,
so the remainder term is a genuine function rather than a pointwise witness. -/
theorem mollifiedZetaError_eq_tail_add_canonicalRemainder
    {X : ℕ} (hX : 0 < X) (s : ℂ) (x : ℝ)
    (hfloor : 0 < Nat.floor x) :
    mollifiedZetaError X s =
        (∑ n ∈ Finset.Icc (min X (Nat.floor x) + 1)
            (Nat.floor x * X),
          mollifiedTruncatedCoefficient X (Nat.floor x) n /
            (n : ℂ) ^ s) +
          carlsonZetaRemainder s x * mobiusMollifier X s := by
  have htail := mollifiedTruncatedPolynomial_sub_one_eq_tail hX hfloor s
  unfold mollifiedZetaError
  rw [riemannZeta_eq_truncated_add_carlsonZetaRemainder]
  change (truncatedZetaPolynomial x s + carlsonZetaRemainder s x) *
      mobiusMollifier X s - 1 = _
  rw [add_mul, truncatedZetaPolynomial_mul_mobiusMollifier]
  calc
    mollifiedTruncatedPolynomial X (Nat.floor x) s +
        carlsonZetaRemainder s x * mobiusMollifier X s - 1 =
      (mollifiedTruncatedPolynomial X (Nat.floor x) s - 1) +
        carlsonZetaRemainder s x * mobiusMollifier X s := by ring
    _ = _ := by rw [htail]

/-- Squaring the norm of the canonical decomposition separates the finite tail
and the now-integrable canonical remainder contribution. -/
theorem norm_mollifiedZetaError_sq_le_tail_add_canonicalRemainder
    {X : ℕ} (hX : 0 < X) (s : ℂ) (x : ℝ)
    (hfloor : 0 < Nat.floor x) :
    ‖mollifiedZetaError X s‖ ^ 2 ≤
        2 * ‖∑ n ∈ Finset.Icc (min X (Nat.floor x) + 1)
            (Nat.floor x * X),
          mollifiedTruncatedCoefficient X (Nat.floor x) n /
            (n : ℂ) ^ s‖ ^ 2 +
          2 * ‖carlsonZetaRemainder s x * mobiusMollifier X s‖ ^ 2 := by
  let A : ℂ :=
    ∑ n ∈ Finset.Icc (min X (Nat.floor x) + 1) (Nat.floor x * X),
      mollifiedTruncatedCoefficient X (Nat.floor x) n / (n : ℂ) ^ s
  let B : ℂ := carlsonZetaRemainder s x * mobiusMollifier X s
  have hdecomp : mollifiedZetaError X s = A + B := by
    exact mollifiedZetaError_eq_tail_add_canonicalRemainder hX s x hfloor
  rw [hdecomp]
  have htri : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le A B
  have hA : 0 ≤ ‖A‖ := norm_nonneg A
  have hB : 0 ≤ ‖B‖ := norm_nonneg B
  have hAB : 0 ≤ ‖A + B‖ := norm_nonneg (A + B)
  dsimp [A, B]
  nlinarith [sq_nonneg (‖A‖ - ‖B‖)]

/-- A uniform pointwise bound for the canonical zeta remainder converts its
product with the Möbius mollifier into the sharp mollifier mean-square bound. -/
theorem canonicalRemainder_mul_mobius_meanSquare_le
    {X : ℕ} (hX : 1 ≤ X) {sigma a b x K : ℝ}
    (hab : a ≤ b) (hsigma : 1 / 2 < sigma) (hsigma1 : sigma < 1)
    (hK : 0 ≤ K)
    (hR : ∀ t ∈ Set.Icc a b,
      ‖carlsonZetaRemainder ((sigma : ℂ) + Complex.I * t) x‖ ≤ K) :
    ∫ t in a..b,
        ‖carlsonZetaRemainder ((sigma : ℂ) + Complex.I * t) x *
          mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      K ^ 2 * (((b - a) + 4 * Real.pi) *
        (2 * (1 +
          ((X : ℝ) ^ (2 - 2 * sigma) - 1) / (2 - 2 * sigma)))) := by
  have hsigma_ne : sigma ≠ 1 := ne_of_lt hsigma1
  have hRcont := continuous_carlsonZetaRemainder_verticalLine x sigma hsigma_ne
  have hMcont := continuous_mobiusMollifier_verticalLine X sigma
  have hleftInt : IntervalIntegrable (fun t : ℝ =>
      ‖carlsonZetaRemainder ((sigma : ℂ) + Complex.I * t) x *
        mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2)
      MeasureTheory.volume a b :=
    ((hRcont.mul hMcont).norm.pow 2).intervalIntegrable a b
  have hrightInt : IntervalIntegrable (fun t : ℝ =>
      K ^ 2 * ‖mobiusMollifier X
        ((sigma : ℂ) + Complex.I * t)‖ ^ 2)
      MeasureTheory.volume a b :=
    (continuous_const.mul (hMcont.norm.pow 2)).intervalIntegrable a b
  have hpoint : ∀ t ∈ Set.Icc a b,
      ‖carlsonZetaRemainder ((sigma : ℂ) + Complex.I * t) x *
        mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      K ^ 2 * ‖mobiusMollifier X
        ((sigma : ℂ) + Complex.I * t)‖ ^ 2 := by
    intro t ht
    rw [norm_mul, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hnorm := norm_nonneg
      (carlsonZetaRemainder ((sigma : ℂ) + Complex.I * t) x)
    nlinarith [hR t ht]
  calc
    ∫ t in a..b,
        ‖carlsonZetaRemainder ((sigma : ℂ) + Complex.I * t) x *
          mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ∫ t in a..b,
        K ^ 2 * ‖mobiusMollifier X
          ((sigma : ℂ) + Complex.I * t)‖ ^ 2 :=
      intervalIntegral.integral_mono_on hab hleftInt hrightInt hpoint
    _ = K ^ 2 * ∫ t in a..b,
        ‖mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ K ^ 2 * (((b - a) + 4 * Real.pi) *
        (2 * (1 +
          ((X : ℝ) ^ (2 - 2 * sigma) - 1) / (2 - 2 * sigma)))) := by
      exact mul_le_mul_of_nonneg_left
        (mobiusMollifier_meanSquare_le_rpow_endpoint
          hX hab hsigma hsigma1)
        (sq_nonneg K)

/-- The canonical Carlson remainder estimate with a variable comparability
factor supplies a uniform bound throughout a genuine height interval. -/
theorem exists_canonicalRemainder_mul_mobius_meanSquare_le_of_comparable :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (kappa : ℝ) (X : ℕ) (sigma a b x : ℝ),
      0 < kappa →
      1 ≤ X → a ≤ b → 1 / 2 < sigma → sigma < 1 → 2 ≤ x →
      (∀ t ∈ Set.Icc a b,
        |t| ≤ x / 2 ∧ x ≤ kappa * |t|) →
        ∫ t in a..b,
            ‖carlsonZetaRemainder ((sigma : ℂ) + Complex.I * t) x *
              mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
          ((A + kappa) * x ^ (-sigma)) ^ 2 *
            (((b - a) + 4 * Real.pi) *
              (2 * (1 +
                ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
                  (2 - 2 * sigma)))) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_norm_carlsonZetaRemainder_le_of_comparable
  refine ⟨A, hA, ?_⟩
  intro kappa X sigma a b x hkappa hX hab hsigma hsigma1 hx hheight
  apply canonicalRemainder_mul_mobius_meanSquare_le
    hX hab hsigma hsigma1
  · exact mul_nonneg (add_nonneg hA hkappa.le)
      (Real.rpow_nonneg (by linarith) _)
  · intro t ht
    have hs_ne : ((sigma : ℂ) + Complex.I * t) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      linarith
    have hcomparability := hheight t ht
    have hs_lower : (1 / 2 : ℝ) ≤
        ((sigma : ℂ) + Complex.I * t).re := by
      simpa using hsigma.le
    have hs_upper : ((sigma : ℂ) + Complex.I * t).re ≤ 1 := by
      simpa using hsigma1.le
    have him_upper : |((sigma : ℂ) + Complex.I * t).im| ≤ x / 2 := by
      simpa using hcomparability.1
    have him_lower :
        x ≤ kappa * |((sigma : ℂ) + Complex.I * t).im| := by
      simpa using hcomparability.2
    simpa using hbound kappa ((sigma : ℂ) + Complex.I * t) x
      hkappa hs_lower hs_upper hs_ne hx him_upper him_lower

/-- The original exact-height `kappa = 2` specialization. -/
theorem exists_canonicalRemainder_mul_mobius_meanSquare_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (sigma a b x : ℝ),
      1 ≤ X → a ≤ b → 1 / 2 < sigma → sigma < 1 → 2 ≤ x →
      (∀ t ∈ Set.Icc a b, |t| ≤ x / 2 ∧ x ≤ 2 * |t|) →
        ∫ t in a..b,
            ‖carlsonZetaRemainder ((sigma : ℂ) + Complex.I * t) x *
              mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
          (C * x ^ (-sigma)) ^ 2 * (((b - a) + 4 * Real.pi) *
            (2 * (1 +
              ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
                (2 - 2 * sigma)))) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_canonicalRemainder_mul_mobius_meanSquare_le_of_comparable
  refine ⟨A + 2, by positivity, ?_⟩
  intro X sigma a b x hX hab hsigma hsigma1 hx hheight
  exact hbound 2 X sigma a b x (by norm_num) hX hab hsigma hsigma1 hx
    hheight

/-- Integrating the canonical pointwise decomposition separates the full
mollified-zeta second moment into its finite tail and canonical remainder.
This common layer lets coarse and sharp Carlson endpoints share the same
analytic bookkeeping. -/
theorem mollifiedZetaError_meanSquare_le_tail_add_remainder
    {X : ℕ} (hX : 0 < X) {sigma a b x : ℝ}
    (hab : a ≤ b) (hsigma1 : sigma ≠ 1)
    (hfloor : 0 < Nat.floor x) :
    (∫ t in a..b,
        ‖mollifiedZetaError X
          ((sigma : ℂ) + Complex.I * t)‖ ^ 2) ≤
      2 * (∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X (Nat.floor x) + 1)
            (Nat.floor x * X),
          mollifiedTruncatedCoefficient X (Nat.floor x) n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2) +
      2 * (∫ t in a..b,
        ‖carlsonZetaRemainder ((sigma : ℂ) + Complex.I * t) x *
          mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2) := by
  let Tail : ℝ → ℂ := fun t =>
    ∑ n ∈ Finset.Icc (min X (Nat.floor x) + 1) (Nat.floor x * X),
      mollifiedTruncatedCoefficient X (Nat.floor x) n /
        (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)
  let Rem : ℝ → ℂ := fun t =>
    carlsonZetaRemainder ((sigma : ℂ) + Complex.I * t) x *
      mobiusMollifier X ((sigma : ℂ) + Complex.I * t)
  have hTailCont : Continuous Tail := by
    have hpoly : Continuous (fun t : ℝ =>
        DirichletPolynomial.finiteDirichletPolynomial
          (Finset.Icc (min X (Nat.floor x) + 1) (Nat.floor x * X))
          (mollifiedTailCoefficient X (Nat.floor x) sigma) t) := by
      unfold DirichletPolynomial.finiteDirichletPolynomial
        DirichletPolynomial.finiteExponentialSum
      fun_prop
    exact hpoly.congr fun t =>
      (mollifiedTruncatedTail_verticalLine_eq_finiteDirichletPolynomial
        X (Nat.floor x) sigma t).symm
  have hRcont := continuous_carlsonZetaRemainder_verticalLine x sigma hsigma1
  have hMcont := continuous_mobiusMollifier_verticalLine X sigma
  have hRemCont : Continuous Rem := hRcont.mul hMcont
  have hErrorCont : Continuous (fun t : ℝ =>
      mollifiedZetaError X ((sigma : ℂ) + Complex.I * t)) := by
    exact (hTailCont.add hRemCont).congr fun t =>
      (mollifiedZetaError_eq_tail_add_canonicalRemainder
        hX ((sigma : ℂ) + Complex.I * t) x hfloor).symm
  have hTailSqInt : IntervalIntegrable (fun t : ℝ => ‖Tail t‖ ^ 2)
      MeasureTheory.volume a b :=
    (hTailCont.norm.pow 2).intervalIntegrable a b
  have hRemSqInt : IntervalIntegrable (fun t : ℝ => ‖Rem t‖ ^ 2)
      MeasureTheory.volume a b :=
    (hRemCont.norm.pow 2).intervalIntegrable a b
  have hErrorSqInt : IntervalIntegrable (fun t : ℝ =>
      ‖mollifiedZetaError X ((sigma : ℂ) + Complex.I * t)‖ ^ 2)
      MeasureTheory.volume a b :=
    (hErrorCont.norm.pow 2).intervalIntegrable a b
  have hMajorantInt : IntervalIntegrable (fun t : ℝ =>
      2 * ‖Tail t‖ ^ 2 + 2 * ‖Rem t‖ ^ 2)
      MeasureTheory.volume a b :=
    ((continuous_const.mul (hTailCont.norm.pow 2)).add
      (continuous_const.mul (hRemCont.norm.pow 2))).intervalIntegrable a b
  have hpoint : ∀ t ∈ Set.Icc a b,
      ‖mollifiedZetaError X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
        2 * ‖Tail t‖ ^ 2 + 2 * ‖Rem t‖ ^ 2 := by
    intro t _
    exact norm_mollifiedZetaError_sq_le_tail_add_canonicalRemainder
      hX ((sigma : ℂ) + Complex.I * t) x hfloor
  change (∫ t in a..b,
      ‖mollifiedZetaError X ((sigma : ℂ) + Complex.I * t)‖ ^ 2) ≤
    2 * (∫ t in a..b, ‖Tail t‖ ^ 2) +
      2 * (∫ t in a..b, ‖Rem t‖ ^ 2)
  calc
    (∫ t in a..b,
        ‖mollifiedZetaError X ((sigma : ℂ) + Complex.I * t)‖ ^ 2) ≤
      ∫ t in a..b, (2 * ‖Tail t‖ ^ 2 + 2 * ‖Rem t‖ ^ 2) :=
        intervalIntegral.integral_mono_on
          hab hErrorSqInt hMajorantInt hpoint
    _ = 2 * (∫ t in a..b, ‖Tail t‖ ^ 2) +
        2 * (∫ t in a..b, ‖Rem t‖ ^ 2) := by
      rw [intervalIntegral.integral_add
        (hTailSqInt.const_mul 2) (hRemSqInt.const_mul 2),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]

/-- The full mollified-zeta second moment with the sharp, separated Carlson
tail endpoint. -/
theorem exists_mollifiedZetaError_meanSquare_le_sharpEndpoint_of_comparable :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (kappa : ℝ) (X : ℕ) (sigma a b x : ℝ),
      0 < kappa →
      1 ≤ X → a ≤ b → 1 / 2 < sigma → sigma < 1 → 2 ≤ x →
      (∀ t ∈ Set.Icc a b,
        |t| ≤ x / 2 ∧ x ≤ kappa * |t|) →
        ∫ t in a..b,
            ‖mollifiedZetaError X
              ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
          2 * ((b - a) * ((1 + Real.log (Nat.floor x * X)) ^ 3 *
              ((2 + 1 / (2 * sigma - 1)) *
                ((min X (Nat.floor x) + 1 : ℕ) : ℝ) ^
                  (1 - 2 * sigma))) +
            8 * Real.pi * ((1 + Real.log (Nat.floor x * X)) ^ 3 *
              ((2 + 1 / (2 - 2 * sigma)) *
                (((Nat.floor x) * X : ℕ) : ℝ) ^
                  (2 - 2 * sigma)))) +
          2 * ((((A + kappa) * x ^ (-sigma)) ^ 2) *
            (((b - a) + 4 * Real.pi) *
              (2 * (1 +
                ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
                  (2 - 2 * sigma))))) := by
  obtain ⟨A, hA, hRemainder⟩ :=
    exists_norm_carlsonZetaRemainder_le_of_comparable
  refine ⟨A, hA, ?_⟩
  intro kappa X sigma a b x hkappa hX hab hsigma hsigma1 hx hheight
  have hXpos : 0 < X := lt_of_lt_of_le Nat.zero_lt_one hX
  have hfloor : 0 < Nat.floor x := Nat.floor_pos.mpr (by linarith)
  have hfloorTwo : 2 ≤ Nat.floor x := by
    exact Nat.le_floor hx
  have hsupport : min X (Nat.floor x) + 1 ≤ Nat.floor x * X := by
    by_cases hXone : X = 1
    · subst X
      rw [min_eq_left (by omega), Nat.mul_one]
      omega
    · have hXtwo : 2 ≤ X := by omega
      have hmin := min_le_right X (Nat.floor x)
      have hproduct : Nat.floor x + 1 ≤ Nat.floor x * X := by
        nlinarith
      omega
  have hsplit := mollifiedZetaError_meanSquare_le_tail_add_remainder
    hXpos hab (ne_of_lt hsigma1) hfloor
  have hTail := mollifiedTruncatedTail_meanSquare_le_sharpDivisorEndpoint
    (X := X) (N := Nat.floor x) hab hsupport hsigma hsigma1
  have hK : 0 ≤ (A + kappa) * x ^ (-sigma) :=
    mul_nonneg (add_nonneg hA hkappa.le)
      (Real.rpow_nonneg (by linarith) _)
  have hRpoint : ∀ t ∈ Set.Icc a b,
      ‖carlsonZetaRemainder ((sigma : ℂ) + Complex.I * t) x‖ ≤
        (A + kappa) * x ^ (-sigma) := by
    intro t ht
    have hs_ne : ((sigma : ℂ) + Complex.I * t) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      linarith
    have hcomparability := hheight t ht
    have hs_lower : (1 / 2 : ℝ) ≤
        ((sigma : ℂ) + Complex.I * t).re := by simpa using hsigma.le
    have hs_upper : ((sigma : ℂ) + Complex.I * t).re ≤ 1 := by
      simpa using hsigma1.le
    have him_upper : |((sigma : ℂ) + Complex.I * t).im| ≤ x / 2 := by
      simpa using hcomparability.1
    have him_lower :
        x ≤ kappa * |((sigma : ℂ) + Complex.I * t).im| := by
      simpa using hcomparability.2
    simpa using hRemainder kappa ((sigma : ℂ) + Complex.I * t) x
      hkappa hs_lower hs_upper hs_ne hx him_upper him_lower
  have hRem := canonicalRemainder_mul_mobius_meanSquare_le
    hX hab hsigma hsigma1 hK hRpoint
  exact hsplit.trans (add_le_add
    (mul_le_mul_of_nonneg_left hTail (by norm_num))
    (mul_le_mul_of_nonneg_left hRem (by norm_num)))

/-- The full mollified zeta error has a Carlson-ready second-moment bound with
a variable height-comparability factor. -/
theorem exists_mollifiedZetaError_meanSquare_le_endpoint_of_comparable :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (kappa : ℝ) (X : ℕ) (sigma a b x : ℝ),
      0 < kappa →
      1 ≤ X → a ≤ b → 1 / 2 < sigma → sigma < 1 → 2 ≤ x →
      (∀ t ∈ Set.Icc a b,
        |t| ≤ x / 2 ∧ x ≤ kappa * |t|) →
        ∫ t in a..b,
            ‖mollifiedZetaError X
              ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
          2 * (((b - a) + 4 * Real.pi) *
            (2 * ((min X (Nat.floor x) + 1 : ℕ) : ℝ) ^
                (1 - 2 * sigma) *
              ((((Nat.floor x) * X : ℕ) : ℝ) *
                (1 + Real.log (Nat.floor x * X)) ^ 3))) +
          2 * ((((A + kappa) * x ^ (-sigma)) ^ 2) *
            (((b - a) + 4 * Real.pi) *
              (2 * (1 +
                ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
                  (2 - 2 * sigma))))) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_norm_carlsonZetaRemainder_le_of_comparable
  refine ⟨A, hA, ?_⟩
  intro kappa X sigma a b x hkappa hX hab hsigma hsigma1 hx hheight
  have hXpos : 0 < X := lt_of_lt_of_le Nat.zero_lt_one hX
  have hfloor : 0 < Nat.floor x := Nat.floor_pos.mpr (by linarith)
  let Tail : ℝ → ℂ := fun t =>
    ∑ n ∈ Finset.Icc (min X (Nat.floor x) + 1) (Nat.floor x * X),
      mollifiedTruncatedCoefficient X (Nat.floor x) n /
        (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)
  let Rem : ℝ → ℂ := fun t =>
    carlsonZetaRemainder ((sigma : ℂ) + Complex.I * t) x *
      mobiusMollifier X ((sigma : ℂ) + Complex.I * t)
  have hTailCont : Continuous Tail := by
    have hpoly : Continuous (fun t : ℝ =>
        DirichletPolynomial.finiteDirichletPolynomial
          (Finset.Icc (min X (Nat.floor x) + 1) (Nat.floor x * X))
          (mollifiedTailCoefficient X (Nat.floor x) sigma) t) := by
      unfold DirichletPolynomial.finiteDirichletPolynomial
        DirichletPolynomial.finiteExponentialSum
      fun_prop
    exact hpoly.congr fun t =>
      (mollifiedTruncatedTail_verticalLine_eq_finiteDirichletPolynomial
        X (Nat.floor x) sigma t).symm
  have hRcont := continuous_carlsonZetaRemainder_verticalLine
    x sigma (ne_of_lt hsigma1)
  have hMcont := continuous_mobiusMollifier_verticalLine X sigma
  have hRemCont : Continuous Rem := hRcont.mul hMcont
  have hErrorCont : Continuous (fun t : ℝ =>
      mollifiedZetaError X ((sigma : ℂ) + Complex.I * t)) := by
    exact (hTailCont.add hRemCont).congr fun t =>
      (mollifiedZetaError_eq_tail_add_canonicalRemainder
        hXpos ((sigma : ℂ) + Complex.I * t) x hfloor).symm
  have hTailSqInt : IntervalIntegrable (fun t : ℝ => ‖Tail t‖ ^ 2)
      MeasureTheory.volume a b :=
    (hTailCont.norm.pow 2).intervalIntegrable a b
  have hRemSqInt : IntervalIntegrable (fun t : ℝ => ‖Rem t‖ ^ 2)
      MeasureTheory.volume a b :=
    (hRemCont.norm.pow 2).intervalIntegrable a b
  have hErrorSqInt : IntervalIntegrable (fun t : ℝ =>
      ‖mollifiedZetaError X ((sigma : ℂ) + Complex.I * t)‖ ^ 2)
      MeasureTheory.volume a b :=
    (hErrorCont.norm.pow 2).intervalIntegrable a b
  have hMajorantInt : IntervalIntegrable (fun t : ℝ =>
      2 * ‖Tail t‖ ^ 2 + 2 * ‖Rem t‖ ^ 2)
      MeasureTheory.volume a b :=
    ((continuous_const.mul (hTailCont.norm.pow 2)).add
      (continuous_const.mul (hRemCont.norm.pow 2))).intervalIntegrable a b
  have hpoint : ∀ t ∈ Set.Icc a b,
      ‖mollifiedZetaError X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
        2 * ‖Tail t‖ ^ 2 + 2 * ‖Rem t‖ ^ 2 := by
    intro t _
    exact norm_mollifiedZetaError_sq_le_tail_add_canonicalRemainder
      hXpos ((sigma : ℂ) + Complex.I * t) x hfloor
  have hintegral :
      (∫ t in a..b,
          ‖mollifiedZetaError X ((sigma : ℂ) + Complex.I * t)‖ ^ 2) ≤
        2 * (∫ t in a..b, ‖Tail t‖ ^ 2) +
          2 * (∫ t in a..b, ‖Rem t‖ ^ 2) := by
    calc
      (∫ t in a..b,
          ‖mollifiedZetaError X ((sigma : ℂ) + Complex.I * t)‖ ^ 2) ≤
        ∫ t in a..b, (2 * ‖Tail t‖ ^ 2 + 2 * ‖Rem t‖ ^ 2) :=
        intervalIntegral.integral_mono_on
          hab hErrorSqInt hMajorantInt hpoint
      _ = 2 * (∫ t in a..b, ‖Tail t‖ ^ 2) +
          2 * (∫ t in a..b, ‖Rem t‖ ^ 2) := by
        rw [intervalIntegral.integral_add
          (hTailSqInt.const_mul 2) (hRemSqInt.const_mul 2),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  have hTailBound :
      (∫ t in a..b, ‖Tail t‖ ^ 2) ≤
        ((b - a) + 4 * Real.pi) *
          (2 * ((min X (Nat.floor x) + 1 : ℕ) : ℝ) ^
              (1 - 2 * sigma) *
            ((((Nat.floor x) * X : ℕ) : ℝ) *
              (1 + Real.log (Nat.floor x * X)) ^ 3)) := by
    exact mollifiedTruncatedTail_meanSquare_le_prefix_bound hab hsigma
  have hK : 0 ≤ (A + kappa) * x ^ (-sigma) :=
    mul_nonneg (add_nonneg hA hkappa.le)
      (Real.rpow_nonneg (by linarith) _)
  have hRpoint : ∀ t ∈ Set.Icc a b,
      ‖carlsonZetaRemainder ((sigma : ℂ) + Complex.I * t) x‖ ≤
        (A + kappa) * x ^ (-sigma) := by
    intro t ht
    have hs_ne : ((sigma : ℂ) + Complex.I * t) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      linarith
    have hcomparability := hheight t ht
    have hs_lower : (1 / 2 : ℝ) ≤
        ((sigma : ℂ) + Complex.I * t).re := by simpa using hsigma.le
    have hs_upper : ((sigma : ℂ) + Complex.I * t).re ≤ 1 := by
      simpa using hsigma1.le
    have him_upper : |((sigma : ℂ) + Complex.I * t).im| ≤ x / 2 := by
      simpa using hcomparability.1
    have him_lower :
        x ≤ kappa * |((sigma : ℂ) + Complex.I * t).im| := by
      simpa using hcomparability.2
    simpa using hbound kappa ((sigma : ℂ) + Complex.I * t) x
      hkappa hs_lower hs_upper hs_ne hx him_upper him_lower
  have hRemBound :
      (∫ t in a..b, ‖Rem t‖ ^ 2) ≤
        ((A + kappa) * x ^ (-sigma)) ^ 2 *
          (((b - a) + 4 * Real.pi) *
          (2 * (1 +
            ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
              (2 - 2 * sigma)))) := by
    exact canonicalRemainder_mul_mobius_meanSquare_le
      hX hab hsigma hsigma1 hK hRpoint
  exact hintegral.trans (add_le_add
    (mul_le_mul_of_nonneg_left hTailBound (by norm_num))
    (mul_le_mul_of_nonneg_left hRemBound (by norm_num)))

/-- The original exact-height `kappa = 2` specialization of the mollified
zeta second-moment estimate. -/
theorem exists_mollifiedZetaError_meanSquare_le_endpoint :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (sigma a b x : ℝ),
      1 ≤ X → a ≤ b → 1 / 2 < sigma → sigma < 1 → 2 ≤ x →
      (∀ t ∈ Set.Icc a b, |t| ≤ x / 2 ∧ x ≤ 2 * |t|) →
        ∫ t in a..b,
            ‖mollifiedZetaError X
              ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
          2 * (((b - a) + 4 * Real.pi) *
            (2 * ((min X (Nat.floor x) + 1 : ℕ) : ℝ) ^
                (1 - 2 * sigma) *
              ((((Nat.floor x) * X : ℕ) : ℝ) *
                (1 + Real.log (Nat.floor x * X)) ^ 3))) +
          2 * ((C * x ^ (-sigma)) ^ 2 *
            (((b - a) + 4 * Real.pi) *
              (2 * (1 +
                ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
                  (2 - 2 * sigma))))) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_mollifiedZetaError_meanSquare_le_endpoint_of_comparable
  refine ⟨A + 2, by positivity, ?_⟩
  intro X sigma a b x hX hab hsigma hsigma1 hx hheight
  exact hbound 2 X sigma a b x (by norm_num) hX hab hsigma hsigma1 hx
    hheight

/-- The Carlson-ready zeta approximation decomposes the mollified error into
a finite Dirichlet-polynomial product and a controlled remainder times the
mollifier.  The final inequality is the pointwise input for the second-moment
argument. -/
theorem exists_mollifiedZetaError_decomposition :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (s : ℂ) (x : ℝ),
      (1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 → s ≠ 1 → 2 ≤ x →
        |s.im| ≤ x / 2 → x ≤ 2 * |s.im| →
          ∃ R : ℂ,
            ‖R‖ ≤ C * x ^ (-s.re) ∧
            mollifiedZetaError X s =
              (truncatedZetaPolynomial x s * mobiusMollifier X s - 1) +
                R * mobiusMollifier X s ∧
            ‖mollifiedZetaError X s‖ ^ 2 ≤
              2 * ‖truncatedZetaPolynomial x s * mobiusMollifier X s - 1‖ ^ 2 +
                2 * ‖R * mobiusMollifier X s‖ ^ 2 := by
  obtain ⟨C, hC, happrox⟩ := exists_riemannZeta_carlson_approximation
  refine ⟨C, hC, ?_⟩
  intro X s x hs_lower hs_upper hs1 hx him_upper him_lower
  rcases happrox s x hs_lower hs_upper hs1 hx him_upper him_lower with
    ⟨R, hR_eq, hR_bound⟩
  refine ⟨R, hR_bound, ?_, ?_⟩
  · unfold mollifiedZetaError truncatedZetaPolynomial
    rw [hR_eq]
    ring
  · let A : ℂ :=
      truncatedZetaPolynomial x s * mobiusMollifier X s - 1
    let B : ℂ := R * mobiusMollifier X s
    have hdecomp : mollifiedZetaError X s = A + B := by
      dsimp [A, B]
      unfold mollifiedZetaError truncatedZetaPolynomial
      rw [hR_eq]
      ring
    rw [hdecomp]
    have htri : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le A B
    have hA : 0 ≤ ‖A‖ := norm_nonneg A
    have hB : 0 ≤ ‖B‖ := norm_nonneg B
    have hAB : 0 ≤ ‖A + B‖ := norm_nonneg (A + B)
    dsimp [A, B]
    nlinarith [sq_nonneg (‖A‖ - ‖B‖)]

/-- Carlson's pointwise decomposition with the finite product already
collected into its Dirichlet-convolution coefficients.  This is the form in
which Möbius cancellation can be fed into the eventual second-moment bound. -/
theorem exists_mollifiedZetaError_coefficient_decomposition :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (s : ℂ) (x : ℝ),
      (1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 → s ≠ 1 → 2 ≤ x →
        |s.im| ≤ x / 2 → x ≤ 2 * |s.im| →
          ∃ R : ℂ,
            ‖R‖ ≤ C * x ^ (-s.re) ∧
            mollifiedZetaError X s =
              (mollifiedTruncatedPolynomial X (Nat.floor x) s - 1) +
                R * mobiusMollifier X s ∧
            ‖mollifiedZetaError X s‖ ^ 2 ≤
              2 * ‖mollifiedTruncatedPolynomial X (Nat.floor x) s - 1‖ ^ 2 +
                2 * ‖R * mobiusMollifier X s‖ ^ 2 := by
  obtain ⟨C, hC, hdecomp⟩ := exists_mollifiedZetaError_decomposition
  refine ⟨C, hC, ?_⟩
  intro X s x hs_lower hs_upper hs1 hx him_upper him_lower
  rcases hdecomp X s x hs_lower hs_upper hs1 hx him_upper him_lower with
    ⟨R, hR, hEq, hnorm⟩
  rw [truncatedZetaPolynomial_mul_mobiusMollifier X x s] at hEq hnorm
  exact ⟨R, hR, hEq, hnorm⟩

/-- Once the mollifier cutoff is positive, exact Möbius inversion removes all
coefficients through `min X ⌊x⌋`.  This tail form isolates the finite
Dirichlet polynomial whose mean square remains to be estimated in Carlson's
argument. -/
theorem exists_mollifiedZetaError_tail_decomposition :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (s : ℂ) (x : ℝ),
      0 < X → (1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 → s ≠ 1 → 2 ≤ x →
        |s.im| ≤ x / 2 → x ≤ 2 * |s.im| →
          ∃ R : ℂ,
            ‖R‖ ≤ C * x ^ (-s.re) ∧
            mollifiedZetaError X s =
                (∑ n ∈ Finset.Icc (min X (Nat.floor x) + 1)
                    (Nat.floor x * X),
                  mollifiedTruncatedCoefficient X (Nat.floor x) n /
                    (n : ℂ) ^ s) + R * mobiusMollifier X s ∧
              ‖mollifiedZetaError X s‖ ^ 2 ≤
                2 * ‖∑ n ∈ Finset.Icc (min X (Nat.floor x) + 1)
                    (Nat.floor x * X),
                  mollifiedTruncatedCoefficient X (Nat.floor x) n /
                    (n : ℂ) ^ s‖ ^ 2 +
                  2 * ‖R * mobiusMollifier X s‖ ^ 2 := by
  obtain ⟨C, hC, hdecomp⟩ := exists_mollifiedZetaError_coefficient_decomposition
  refine ⟨C, hC, ?_⟩
  intro X s x hX hs_lower hs_upper hs1 hx him_upper him_lower
  rcases hdecomp X s x hs_lower hs_upper hs1 hx him_upper him_lower with
    ⟨R, hR, hEq, hnorm⟩
  have hfloor : 0 < Nat.floor x := Nat.floor_pos.mpr (by linarith)
  have htail := mollifiedTruncatedPolynomial_sub_one_eq_tail hX hfloor s
  rw [htail] at hEq hnorm
  exact ⟨R, hR, hEq, hnorm⟩

end CarlsonZeroDensity
end PrimeNumberTheorem
