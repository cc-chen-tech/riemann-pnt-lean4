import PrimeNumberTheorem.CarlsonZetaApproximation
import PrimeNumberTheorem.CarlsonMollifierCoefficients
import PrimeNumberTheorem.CarlsonDivisorSquare
import PrimeNumberTheorem.CarneiroLittmannKernelConstruction
import PrimeNumberTheorem.MobiusMollifier

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
