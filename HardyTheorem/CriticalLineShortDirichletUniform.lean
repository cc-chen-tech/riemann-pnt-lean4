import HardyTheorem.CriticalLineShortDirichlet
import MathlibAux.LogSquareSummability
import MathlibAux.NegativeLogDirichletPolynomialMeanSquare

open Complex MeasureTheory Set

namespace HardyTheorem

/-- The nonconstant Dirichlet polynomial arising from a critical-line short
integral has a second moment `O(T)`, with a constant independent of the window
length and of the moving cutoff `floor (4T)`. -/
theorem exists_integral_normSq_criticalLineShortDirichletPolynomial_le_mul :
    ∃ B : ℝ, 0 < B ∧
      ∀ T delta : ℝ, 1 ≤ T → 0 ≤ delta → delta ≤ T →
        (∫ t in T..2 * T - delta,
            Complex.normSq
              (criticalLineShortDirichletPolynomial delta
                (firstZetaApproximationCutoff T) t)) ≤
          B * T := by
  let K : ℝ := 5 * Real.pi + 4
  let B : ℝ := 16 * (1 + 16 * K)
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro T delta hT hdelta hdeltaT
  let N : ℕ := firstZetaApproximationCutoff T
  let s : Finset ℕ := Finset.Icc 2 N
  have hN : 0 < N := by
    dsimp only [N, firstZetaApproximationCutoff]
    apply Nat.floor_pos.mpr
    linarith
  have hpositive : ∀ n ∈ s, n ≠ 0 := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    omega
  have hupper : ∀ n ∈ s, n ≤ N := by
    intro n hn
    exact (Finset.mem_Icc.mp hn).2
  have hraw :=
    MathlibAux.integral_normSq_negLogExponentialPolynomial_le_of_upper
      hN s (criticalLineShortDirichletCoeff delta) hpositive hupper
        (a := T) (b := 2 * T - delta)
  have henergy :
      (∑ n ∈ s,
          Complex.normSq (criticalLineShortDirichletCoeff delta n)) ≤ 16 := by
    simpa only [s] using
      sum_normSq_criticalLineShortDirichletCoeff_le_sixteen
        delta N
  have henergy0 :
      0 ≤ ∑ n ∈ s,
          Complex.normSq (criticalLineShortDirichletCoeff delta n) :=
    Finset.sum_nonneg fun n hn => Complex.normSq_nonneg _
  have hNupper : (N : ℝ) ≤ 4 * T := by
    dsimp only [N, firstZetaApproximationCutoff]
    exact Nat.floor_le (by positivity)
  have hfactorUpper :
      (2 * T - delta - T) + 4 * K * N ≤
        (1 + 16 * K) * T := by
    have h4K : 0 ≤ 4 * K := by positivity
    have hmul := mul_le_mul_of_nonneg_left hNupper h4K
    dsimp only [K] at hmul ⊢
    nlinarith
  have hfactorUpper0 : 0 ≤ (1 + 16 * K) * T := by positivity
  change
    (∫ t in T..2 * T - delta,
        Complex.normSq
          (MathlibAux.exponentialPolynomial s
            (criticalLineShortDirichletCoeff delta)
              (fun n => -Real.log n) t)) ≤ B * T
  calc
    (∫ t in T..2 * T - delta,
        Complex.normSq
          (MathlibAux.exponentialPolynomial s
            (criticalLineShortDirichletCoeff delta)
              (fun n => -Real.log n) t)) ≤
        ((2 * T - delta - T) + 4 * K * N) *
          ∑ n ∈ s,
            Complex.normSq (criticalLineShortDirichletCoeff delta n) := by
      simpa only [K] using hraw
    _ ≤ ((1 + 16 * K) * T) * 16 :=
      mul_le_mul hfactorUpper henergy henergy0 hfactorUpper0
    _ = B * T := by
      dsimp only [B]
      ring

end HardyTheorem
