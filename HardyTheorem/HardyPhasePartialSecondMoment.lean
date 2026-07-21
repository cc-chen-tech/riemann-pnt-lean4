import HardyTheorem.HardyPhaseMovingSecondMoment

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-- A finite sub-sum of the linearized Hardy short polynomial.  Splitting the
full index interval into frequency bands lets the moving Hilbert estimate use
different smoothing scales on each band. -/
noncomputable def hardyPhaseLinearizedPartialSum
    (s : Finset ℕ) (delta t : ℝ) : ℂ :=
  ∑ n ∈ s, hardyPhaseLinearizedCoeff n delta t

/-- Removing the common theta phase from an arbitrary positive-index band. -/
theorem hardyPhaseLinearizedPartialSum_eq_commonPhase_mul_negLogPolynomial
    (s : Finset ℕ) {delta t : ℝ} (ht : 0 < t)
    (hpositive : ∀ n ∈ s, n ≠ 0) :
    hardyPhaseLinearizedPartialSum s delta t =
      Complex.exp (I * thetaModel t) *
        MathlibAux.timeDependentNegLogPolynomial s
          (fun x n => hardyPhaseWindowCoeff n delta x) t := by
  rw [hardyPhaseLinearizedPartialSum,
    MathlibAux.timeDependentNegLogPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hardyPhaseLinearizedCoeff_eq_commonPhase_mul_windowCoeff
    (Nat.pos_of_ne_zero (hpositive n hn)) ht]
  have hexp :
      Complex.exp (-I * ((Real.log n : ℂ) * (t : ℂ))) =
        Complex.exp (-I * ((Real.log n * t : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- Pointwise energy of a partial Hardy band in the positive-frequency
convention used by the logarithmic Hilbert inequality. -/
theorem normSq_hardyPhaseLinearizedPartialSum_eq_logPolynomial
    (s : Finset ℕ) {delta t : ℝ} (ht : 0 < t)
    (hpositive : ∀ n ∈ s, n ≠ 0) :
    Complex.normSq (hardyPhaseLinearizedPartialSum s delta t) =
      Complex.normSq
        (MathlibAux.timeDependentLogPolynomial s
          (fun x n => (starRingEnd ℂ) (hardyPhaseWindowCoeff n delta x)) t) := by
  rw [hardyPhaseLinearizedPartialSum_eq_commonPhase_mul_negLogPolynomial
      s ht hpositive,
    Complex.normSq_mul]
  have hphase :
      Complex.normSq (Complex.exp (I * thetaModel t)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_I_mul_ofReal]
    norm_num
  rw [hphase, one_mul, hardyPhaseNegLogPolynomial_eq_conj_positive,
    Complex.normSq_conj]

/-- Moving logarithmic-Hilbert estimate for an arbitrary finite Hardy
frequency band.  The coefficient and derivative energies are explicit
inputs, allowing separate choices of `q` for near and far bands. -/
theorem integral_normSq_hardyPhaseLinearizedPartialSum_le
    {N : ℕ} (hN : 0 < N) (s : Finset ℕ)
    {delta a b q E D : ℝ} (ha : 0 < a) (hab : a ≤ b) (hq : 0 < q)
    (hpositive : ∀ n ∈ s, n ≠ 0) (hupper : ∀ n ∈ s, n ≤ N)
    (henergy : ∀ t ∈ Set.Icc a b,
      (∑ n ∈ s, Complex.normSq
        (hardyPhaseLinearizedCoeff n delta t)) ≤ E)
    (hderivEnergy : ∀ t ∈ Set.Icc a b,
      (∑ n ∈ s, Complex.normSq
        (deriv (hardyPhaseWindowCoeff n delta) t)) ≤ D) :
    (∫ t in a..b,
      Complex.normSq (hardyPhaseLinearizedPartialSum s delta t)) ≤
      (b - a) * E +
        4 * (5 * Real.pi + 4) * N * E +
        |b - a| *
          (2 * (5 * Real.pi + 4) * N *
            (q ^ 2 * D + (q ^ 2)⁻¹ * E)) := by
  let coeff : ℝ → ℕ → ℂ := fun x n =>
    (starRingEnd ℂ) (hardyPhaseWindowCoeff n delta x)
  let coeff' : ℝ → ℕ → ℂ := fun x n => deriv (fun y => coeff y n) x
  have htpos : ∀ t ∈ Set.Icc a b, 0 < t := by
    intro t ht
    exact ha.trans_le ht.1
  have hderiv : ∀ t ∈ Set.Icc a b, ∀ n ∈ s,
      HasDerivAt (fun x => coeff x n) (coeff' t n) t := by
    intro t ht n hn
    exact ((hasDerivAt_hardyPhaseWindowCoeff
      (delta := delta) n (htpos t ht)).star).differentiableAt.hasDerivAt
  have hcoeffCont : ∀ n ∈ s,
      ContinuousOn (fun t => coeff t n) (Set.Icc a b) := by
    intro n hn t ht
    exact ((hasDerivAt_hardyPhaseWindowCoeff n (htpos t ht)).star).continuousAt.continuousWithinAt
  have hcoeffPrimeMeas : ∀ n ∈ s,
      AEStronglyMeasurable (fun t => coeff' t n)
        (volume.restrict (Set.Icc a b)) := by
    intro n hn
    dsimp only [coeff']
    exact (stronglyMeasurable_deriv
      (fun y => coeff y n)).aestronglyMeasurable.restrict
  have henergy' : ∀ t ∈ Set.Icc a b,
      (∑ n ∈ s, Complex.normSq (coeff t n)) ≤ E := by
    intro t ht
    calc
      (∑ n ∈ s, Complex.normSq (coeff t n)) =
          ∑ n ∈ s, Complex.normSq
            (hardyPhaseLinearizedCoeff n delta t) := by
        apply Finset.sum_congr rfl
        intro n hn
        dsimp only [coeff]
        rw [Complex.normSq_conj]
        exact normSq_hardyPhaseWindowCoeff_eq_linearizedCoeff
          (Nat.pos_of_ne_zero (hpositive n hn)) (htpos t ht)
      _ ≤ E := henergy t ht
  have hderivEnergy' : ∀ t ∈ Set.Icc a b,
      (∑ n ∈ s, Complex.normSq (coeff' t n)) ≤ D := by
    intro t ht
    calc
      (∑ n ∈ s, Complex.normSq (coeff' t n)) =
          ∑ n ∈ s, Complex.normSq
            (deriv (hardyPhaseWindowCoeff n delta) t) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hd := hasDerivAt_hardyPhaseWindowCoeff
          (delta := delta) n (htpos t ht)
        have hstar := hd.star
        dsimp only [coeff', coeff]
        change Complex.normSq
            (deriv (fun y => star (hardyPhaseWindowCoeff n delta y)) t) =
          Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)
        rw [hstar.deriv, hd.deriv]
        simp only [Complex.normSq_eq_norm_sq, norm_star]
      _ ≤ D := hderivEnergy t ht
  have hpoly :=
    MathlibAux.integral_normSq_timeDependentLogPolynomial_le_of_measurable
      hN s coeff coeff' hpositive hupper hab hq hderiv hcoeffCont
        hcoeffPrimeMeas henergy' hderivEnergy'
  calc
    (∫ t in a..b,
        Complex.normSq (hardyPhaseLinearizedPartialSum s delta t)) =
        ∫ t in a..b,
          Complex.normSq (MathlibAux.timeDependentLogPolynomial s coeff t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact normSq_hardyPhaseLinearizedPartialSum_eq_logPolynomial
        s (htpos t ht) hpositive
    _ ≤ (b - a) * E +
        4 * (5 * Real.pi + 4) * N * E +
        |b - a| *
          (2 * (5 * Real.pi + 4) * N *
            (q ^ 2 * D + (q ^ 2)⁻¹ * E)) := hpoly

end HardyTheorem
