import MathlibAux.TimeDependentLogHilbert
import Mathlib.Analysis.Calculus.FDeriv.Measurable

open Complex MeasureTheory Set
open scoped BigOperators

namespace MathlibAux

/-- A finite logarithmic polynomial inherits continuity on an interval from
its time-dependent coefficients. -/
theorem continuousOn_timeDependentLogPolynomial
    (s : Finset ℕ) (coeff : ℝ → ℕ → ℂ) {a b : ℝ}
    (hcoeffCont : ∀ n ∈ s,
      ContinuousOn (fun t ↦ coeff t n) (Set.Icc a b)) :
    ContinuousOn (timeDependentLogPolynomial s coeff) (Set.Icc a b) := by
  intro t ht
  unfold timeDependentLogPolynomial timeLogTwist
  apply tendsto_finset_sum
  intro n hn
  exact (hcoeffCont n hn t ht).mul (by fun_prop)

/-- The time-dependent logarithmic Hilbert integration-by-parts estimate
with both integrability hypotheses discharged from continuity of the moving
coefficients, measurability of their derivatives, and the same uniform
energy bounds that occur in the estimate. -/
theorem norm_integral_timeDependentLogOffDiagonal_le_of_measurable
    {N : ℕ} (hN : 0 < N) (s : Finset ℕ)
    (coeff coeff' : ℝ → ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0) (hupper : ∀ n ∈ s, n ≤ N)
    {a b q E D : ℝ} (hab : a ≤ b) (hq : 0 < q)
    (hderiv : ∀ t ∈ Set.Icc a b, ∀ n ∈ s,
      HasDerivAt (fun x ↦ coeff x n) (coeff' t n) t)
    (hcoeffCont : ∀ n ∈ s,
      ContinuousOn (fun t ↦ coeff t n) (Set.Icc a b))
    (hcoeffPrimeMeas : ∀ n ∈ s,
      AEStronglyMeasurable (fun t ↦ coeff' t n)
        (volume.restrict (Set.Icc a b)))
    (henergy : ∀ t ∈ Set.Icc a b,
      (∑ n ∈ s, Complex.normSq (coeff t n)) ≤ E)
    (hderivEnergy : ∀ t ∈ Set.Icc a b,
      (∑ n ∈ s, Complex.normSq (coeff' t n)) ≤ D) :
    ‖∫ t in a..b, logOffDiagonalForm s (coeff t) (coeff t) t‖ ≤
      4 * (5 * Real.pi + 4) * N * E +
        |b - a| *
          (2 * (5 * Real.pi + 4) * N *
            (q ^ 2 * D + (q ^ 2)⁻¹ * E)) := by
  let F : ℝ → ℂ := fun t ↦ logOffDiagonalForm s (coeff t) (coeff t) t
  let V : ℝ → ℂ := timeDependentLogHilbertVariation s coeff coeff'
  have hFcont : ContinuousOn F (Set.Icc a b) := by
    intro t ht
    dsimp only [F]
    unfold logOffDiagonalForm
    apply tendsto_finset_sum
    intro m hm
    apply tendsto_finset_sum
    intro n hn
    unfold logOffDiagonalTerm
    by_cases hmn : m = n
    · subst n
      simpa using (continuousWithinAt_const :
        ContinuousWithinAt (fun _x : ℝ ↦ (0 : ℂ)) (Set.Icc a b) t)
    · simp only [hmn, if_false]
      have hncont := hcoeffCont n hn t ht
      have hmcont := hcoeffCont m hm t ht
      have hexp : ContinuousWithinAt
          (fun x : ℝ ↦
            Complex.exp (I * ((Real.log m - Real.log n) * x)))
          (Set.Icc a b) t := by
        fun_prop
      exact (hncont.star.mul hmcont).mul hexp
  have hoffInt : IntervalIntegrable F volume a b :=
    hFcont.intervalIntegrable_of_Icc hab
  have hcoeffMeas : ∀ n ∈ s,
      AEStronglyMeasurable (fun t ↦ coeff t n)
        (volume.restrict (Set.Icc a b)) := by
    intro n hn
    exact (hcoeffCont n hn).aestronglyMeasurable measurableSet_Icc
  have hVmeas : AEStronglyMeasurable V
      (volume.restrict (Set.Icc a b)) := by
    dsimp only [V]
    unfold timeDependentLogHilbertVariation
    apply s.aestronglyMeasurable_fun_sum
    intro m hm
    apply s.aestronglyMeasurable_fun_sum
    intro n hn
    by_cases hmn : m = n
    · subst n
      simp only [if_pos]
      exact aestronglyMeasurable_const
    · simp only [hmn, if_false]
      have hnmeas := hcoeffMeas n hn
      have hmmeas := hcoeffMeas m hm
      have hnpmeas := hcoeffPrimeMeas n hn
      have hmpmeas := hcoeffPrimeMeas m hm
      have hexp : AEStronglyMeasurable
          (fun x : ℝ ↦
            Complex.exp (I *
              (((Real.log m - Real.log n) * x : ℝ) : ℂ)))
          (volume.restrict (Set.Icc a b)) := by
        exact (by fun_prop : Continuous fun x : ℝ ↦
          Complex.exp (I *
            (((Real.log m - Real.log n) * x : ℝ) : ℂ))).aestronglyMeasurable.restrict
      have hamp := (hnpmeas.star.mul hmmeas).add
        (hnmeas.star.mul hmpmeas)
      have hscaled := hamp.mul_const
        (((1 / (Real.log (m : ℝ) - Real.log (n : ℝ)) : ℝ) : ℂ))
      exact hscaled.mul hexp
  have haMem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hE : 0 ≤ E := by
    exact (Finset.sum_nonneg fun n _ ↦ Complex.normSq_nonneg _).trans
      (henergy a haMem)
  have hD : 0 ≤ D := by
    exact (Finset.sum_nonneg fun n _ ↦ Complex.normSq_nonneg _).trans
      (hderivEnergy a haMem)
  let B : ℝ := 2 * (5 * Real.pi + 4) * N *
    (q ^ 2 * D + (q ^ 2)⁻¹ * E)
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hVbound : ∀ t ∈ Set.Icc a b, ‖V t‖ ≤ B := by
    intro t ht
    dsimp only [V, B]
    exact norm_timeDependentLogHilbertVariation_le
      hN s coeff coeff' hpositive hupper hq
        (henergy t ht) (hderivEnergy t ht)
  have hBint : IntegrableOn (fun _t : ℝ ↦ B) (Set.Icc a b) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hVintOn : IntegrableOn V (Set.Icc a b) := by
    change Integrable V (volume.restrict (Set.Icc a b))
    change Integrable (fun _t : ℝ ↦ B)
      (volume.restrict (Set.Icc a b)) at hBint
    apply hBint.mono' hVmeas
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hVbound t ht
  have hvarInt : IntervalIntegrable V volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hVintOn
  exact norm_integral_timeDependentLogOffDiagonal_le
    hN s coeff coeff' hpositive hupper hab hq
      (by
        intro t ht
        rw [Set.uIcc_of_le hab] at ht
        exact hderiv t ht)
      (by simpa only [F] using hoffInt)
      (by simpa only [V] using hvarInt)
      (by
        intro t ht
        rw [Set.uIcc_of_le hab] at ht
        exact henergy t ht)
      (by
        intro t ht
        rw [Set.uIcc_of_le hab] at ht
        exact hderivEnergy t ht)

/-- A uniform coefficient-energy bound and a uniform derivative-energy
bound control the full second moment of a logarithmic polynomial with moving
coefficients.  The first term is the diagonal contribution; the remaining
terms are the endpoint and variation costs from Hilbert integration by
parts. -/
theorem integral_normSq_timeDependentLogPolynomial_le_of_measurable
    {N : ℕ} (hN : 0 < N) (s : Finset ℕ)
    (coeff coeff' : ℝ → ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0) (hupper : ∀ n ∈ s, n ≤ N)
    {a b q E D : ℝ} (hab : a ≤ b) (hq : 0 < q)
    (hderiv : ∀ t ∈ Set.Icc a b, ∀ n ∈ s,
      HasDerivAt (fun x ↦ coeff x n) (coeff' t n) t)
    (hcoeffCont : ∀ n ∈ s,
      ContinuousOn (fun t ↦ coeff t n) (Set.Icc a b))
    (hcoeffPrimeMeas : ∀ n ∈ s,
      AEStronglyMeasurable (fun t ↦ coeff' t n)
        (volume.restrict (Set.Icc a b)))
    (henergy : ∀ t ∈ Set.Icc a b,
      (∑ n ∈ s, Complex.normSq (coeff t n)) ≤ E)
    (hderivEnergy : ∀ t ∈ Set.Icc a b,
      (∑ n ∈ s, Complex.normSq (coeff' t n)) ≤ D) :
    (∫ t in a..b,
      Complex.normSq (timeDependentLogPolynomial s coeff t)) ≤
      (b - a) * E +
        4 * (5 * Real.pi + 4) * N * E +
        |b - a| *
          (2 * (5 * Real.pi + 4) * N *
            (q ^ 2 * D + (q ^ 2)⁻¹ * E)) := by
  let P : ℝ → ℂ := timeDependentLogPolynomial s coeff
  let A : ℝ → ℝ := fun t ↦
    ∑ n ∈ s, Complex.normSq (coeff t n)
  let F : ℝ → ℂ := fun t ↦
    logOffDiagonalForm s (coeff t) (coeff t) t
  have hPcont : ContinuousOn P (Set.Icc a b) := by
    simpa only [P] using continuousOn_timeDependentLogPolynomial
      s coeff hcoeffCont
  have hAcont : ContinuousOn A (Set.Icc a b) := by
    intro t ht
    dsimp only [A]
    apply tendsto_finset_sum
    intro n hn
    exact Complex.continuous_normSq.continuousAt.comp_continuousWithinAt
      (hcoeffCont n hn t ht)
  have hFcont : ContinuousOn F (Set.Icc a b) := by
    intro t ht
    dsimp only [F]
    unfold logOffDiagonalForm
    apply tendsto_finset_sum
    intro m hm
    apply tendsto_finset_sum
    intro n hn
    unfold logOffDiagonalTerm
    by_cases hmn : m = n
    · subst n
      simpa using (continuousWithinAt_const :
        ContinuousWithinAt (fun _x : ℝ ↦ (0 : ℂ)) (Set.Icc a b) t)
    · simp only [hmn, if_false]
      have hncont := hcoeffCont n hn t ht
      have hmcont := hcoeffCont m hm t ht
      have hexp : ContinuousWithinAt
          (fun x : ℝ ↦
            Complex.exp (I * ((Real.log m - Real.log n) * x)))
          (Set.Icc a b) t := by
        fun_prop
      exact (hncont.star.mul hmcont).mul hexp
  have hPint : IntervalIntegrable (fun t ↦ Complex.normSq (P t))
      volume a b :=
    (Complex.continuous_normSq.comp_continuousOn hPcont).intervalIntegrable_of_Icc hab
  have hAint : IntervalIntegrable A volume a b :=
    hAcont.intervalIntegrable_of_Icc hab
  have hFint : IntervalIntegrable F volume a b :=
    hFcont.intervalIntegrable_of_Icc hab
  have hFreInt : IntervalIntegrable (fun t ↦ (F t).re) volume a b :=
    (Complex.continuous_re.comp_continuousOn hFcont).intervalIntegrable_of_Icc hab
  have hpoint : ∀ t,
      Complex.normSq (P t) = A t + (F t).re := by
    intro t
    exact normSq_timeDependentLogPolynomial_eq s coeff t
  have hsplit :
      (∫ t in a..b, Complex.normSq (P t)) =
        (∫ t in a..b, A t) + ∫ t in a..b, (F t).re := by
    calc
      (∫ t in a..b, Complex.normSq (P t)) =
          ∫ t in a..b, A t + (F t).re := by
        apply intervalIntegral.integral_congr
        intro t _ht
        exact hpoint t
      _ = (∫ t in a..b, A t) + ∫ t in a..b, (F t).re :=
        intervalIntegral.integral_add hAint hFreInt
  have hconstInt : IntervalIntegrable (fun _t : ℝ ↦ E) volume a b :=
    continuous_const.intervalIntegrable _ _
  have hAdiag : (∫ t in a..b, A t) ≤ (b - a) * E := by
    calc
      (∫ t in a..b, A t) ≤ ∫ _t in a..b, E := by
        apply intervalIntegral.integral_mono_on hab hAint hconstInt
        intro t ht
        exact henergy t ht
      _ = (b - a) * E := by
        simp only [intervalIntegral.integral_const, smul_eq_mul]
  have hre :
      (∫ t in a..b, (F t).re) = (∫ t in a..b, F t).re := by
    simpa using Complex.reCLM.intervalIntegral_comp_comm hFint
  have hFre : (∫ t in a..b, (F t).re) ≤ ‖∫ t in a..b, F t‖ := by
    rw [hre]
    exact Complex.re_le_norm _
  have hOff := norm_integral_timeDependentLogOffDiagonal_le_of_measurable
    hN s coeff coeff' hpositive hupper hab hq hderiv hcoeffCont
      hcoeffPrimeMeas henergy hderivEnergy
  rw [hsplit]
  calc
    (∫ t in a..b, A t) + ∫ t in a..b, (F t).re ≤
        (b - a) * E + ‖∫ t in a..b, F t‖ :=
      add_le_add hAdiag hFre
    _ ≤ (b - a) * E +
        (4 * (5 * Real.pi + 4) * N * E +
          |b - a| *
            (2 * (5 * Real.pi + 4) * N *
              (q ^ 2 * D + (q ^ 2)⁻¹ * E))) :=
      by
        simpa [add_comm] using add_le_add_right hOff ((b - a) * E)
    _ = (b - a) * E +
        4 * (5 * Real.pi + 4) * N * E +
        |b - a| *
          (2 * (5 * Real.pi + 4) * N *
            (q ^ 2 * D + (q ^ 2)⁻¹ * E)) := by ring

end MathlibAux
