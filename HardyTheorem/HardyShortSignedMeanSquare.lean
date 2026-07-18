import HardyTheorem.HardyModelApproximation
import HardyTheorem.ShortIntervalMeanValue
import MathlibAux.DirichletPolynomialMeanSquare

open Complex MeasureTheory Set

namespace MathlibAux

/-- The coefficient acquired by one exponential mode after integration over a
sliding window of length `delta`. -/
noncomputable def shortExponentialCoefficient {ι : Type*}
    (delta : ℝ) (coeff : ι → ℂ) (freq : ι → ℝ) (n : ι) : ℂ :=
  coeff n * ∫ v in 0..delta, Complex.exp (I * (freq n * v))

/-- A sliding integral of a finite linear exponential polynomial is another
exponential polynomial, with the exact short-window coefficients. -/
theorem intervalIntegral_exponentialPolynomial_eq_exponentialPolynomial
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    (delta t : ℝ) :
    (∫ u in t..t + delta, exponentialPolynomial s coeff freq u) =
      exponentialPolynomial s
        (shortExponentialCoefficient delta coeff freq) freq t := by
  rw [show (fun u : ℝ => exponentialPolynomial s coeff freq u) =
      fun u : ℝ => ∑ n ∈ s,
        coeff n * Complex.exp (I * (freq n * u)) by
    rfl]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro n hn
    calc
      (∫ u in t..t + delta,
          coeff n * Complex.exp (I * (freq n * u))) =
          ∫ v in 0..delta,
            coeff n * Complex.exp
              (I * ((freq n : ℂ) * ((v + t : ℝ) : ℂ))) := by
        have hshift := intervalIntegral.integral_comp_add_right
          (fun u : ℝ => coeff n * Complex.exp (I * (freq n * u))) t
          (a := 0) (b := delta)
        simpa only [zero_add, add_comm delta t] using hshift.symm
      _ = ∫ v in 0..delta,
          (coeff n * Complex.exp (I * (freq n * v))) *
            Complex.exp (I * (freq n * t)) := by
        apply intervalIntegral.integral_congr
        intro v hv
        change coeff n * Complex.exp
            (I * ((freq n : ℂ) * ((v + t : ℝ) : ℂ))) =
          (coeff n * Complex.exp (I * (freq n * v))) *
            Complex.exp (I * (freq n * t))
        push_cast
        rw [mul_assoc, ← Complex.exp_add]
        congr 1
        ring
      _ = (∫ v in 0..delta,
          coeff n * Complex.exp (I * (freq n * v))) *
            Complex.exp (I * (freq n * t)) :=
        intervalIntegral.integral_mul_const _ _
      _ = shortExponentialCoefficient delta coeff freq n *
            Complex.exp (I * (freq n * t)) := by
        rw [shortExponentialCoefficient]
        congr 1
        exact intervalIntegral.integral_const_mul _ _
  · intro n hn
    apply Continuous.intervalIntegrable
    fun_prop

/-- The standard diagonal plus frequency-gap estimate for the second moment
of sliding integrals of a finite linear exponential polynomial. The exact
window coefficients retain all cancellation inside the short integral. -/
theorem integral_normSq_intervalIntegral_exponentialPolynomial_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    {a b delta : ℝ}
    (hfreq : ∀ m ∈ s, ∀ n ∈ s, m ≠ n → freq m ≠ freq n) :
    (∫ t in a..b,
        Complex.normSq
          (∫ u in t..t + delta, exponentialPolynomial s coeff freq u)) ≤
      ∑ m ∈ s, ∑ n ∈ s,
        if m = n then
          (b - a) * Complex.normSq
            (shortExponentialCoefficient delta coeff freq n)
        else
          2 * ‖shortExponentialCoefficient delta coeff freq m‖ *
              ‖shortExponentialCoefficient delta coeff freq n‖ /
            |freq m - freq n| := by
  rw [show (fun t : ℝ =>
      Complex.normSq
        (∫ u in t..t + delta, exponentialPolynomial s coeff freq u)) =
      fun t : ℝ => Complex.normSq
        (exponentialPolynomial s
          (shortExponentialCoefficient delta coeff freq) freq t) by
    funext t
    rw [intervalIntegral_exponentialPolynomial_eq_exponentialPolynomial]]
  exact integral_normSq_exponentialPolynomial_le s
    (shortExponentialCoefficient delta coeff freq) freq hfreq

end MathlibAux

namespace HardyTheorem

/-- The real elementary-phase first-approximation model, expressed directly
as a finite sum of Hardy oscillatory phases. -/
noncomputable def hardyFirstModel (kappa T t : ℝ) : ℝ :=
  (Complex.exp (I * kappa) *
    (∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
      ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
        Complex.exp (I * OscillatoryIntegral.hardyPhase n t))).re

/-- The signed sliding integral of the elementary-phase first model. -/
noncomputable def hardyFirstModelShortIntegral
    (kappa T delta t : ℝ) : ℝ :=
  ∫ u in t..t + delta, hardyFirstModel kappa T u

private theorem hardyFirstModel_eq_re_thetaModel_dirichletPolynomial
    (kappa T : ℝ) {t : ℝ} (ht : 0 < t) :
    hardyFirstModel kappa T t =
      (Complex.exp (I * kappa) * Complex.exp (I * thetaModel t) *
        (∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
          1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))).re := by
  have hsum :
      Complex.exp (I * thetaModel t) *
          (∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
            1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) =
        ∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
          ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
            Complex.exp (I * OscillatoryIntegral.hardyPhase n t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hnmem
    have hn : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hnmem).1
      omega
    exact exp_I_thetaModel_mul_inv_nat_cpow_criticalLine_eq hn ht
  dsimp only [hardyFirstModel]
  rw [← hsum]
  ring_nf

private theorem continuousAt_hardyFirstModel
    (kappa T : ℝ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (hardyFirstModel kappa T) t := by
  unfold hardyFirstModel
  apply Complex.continuous_re.continuousAt.comp
  apply ContinuousAt.mul continuousAt_const
  apply tendsto_finset_sum
  intro n hnmem
  have hn : n ≠ 0 := by
    have := (Finset.mem_Icc.mp hnmem).1
    omega
  apply ContinuousAt.mul continuousAt_const
  exact (continuousAt_const.mul
    (Complex.continuous_ofReal.continuousAt.comp
      (OscillatoryIntegral.contDiffAt_hardyPhase_two hn ht).continuousAt)).cexp

/-- On an interior sliding interval, the true signed Hardy integral differs
from the unconditional first rotated model by the integrated pointwise
`O(T^(-1/2))` approximation error. -/
theorem exists_abs_hardyShortIntegral_sub_hardyFirstModelShortIntegral_le :
    ∃ kappa C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ T delta t : ℝ, T0 ≤ T → 0 ≤ delta →
        t ∈ Icc T (2 * T - delta) →
          |hardyShortIntegral delta t -
              hardyFirstModelShortIntegral kappa T delta t| ≤
            C * delta / Real.sqrt T := by
  obtain ⟨kappa, C, T0, hC, hT0, happrox⟩ :=
    exists_norm_rotated_riemannZeta_sub_thetaModel_dirichletPolynomial_le_inv_sqrt
  refine ⟨kappa, C, T0, hC, hT0, ?_⟩
  intro T delta t hT hdelta ht
  have hT1 : 1 ≤ T := hT0.trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have htpos : 0 < t := hTpos.trans_le ht.1
  have htle : t ≤ t + delta := by linarith
  have hhardyInt : IntervalIntegrable hardyZ volume t (t + delta) :=
    hardyZ_continuous.intervalIntegrable _ _
  have hmodelInt :
      IntervalIntegrable (hardyFirstModel kappa T) volume t (t + delta) := by
    apply ContinuousOn.intervalIntegrable_of_Icc htle
    intro u hu
    exact (continuousAt_hardyFirstModel kappa T
      (htpos.trans_le hu.1)).continuousWithinAt
  have hpoint : ∀ u ∈ Icc t (t + delta),
      |hardyZ u - hardyFirstModel kappa T u| ≤ C / Real.sqrt T := by
    intro u hu
    have huDyadic : u ∈ Icc T (2 * T) := by
      constructor
      · exact ht.1.trans hu.1
      · linarith [hu.2, ht.2]
    have huPos : 0 < u := hTpos.trans_le huDyadic.1
    have happ := happrox T u hT huDyadic
    rw [hardyZ_eq_re_exp_I_thetaPhase_mul_zeta,
      hardyFirstModel_eq_re_thetaModel_dirichletPolynomial kappa T huPos]
    rw [← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans happ
  have hdiff :
      hardyShortIntegral delta t -
          hardyFirstModelShortIntegral kappa T delta t =
        ∫ u in t..t + delta,
          (hardyZ u - hardyFirstModel kappa T u) := by
    dsimp only [hardyShortIntegral, hardyFirstModelShortIntegral]
    rw [intervalIntegral.integral_sub hhardyInt hmodelInt]
  rw [hdiff]
  change ‖∫ u in t..t + delta,
      (hardyZ u - hardyFirstModel kappa T u)‖ ≤
    C * delta / Real.sqrt T
  calc
    ‖∫ u in t..t + delta,
        (hardyZ u - hardyFirstModel kappa T u)‖ ≤
        (C / Real.sqrt T) * |t + delta - t| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro u hu
      have hu' := Set.uIoc_subset_uIcc hu
      rw [Set.uIcc_of_le htle] at hu'
      simpa only [Real.norm_eq_abs] using hpoint u hu'
    _ = C * delta / Real.sqrt T := by
      rw [show t + delta - t = delta by ring, abs_of_nonneg hdelta]
      ring

end HardyTheorem
