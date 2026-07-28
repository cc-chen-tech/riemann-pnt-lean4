import PrimeNumberTheorem.VKEdgeExplicitFormulaPairBridge
import PrimeNumberTheorem.ZeroForcedOscillation
import PrimeNumberTheorem.ZeroForcedOscillationExplicitFormula

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Averaging the target-pair annihilator step

The symmetric detector tuned to `gamma` kills the selected frequency exactly.
A fixed step can accidentally kill another frequency as well. This module
proves that averaging over the step removes that collision for every fixed
distinct positive frequency.

The final theorem is purely finite-spectral: a nonzero finite residual
frequency package admits a step and a finite logarithmic interval on which
the annihilated package has strictly positive second moment. Identifying and
estimating the complete zeta explicit-formula residual remains a separate
analytic task.
-/

/-- The scalar by which the target-pair annihilator multiplies a cosine or
complex exponential of frequency `lambda`. -/
def frequencyAnnihilatorMultiplier
    (gamma lambda h : ℝ) : ℝ :=
  2 * (Real.cos (lambda * h) - Real.cos (gamma * h))

/-- The selected frequency is annihilated for every step. -/
theorem frequencyAnnihilatorMultiplier_target
    (gamma h : ℝ) :
    frequencyAnnihilatorMultiplier gamma gamma h = 0 := by
  simp [frequencyAnnihilatorMultiplier]

/-- Exact finite-interval mean square of the annihilator multiplier. -/
theorem intervalIntegral_frequencyAnnihilatorMultiplier_sq
    {gamma lambda H : ℝ}
    (hgamma : gamma ≠ 0) (hlambda : lambda ≠ 0)
    (hne : lambda ≠ gamma) (hneg : lambda ≠ -gamma) :
    (∫ h in (0 : ℝ)..H,
        frequencyAnnihilatorMultiplier gamma lambda h ^ 2) =
      4 * H +
        Real.sin (2 * lambda * H) / lambda +
        Real.sin (2 * gamma * H) / gamma -
        4 * Real.sin ((lambda - gamma) * H) / (lambda - gamma) -
        4 * Real.sin ((lambda + gamma) * H) / (lambda + gamma) := by
  let primitive : ℝ → ℝ := fun h =>
    4 * h +
      Real.sin (2 * lambda * h) / lambda +
      Real.sin (2 * gamma * h) / gamma -
      4 * Real.sin ((lambda - gamma) * h) / (lambda - gamma) -
      4 * Real.sin ((lambda + gamma) * h) / (lambda + gamma)
  have hsub : lambda - gamma ≠ 0 := sub_ne_zero.mpr hne
  have hadd : lambda + gamma ≠ 0 := by
    intro hzero
    apply hneg
    linarith
  have hderiv (h : ℝ) :
      HasDerivAt primitive
        (frequencyAnnihilatorMultiplier gamma lambda h ^ 2) h := by
    have hmain : HasDerivAt (fun x : ℝ => 4 * x) 4 h := by
      convert (hasDerivAt_id h).const_mul 4 using 1 <;> ring
    have hlambdaDeriv :
        HasDerivAt
          (fun x : ℝ => Real.sin (2 * lambda * x) / lambda)
          (2 * Real.cos (2 * lambda * h)) h := by
      convert
        (((Real.hasDerivAt_sin (2 * lambda * h)).comp h
          ((hasDerivAt_const h (2 * lambda)).mul
            (hasDerivAt_id h))).div_const lambda) using 1 <;>
        field_simp [hlambda] <;>
        ring
    have hgammaDeriv :
        HasDerivAt
          (fun x : ℝ => Real.sin (2 * gamma * x) / gamma)
          (2 * Real.cos (2 * gamma * h)) h := by
      convert
        (((Real.hasDerivAt_sin (2 * gamma * h)).comp h
          ((hasDerivAt_const h (2 * gamma)).mul
            (hasDerivAt_id h))).div_const gamma) using 1 <;>
        field_simp [hgamma] <;>
        ring
    have hsubDeriv :
        HasDerivAt
          (fun x : ℝ =>
            4 * Real.sin ((lambda - gamma) * x) / (lambda - gamma))
          (4 * Real.cos ((lambda - gamma) * h)) h := by
      convert
        ((((Real.hasDerivAt_sin ((lambda - gamma) * h)).comp h
          ((hasDerivAt_const h (lambda - gamma)).mul
            (hasDerivAt_id h))).const_mul 4).div_const
              (lambda - gamma)) using 1 <;>
        field_simp [hsub] <;>
        ring
    have haddDeriv :
        HasDerivAt
          (fun x : ℝ =>
            4 * Real.sin ((lambda + gamma) * x) / (lambda + gamma))
          (4 * Real.cos ((lambda + gamma) * h)) h := by
      convert
        ((((Real.hasDerivAt_sin ((lambda + gamma) * h)).comp h
          ((hasDerivAt_const h (lambda + gamma)).mul
            (hasDerivAt_id h))).const_mul 4).div_const
              (lambda + gamma)) using 1 <;>
        field_simp [hadd] <;>
        ring
    have hcombined :=
      (((hmain.add hlambdaDeriv).add hgammaDeriv).sub hsubDeriv).sub
        haddDeriv
    convert hcombined using 1
    unfold frequencyAnnihilatorMultiplier
    rw [show
        (2 *
            (Real.cos (lambda * h) -
              Real.cos (gamma * h))) ^ 2 =
          4 * Real.cos (lambda * h) ^ 2 +
            4 * Real.cos (gamma * h) ^ 2 -
            8 * Real.cos (lambda * h) *
              Real.cos (gamma * h) by ring]
    rw [Real.cos_sq, Real.cos_sq]
    have hproduct :=
      Real.two_mul_cos_mul_cos (lambda * h) (gamma * h)
    rw [show
        8 * Real.cos (lambda * h) *
            Real.cos (gamma * h) =
          4 *
            (Real.cos (lambda * h - gamma * h) +
              Real.cos (lambda * h + gamma * h)) by
        nlinarith]
    ring_nf
  have hint :
      IntervalIntegrable
        (fun h => frequencyAnnihilatorMultiplier gamma lambda h ^ 2)
        volume 0 H := by
    apply Continuous.intervalIntegrable
    unfold frequencyAnnihilatorMultiplier
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun h _hh => hderiv h) hint]
  dsimp [primitive]
  simp

/-- The multiplier energy per unit step length. -/
def normalizedStepMultiplierEnergy
    (gamma lambda H : ℝ) : ℝ :=
  H⁻¹ * ∫ h in (0 : ℝ)..H,
    frequencyAnnihilatorMultiplier gamma lambda h ^ 2

private theorem tendsto_sin_mul_div_atTop
    {c d : ℝ} (hd : d ≠ 0) :
    Tendsto (fun H : ℝ => Real.sin (c * H) / (d * H))
      atTop (𝓝 0) := by
  have hsinBound :
      IsBoundedUnder (· ≤ ·) atTop
        (norm ∘ fun H : ℝ => Real.sin (c * H)) := by
    apply isBoundedUnder_of_eventually_le
      (a := (1 : ℝ))
    exact Eventually.of_forall fun H => by
      simpa [Function.comp_apply, Real.norm_eq_abs] using
        Real.abs_sin_le_one (c * H)
  have hzero :
      Tendsto
        (fun H : ℝ => Real.sin (c * H) * H⁻¹)
        atTop (𝓝 0) :=
    Filter.isBoundedUnder_le_mul_tendsto_zero
      hsinBound tendsto_inv_atTop_zero
  convert hzero.const_mul d⁻¹ using 1
  · funext H
    field_simp [hd]
  · simp

/-- Averaging over the step removes a collision with every fixed distinct
positive frequency. -/
theorem tendsto_normalizedStepMultiplierEnergy
    {gamma lambda : ℝ}
    (hgamma : 0 < gamma) (hlambda : 0 < lambda)
    (hne : lambda ≠ gamma) :
    Tendsto (normalizedStepMultiplierEnergy gamma lambda)
      atTop (𝓝 4) := by
  have hsub : lambda - gamma ≠ 0 := sub_ne_zero.mpr hne
  have hadd : lambda + gamma ≠ 0 := by positivity
  have hlambdaTerm :
      Tendsto
        (fun H : ℝ => Real.sin (2 * lambda * H) / (lambda * H))
        atTop (𝓝 0) :=
    tendsto_sin_mul_div_atTop hlambda.ne'
  have hgammaTerm :
      Tendsto
        (fun H : ℝ => Real.sin (2 * gamma * H) / (gamma * H))
        atTop (𝓝 0) :=
    tendsto_sin_mul_div_atTop hgamma.ne'
  have hsubTerm :
      Tendsto
        (fun H : ℝ =>
          Real.sin ((lambda - gamma) * H) /
            ((lambda - gamma) * H))
        atTop (𝓝 0) :=
    tendsto_sin_mul_div_atTop hsub
  have haddTerm :
      Tendsto
        (fun H : ℝ =>
          Real.sin ((lambda + gamma) * H) /
            ((lambda + gamma) * H))
        atTop (𝓝 0) :=
    tendsto_sin_mul_div_atTop hadd
  have hformula :
      ∀ᶠ H : ℝ in atTop,
        normalizedStepMultiplierEnergy gamma lambda H =
          4 +
            Real.sin (2 * lambda * H) / (lambda * H) +
            Real.sin (2 * gamma * H) / (gamma * H) -
            4 *
              (Real.sin ((lambda - gamma) * H) /
                ((lambda - gamma) * H)) -
            4 *
              (Real.sin ((lambda + gamma) * H) /
                ((lambda + gamma) * H)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
    rw [normalizedStepMultiplierEnergy,
      intervalIntegral_frequencyAnnihilatorMultiplier_sq
        hgamma.ne' hlambda.ne' hne (by
          intro heq
          nlinarith)]
    field_simp [hH.ne', hgamma.ne', hlambda.ne', hsub, hadd]
  have hlimit :
      Tendsto
        (fun H : ℝ =>
          4 +
            Real.sin (2 * lambda * H) / (lambda * H) +
            Real.sin (2 * gamma * H) / (gamma * H) -
            4 *
              (Real.sin ((lambda - gamma) * H) /
                ((lambda - gamma) * H)) -
            4 *
              (Real.sin ((lambda + gamma) * H) /
                ((lambda + gamma) * H)))
        atTop (𝓝 4) := by
    convert
      (((tendsto_const_nhds.add hlambdaTerm).add hgammaTerm).sub
        (tendsto_const_nhds.mul hsubTerm)).sub
          (tendsto_const_nhds.mul haddTerm) using 1 <;>
      norm_num
  exact hlimit.congr'
    (hformula.mono fun _H hH => hH.symm)

/-- Every fixed non-target positive frequency eventually contributes at least
`2` units of normalized step energy. -/
theorem eventually_two_le_normalizedStepMultiplierEnergy
    {gamma lambda : ℝ}
    (hgamma : 0 < gamma) (hlambda : 0 < lambda)
    (hne : lambda ≠ gamma) :
    ∀ᶠ H in atTop,
      2 ≤ normalizedStepMultiplierEnergy gamma lambda H := by
  have hmem : Set.Ioi (2 : ℝ) ∈ 𝓝 4 :=
    Ioi_mem_nhds (by norm_num)
  filter_upwards [
    (tendsto_normalizedStepMultiplierEnergy hgamma hlambda hne)
      hmem] with H hH
  exact hH.le

/-- The finite exponential polynomial after applying the target-frequency
annihilator coefficientwise. -/
def annihilatedExponentialPolynomial
    {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (omega : ι → ℝ) (gamma h y : ℝ) : ℂ :=
  PrimeNumberTheorem.ZeroForcedOscillation.exponentialPolynomial S
    (fun i =>
      (frequencyAnnihilatorMultiplier gamma (omega i) h : ℂ) * c i)
    omega y

private theorem offDiagonalBound_nonneg
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (omega : ι → ℝ) :
    0 ≤ PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound
      S c omega := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact div_nonneg (by positivity) (abs_nonneg _)

/-- A nonzero finite residual frequency package admits a detector step and a
finite logarithmic interval with strictly positive second moment.

This theorem only concerns the supplied finite spectral package. It neither
asserts that zeta has another zero nor controls the infinite explicit-formula
tail. -/
theorem exists_step_intervalIntegral_annihilatedExponentialPolynomial_pos
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (omega : ι → ℝ)
    {gamma : ℝ}
    (hgamma : 0 < gamma)
    (homega : ∀ i ∈ S, 0 < omega i)
    (hne : ∀ i ∈ S, omega i ≠ gamma)
    (hinj : Set.InjOn omega ↑S)
    (hcoeff : 0 < ∑ i ∈ S, ‖c i‖ ^ 2) :
    ∃ h L : ℝ,
      0 < L ∧
        0 < ∫ y in (0 : ℝ)..L,
          ‖annihilatedExponentialPolynomial
            S c omega gamma h y‖ ^ 2 := by
  have hexistsCoefficient :
      ∃ i ∈ S, 0 < ‖c i‖ ^ 2 := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ i ∈ S, ‖c i‖ ^ 2 = 0 := by
      intro i hi
      exact le_antisymm (hnone i hi) (sq_nonneg ‖c i‖)
    have : (∑ i ∈ S, ‖c i‖ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hzero i hi
    linarith
  obtain ⟨i, hi, hci⟩ := hexistsCoefficient
  have hstepEventually :=
    eventually_two_le_normalizedStepMultiplierEnergy
      hgamma (homega i hi) (hne i hi)
  obtain ⟨H, hH, hstep⟩ :
      ∃ H : ℝ, 0 < H ∧
        2 ≤ normalizedStepMultiplierEnergy gamma (omega i) H := by
    exact ((eventually_gt_atTop (0 : ℝ)).and hstepEventually).exists
  have hmultiplierIntegral :
      0 < ∫ h in (0 : ℝ)..H,
        frequencyAnnihilatorMultiplier gamma (omega i) h ^ 2 := by
    rw [normalizedStepMultiplierEnergy] at hstep
    have hinv : 0 < H⁻¹ := inv_pos.mpr hH
    nlinarith
  have hexistsStep :
      ∃ h : ℝ,
        0 < frequencyAnnihilatorMultiplier gamma (omega i) h ^ 2 := by
    by_contra hnone
    push Not at hnone
    have hzero :
        ∀ h : ℝ,
          frequencyAnnihilatorMultiplier gamma (omega i) h ^ 2 = 0 := by
      intro h
      exact le_antisymm (hnone h) (sq_nonneg _)
    simp_rw [hzero] at hmultiplierIntegral
    simp at hmultiplierIntegral
  obtain ⟨h, hmultiplier⟩ := hexistsStep
  let transformedCoefficient : ι → ℂ := fun j =>
    (frequencyAnnihilatorMultiplier gamma (omega j) h : ℂ) * c j
  let D : ℝ := ∑ j ∈ S, ‖transformedCoefficient j‖ ^ 2
  have hterm :
      0 < ‖transformedCoefficient i‖ ^ 2 := by
    have hmultiplierNe :
        frequencyAnnihilatorMultiplier gamma (omega i) h ≠ 0 := by
      nlinarith
    have hciNe : c i ≠ 0 := by
      simpa [sq_pos_iff] using hci
    have hproduct :
        transformedCoefficient i ≠ 0 := by
      exact mul_ne_zero
        (Complex.ofReal_ne_zero.mpr hmultiplierNe) hciNe
    exact sq_pos_of_pos (norm_pos_iff.mpr hproduct)
  have hD : 0 < D := by
    have hle :
        ‖transformedCoefficient i‖ ^ 2 ≤
          ∑ j ∈ S, ‖transformedCoefficient j‖ ^ 2 :=
      Finset.single_le_sum
        (fun j _hj => sq_nonneg ‖transformedCoefficient j‖) hi
    exact hterm.trans_le hle
  let B : ℝ :=
    PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound
      S transformedCoefficient omega
  have hB : 0 ≤ B :=
    offDiagonalBound_nonneg S transformedCoefficient omega
  let L : ℝ := (B + 1) / D
  have hL : 0 < L := by
    exact div_pos (by linarith) hD
  have hmeanSquare :=
    PrimeNumberTheorem.ZeroForcedOscillation.abs_intervalIntegral_sqNorm_exponentialPolynomial_sub_diagonal_le
      S transformedCoefficient omega (a := (0 : ℝ)) (b := L) hinj
  have hlower := (abs_le.mp hmeanSquare).1
  have hLD : L * D = B + 1 := by
    dsimp [L]
    field_simp [hD.ne']
  have hIntegral :
      1 ≤ ∫ y in (0 : ℝ)..L,
        ‖PrimeNumberTheorem.ZeroForcedOscillation.exponentialPolynomial
          S transformedCoefficient omega y‖ ^ 2 := by
    dsimp [D, B] at hlower hLD ⊢
    linarith
  refine ⟨h, L, hL, ?_⟩
  have hone : (0 : ℝ) < 1 := by norm_num
  apply hone.trans_le
  simpa [annihilatedExponentialPolynomial, transformedCoefficient] using
    hIntegral

/-- Positive-height zeros in the selected equal-real-part package, excluding
the target frequency `gamma`. The selected target and its conjugate are both
absent: the former by the frequency inequality and the latter by positivity. -/
def positiveEqualRealPartResidualPackage
    (T beta gamma : ℝ) : Finset ℂ :=
  (PrimeNumberTheorem.ZeroForcedOscillation.equalRealPartZeroPackage T beta).filter
    fun rho => 0 < rho.im ∧ rho.im ≠ gamma

/-- The actual multiplicity-aware coefficient of a zeta zero in logarithmic
coordinates. -/
def zetaEqualRealPartResidualCoefficient (rho : ℂ) : ℂ :=
  (analyticOrderNatAt riemannZeta rho : ℂ) * rho⁻¹

/-- A nonempty finite package of actual positive-height zeta zeros on the
selected real-part line, after removing the target frequency, survives some
target-pair annihilator step and has positive second moment on a finite
logarithmic interval.

This theorem is conditional only on the finite package being nonempty. It does
not assert the existence of another same-real-part zero and does not estimate
the complementary zero or contour terms. -/
theorem
    exists_step_intervalIntegral_annihilatedPositiveEqualRealPartResidual_pos
    {T beta gamma : ℝ}
    (hgamma : 0 < gamma)
    (hnonempty :
      (positiveEqualRealPartResidualPackage T beta gamma).Nonempty) :
    ∃ h L : ℝ,
      0 < L ∧
        0 < ∫ y in (0 : ℝ)..L,
          ‖annihilatedExponentialPolynomial
            (positiveEqualRealPartResidualPackage T beta gamma)
            zetaEqualRealPartResidualCoefficient Complex.im gamma h y‖ ^ 2 := by
  classical
  let S := positiveEqualRealPartResidualPackage T beta gamma
  have hmem {rho : ℂ} (hrho : rho ∈ S) :
      RiemannHypothesis.IsNontrivialZero rho ∧
        |rho.im| ≤ T ∧ rho.re = beta ∧
          0 < rho.im ∧ rho.im ≠ gamma := by
    have hfilter :
        rho ∈
          PrimeNumberTheorem.ZeroForcedOscillation.equalRealPartZeroPackage
              T beta ∧
            0 < rho.im ∧ rho.im ≠ gamma := by
      simpa [S, positiveEqualRealPartResidualPackage] using hrho
    have hzero :=
      PrimeNumberTheorem.ZeroForcedOscillation.mem_equalRealPartZeroPackage.mp
        hfilter.1
    exact ⟨hzero.1, hzero.2.1, hzero.2.2, hfilter.2.1, hfilter.2.2⟩
  have homega : ∀ rho ∈ S, 0 < rho.im := by
    intro rho hrho
    exact (hmem hrho).2.2.2.1
  have hne : ∀ rho ∈ S, rho.im ≠ gamma := by
    intro rho hrho
    exact (hmem hrho).2.2.2.2
  have hinj : Set.InjOn Complex.im ↑S := by
    intro rho hrho z hz him
    apply Complex.ext
    · exact (hmem hrho).2.2.1.trans (hmem hz).2.2.1.symm
    · exact him
  have hcoeff :
      0 < ∑ rho ∈ S, ‖zetaEqualRealPartResidualCoefficient rho‖ ^ 2 := by
    obtain ⟨rho, hrho⟩ := hnonempty
    have hrhoData := hmem hrho
    have hrhoNeZero : rho ≠ 0 := by
      intro hzero
      have himzero := congrArg Complex.im hzero
      simp at himzero
      linarith [hrhoData.2.2.2.1]
    have hrhoNeOne : rho ≠ 1 := by
      intro hone
      have himzero := congrArg Complex.im hone
      simp at himzero
      linarith [hrhoData.2.2.2.1]
    have horder :
        0 < analyticOrderNatAt riemannZeta rho :=
      ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
        hrhoNeOne hrhoData.1.1
    have hcoefficientNe :
        zetaEqualRealPartResidualCoefficient rho ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast horder.ne'
      · exact inv_ne_zero hrhoNeZero
    have hterm :
        0 < ‖zetaEqualRealPartResidualCoefficient rho‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hcoefficientNe)
    have hle :
        ‖zetaEqualRealPartResidualCoefficient rho‖ ^ 2 ≤
          ∑ z ∈ S, ‖zetaEqualRealPartResidualCoefficient z‖ ^ 2 :=
      Finset.single_le_sum
        (fun z _hz => sq_nonneg ‖zetaEqualRealPartResidualCoefficient z‖) hrho
    exact hterm.trans_le hle
  exact exists_step_intervalIntegral_annihilatedExponentialPolynomial_pos
    S zetaEqualRealPartResidualCoefficient Complex.im hgamma homega hne hinj
      hcoeff

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
