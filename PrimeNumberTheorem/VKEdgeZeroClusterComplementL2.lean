import PrimeNumberTheorem.VKEdgeZeroClusterApproximationL2
import PrimeNumberTheorem.ZeroForcedOscillationComplementaryBound

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Local L2 bounds for the complementary zero package

This module connects the arbitrary selected-cluster complement to the
equal-real-part package used by the fixed-height complementary-zero bounds.
Under a uniform positive real-part gap, it proves local second-moment decay
uniformly for heights of size `exp (a / 2)`.

The uniform gap remains an explicit hypothesis. The theorem does not assert
that the moving maximal zero layer has such a gap.
-/

/-- The equal-real-part complementary package with real-exponent
normalization. -/
noncomputable def normalizedEqualRealPartComplementContribution
    (T beta y : ℝ) : ℂ :=
  (Real.exp (-beta * y) : ℂ) *
    ZeroForcedOscillation.complementaryZeroPackageContribution
      (Real.exp y) T beta

/-- Local second moment of the normalized equal-real-part complement. -/
noncomputable def normalizedEqualRealPartComplementSecondMoment
    (T beta a L : ℝ) : ℝ :=
  ∫ y in a..(a + L),
    ‖normalizedEqualRealPartComplementContribution T beta y‖ ^ 2

/-- Selecting the complete equal-real-part package in the arbitrary cluster
API leaves exactly the complementary package from the fixed-height API. -/
theorem normalizedFiniteZeroClusterComplementContribution_equalRealPart
    (T beta y : ℝ) :
    normalizedFiniteZeroClusterComplementContribution
        (ZeroForcedOscillation.equalRealPartZeroPackage T beta)
        T beta y =
      normalizedEqualRealPartComplementContribution T beta y := by
  classical
  have hfinset :
      nontrivialZerosFinset T \
          ZeroForcedOscillation.equalRealPartZeroPackage T beta =
        ZeroForcedOscillation.complementaryZeroPackage T beta := by
    ext rho
    simp only [Finset.mem_sdiff, Finset.mem_filter,
      ZeroForcedOscillation.equalRealPartZeroPackage,
      ZeroForcedOscillation.complementaryZeroPackage]
    tauto
  unfold normalizedFiniteZeroClusterComplementContribution
  unfold finiteZeroClusterComplementContribution
  unfold normalizedEqualRealPartComplementContribution
  unfold ZeroForcedOscillation.complementaryZeroPackageContribution
  rw [hfinset]

private theorem continuous_normalizedEqualRealPartComplementContribution
    (T beta : ℝ) :
    Continuous (normalizedEqualRealPartComplementContribution T beta) := by
  rw [show normalizedEqualRealPartComplementContribution T beta =
      normalizedFiniteZeroClusterContribution
        (ZeroForcedOscillation.complementaryZeroPackage T beta)
        (analyticOrderNatAt riemannZeta) beta by
    funext y
    rfl]
  rw [show
      normalizedFiniteZeroClusterContribution
          (ZeroForcedOscillation.complementaryZeroPackage T beta)
          (analyticOrderNatAt riemannZeta) beta =
        fun y =>
          MathlibAux.driftingExponentialPolynomial
            (ZeroForcedOscillation.complementaryZeroPackage T beta)
            (finiteZeroClusterCoefficientAt
              (analyticOrderNatAt riemannZeta) beta 0)
            Complex.im (fun rho => rho.re - beta) 0 y by
    funext y
    exact normalizedFiniteZeroClusterContribution_eq_drifting
      (ZeroForcedOscillation.complementaryZeroPackage T beta)
      (analyticOrderNatAt riemannZeta) beta 0 y]
  unfold MathlibAux.driftingExponentialPolynomial
  fun_prop

/-- One global reciprocal-zero constant gives a normalized pointwise bound
for every height, exponent, gap, and nonnegative logarithmic coordinate. -/
theorem
    exists_uniform_norm_normalizedEqualRealPartComplementContribution_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {T beta delta y : ℝ},
        4 ≤ T →
        0 ≤ y →
        (∀ rho ∈ ZeroForcedOscillation.complementaryZeroPackage T beta,
          rho.re ≤ beta - delta) →
        ‖normalizedEqualRealPartComplementContribution T beta y‖ ≤
          Real.exp (-delta * y) *
            (C * (1 + Real.log (T + 6)) ^ 2) := by
  rcases ExplicitFormulaAux.exists_globalReciprocalZeroMultiplicity_le_log_sq
      with ⟨C, hC, hCbound⟩
  refine ⟨C, hC, ?_⟩
  intro T beta delta y hT hy hgap
  have hraw :=
    ZeroForcedOscillation.norm_complementaryZeroPackageContribution_le_exp_gap_mul_sum_nontrivialZerosFinset
        T beta delta y hy hgap
  have hsum :
      (∑ rho ∈ nontrivialZerosFinset T,
          (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) ≤
        C * (1 + Real.log (T + 6)) ^ 2 := by
    simpa only [ExplicitFormulaAux.globalReciprocalZeroMultiplicity] using
      hCbound T hT
  unfold normalizedEqualRealPartComplementContribution
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-beta * y) *
          ‖ZeroForcedOscillation.complementaryZeroPackageContribution
            (Real.exp y) T beta‖ ≤
        Real.exp (-beta * y) *
          (Real.exp ((beta - delta) * y) *
            ∑ rho ∈ nontrivialZerosFinset T,
              (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) :=
      mul_le_mul_of_nonneg_left hraw (Real.exp_pos _).le
    _ ≤
        Real.exp (-beta * y) *
          (Real.exp ((beta - delta) * y) *
            (C * (1 + Real.log (T + 6)) ^ 2)) := by
      gcongr
    _ = Real.exp (-delta * y) *
          (C * (1 + Real.log (T + 6)) ^ 2) := by
      have hexpProduct :
          Real.exp (-beta * y) * Real.exp ((beta - delta) * y) =
            Real.exp (-delta * y) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← mul_assoc, hexpProduct]

private theorem log_height_factor_le_four_add
    {T a : ℝ}
    (hT : 4 ≤ T)
    (ha : 0 ≤ a)
    (hTupper : T ≤ Real.exp (a / 2) + 1) :
    1 + Real.log (T + 6) ≤ 4 + a := by
  have hExpOne : 1 ≤ Real.exp (a / 2) := by
    exact Real.one_le_exp (by linarith)
  have hTplus : T + 6 ≤ 8 * Real.exp (a / 2) := by
    calc
      T + 6 ≤ Real.exp (a / 2) + 7 := by linarith
      _ ≤ 8 * Real.exp (a / 2) := by nlinarith
  have hlog :
      Real.log (T + 6) ≤ Real.log 8 + a / 2 := by
    calc
      Real.log (T + 6) ≤ Real.log (8 * Real.exp (a / 2)) := by
        exact Real.log_le_log (by linarith) hTplus
      _ = Real.log 8 + a / 2 := by
        rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0)
          (ne_of_gt (Real.exp_pos (a / 2))), Real.log_exp]
  have hlogEight : Real.log 8 < 3 := by
    calc
      Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num
      _ < 3 := by nlinarith [Real.log_two_lt_d9]
  linarith

/-- A single global constant controls the local complement second moment for
all moving heights in the `exp (a / 2)` interval, provided the complementary
zeros obey one fixed real-part gap. -/
theorem
    exists_uniform_normalizedEqualRealPartComplementSecondMoment_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {T beta delta a L : ℝ},
        4 ≤ T →
        0 ≤ delta →
        0 ≤ a →
        0 ≤ L →
        T ∈ Set.Icc (Real.exp (a / 2)) (Real.exp (a / 2) + 1) →
        (∀ rho ∈ ZeroForcedOscillation.complementaryZeroPackage T beta,
          rho.re ≤ beta - delta) →
        normalizedEqualRealPartComplementSecondMoment T beta a L ≤
          L * (Real.exp (-delta * a) * (C * (4 + a) ^ 2)) ^ 2 := by
  rcases exists_uniform_norm_normalizedEqualRealPartComplementContribution_le
      with ⟨C, hC, hpoint⟩
  refine ⟨C, hC, ?_⟩
  intro T beta delta a L hT hdelta ha hL hTmem hgap
  have hab : a ≤ a + L := by linarith
  have hlogNonneg : 0 ≤ 1 + Real.log (T + 6) := by
    have hone : 1 ≤ T + 6 := by linarith
    linarith [Real.log_nonneg hone]
  have hfourNonneg : 0 ≤ 4 + a := by linarith
  have hlogFactor :
      1 + Real.log (T + 6) ≤ 4 + a :=
    log_height_factor_le_four_add hT ha hTmem.2
  have hcoef :
      C * (1 + Real.log (T + 6)) ^ 2 ≤ C * (4 + a) ^ 2 := by
    have hsq :
        (1 + Real.log (T + 6)) ^ 2 ≤ (4 + a) ^ 2 := by
      nlinarith
    exact mul_le_mul_of_nonneg_left hsq hC
  have huniform :
      ∀ y ∈ Icc a (a + L),
        ‖normalizedEqualRealPartComplementContribution T beta y‖ ≤
          Real.exp (-delta * a) * (C * (4 + a) ^ 2) := by
    intro y hy
    have hexp :
        Real.exp (-delta * y) ≤ Real.exp (-delta * a) := by
      exact Real.exp_le_exp.mpr (by nlinarith [hy.1])
    calc
      ‖normalizedEqualRealPartComplementContribution T beta y‖ ≤
          Real.exp (-delta * y) *
            (C * (1 + Real.log (T + 6)) ^ 2) :=
        hpoint hT (ha.trans hy.1) hgap
      _ ≤ Real.exp (-delta * a) *
            (C * (4 + a) ^ 2) := by
        exact mul_le_mul hexp hcoef
          (mul_nonneg hC (sq_nonneg _)) (Real.exp_pos _).le
  have hleft :
      IntervalIntegrable
        (fun y =>
          ‖normalizedEqualRealPartComplementContribution T beta y‖ ^ 2)
        volume a (a + L) :=
    ((continuous_normalizedEqualRealPartComplementContribution T beta).norm.pow 2
      |>.intervalIntegrable a (a + L))
  have hright :
      IntervalIntegrable
        (fun _ : ℝ =>
          (Real.exp (-delta * a) * (C * (4 + a) ^ 2)) ^ 2)
        volume a (a + L) :=
    intervalIntegrable_const
  have hpointSq :
      ∀ y ∈ Icc a (a + L),
        ‖normalizedEqualRealPartComplementContribution T beta y‖ ^ 2 ≤
          (Real.exp (-delta * a) * (C * (4 + a) ^ 2)) ^ 2 := by
    intro y hy
    have := huniform y hy
    nlinarith [norm_nonneg
      (normalizedEqualRealPartComplementContribution T beta y),
      Real.exp_pos (-delta * a), hC, sq_nonneg (4 + a)]
  have hmono :=
    intervalIntegral.integral_mono_on hab hleft hright hpointSq
  unfold normalizedEqualRealPartComplementSecondMoment
  calc
    (∫ y in a..(a + L),
        ‖normalizedEqualRealPartComplementContribution T beta y‖ ^ 2) ≤
        ∫ _y in a..(a + L),
          (Real.exp (-delta * a) * (C * (4 + a) ^ 2)) ^ 2 :=
      hmono
    _ = L * (Real.exp (-delta * a) * (C * (4 + a) ^ 2)) ^ 2 := by
      simp

private theorem tendsto_exp_neg_mul_four_add_pow_four
    {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto
      (fun a : ℝ => Real.exp (-2 * delta * a) * (4 + a) ^ 4)
      atTop (nhds 0) := by
  have hc : -2 * delta < 0 := by linarith
  have hpow (k : ℕ) :
      Tendsto (fun a : ℝ => Real.exp ((-2 * delta) * a) * a ^ k)
        atTop (nhds 0) := by
    have hsmall :=
      isLittleO_exp_mul_rpow_of_lt (k : ℝ)
        (a := -2 * delta) (b := 0) hc
    have hratio := hsmall.tendsto_div_nhds_zero
    simpa [Real.rpow_natCast] using hratio
  have h4 := hpow 4
  have h3 := (hpow 3).const_mul 16
  have h2 := (hpow 2).const_mul 96
  have h1 := (hpow 1).const_mul 256
  have h0 := (hpow 0).const_mul 256
  have hsum := (((h4.add h3).add h2).add h1).add h0
  have hsum' :
      Tendsto
        (fun x =>
          Real.exp (-2 * delta * x) * x ^ 4 +
              16 * (Real.exp (-2 * delta * x) * x ^ 3) +
            96 * (Real.exp (-2 * delta * x) * x ^ 2) +
            256 * (Real.exp (-2 * delta * x) * x) +
            256 * Real.exp (-2 * delta * x))
        atTop (nhds 0) := by
    simpa only [pow_one, pow_zero, mul_one, mul_zero, add_zero,
      zero_add] using hsum
  convert hsum' using 1
  funext a
  ring

/-- A fixed positive real-part gap makes the normalized complement second
moment tend to zero uniformly over all allowed moving heights. -/
theorem eventually_normalizedEqualRealPartComplementSecondMoment_lt
    {beta delta L eta : ℝ}
    (hdelta : 0 < delta)
    (hL : 0 ≤ L)
    (heta : 0 < eta) :
    ∀ᶠ a in atTop,
      ∀ T ∈ Set.Icc (Real.exp (a / 2)) (Real.exp (a / 2) + 1),
        4 ≤ T →
        (∀ rho ∈ ZeroForcedOscillation.complementaryZeroPackage T beta,
          rho.re ≤ beta - delta) →
        normalizedEqualRealPartComplementSecondMoment T beta a L < eta := by
  rcases exists_uniform_normalizedEqualRealPartComplementSecondMoment_le
      with ⟨C, hC, hmoment⟩
  have hbase :=
    tendsto_exp_neg_mul_four_add_pow_four hdelta
  have henvelope :
      Tendsto
        (fun a : ℝ =>
          L * (Real.exp (-delta * a) * (C * (4 + a) ^ 2)) ^ 2)
        atTop (nhds 0) := by
    have hscaled := hbase.const_mul (L * C ^ 2)
    have hscaled' :
        Tendsto
          (fun x =>
            L * C ^ 2 *
              (Real.exp (-2 * delta * x) * (4 + x) ^ 4))
          atTop (nhds 0) := by
      simpa only [mul_zero] using hscaled
    convert hscaled' using 1
    funext a
    have hexpSq :
        Real.exp (-delta * a) ^ 2 =
          Real.exp (-2 * delta * a) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [mul_pow, hexpSq]
    ring
  have hsmall :
      ∀ᶠ a in atTop,
        L * (Real.exp (-delta * a) * (C * (4 + a) ^ 2)) ^ 2 < eta :=
    (tendsto_order.1 henvelope).2 eta heta
  have ha0 : ∀ᶠ a : ℝ in atTop, 0 ≤ a :=
    eventually_ge_atTop 0
  filter_upwards [hsmall, ha0] with a henv ha
  intro T hTmem hT hgap
  exact (hmoment hT hdelta.le ha hL hTmem hgap).trans_lt henv

/-- Pointwise three-component square bound for the no-jump selected-cluster
remainder. This is purely algebraic and introduces no zero-distribution
hypothesis. -/
theorem
    normSq_normalizedFiniteZeroClusterPsiRemainderWithoutJump_le_components
    (S : Finset ℂ) (T beta y : ℝ) :
    ‖normalizedFiniteZeroClusterPsiRemainderWithoutJump S T beta y‖ ^ 2 ≤
      3 *
        (‖normalizedFiniteZeroClusterComplementContribution S T beta y‖ ^ 2 +
          ‖normalizedFiniteZeroClusterApproximationError T beta y‖ ^ 2 +
          ‖normalizedZeroPackageClosedTerms beta y‖ ^ 2) := by
  rw [normalizedFiniteZeroClusterPsiRemainderWithoutJump_eq_components]
  let A :=
    ‖normalizedFiniteZeroClusterComplementContribution S T beta y‖
  let B :=
    ‖normalizedFiniteZeroClusterApproximationError T beta y‖
  let D :=
    ‖normalizedZeroPackageClosedTerms beta y‖
  have htriangle :
      ‖normalizedFiniteZeroClusterComplementContribution S T beta y +
          normalizedFiniteZeroClusterApproximationError T beta y +
          normalizedZeroPackageClosedTerms beta y‖ ≤
        A + B + D := by
    calc
      ‖normalizedFiniteZeroClusterComplementContribution S T beta y +
          normalizedFiniteZeroClusterApproximationError T beta y +
          normalizedZeroPackageClosedTerms beta y‖ ≤
          ‖normalizedFiniteZeroClusterComplementContribution S T beta y +
            normalizedFiniteZeroClusterApproximationError T beta y‖ +
            ‖normalizedZeroPackageClosedTerms beta y‖ :=
        norm_add_le _ _
      _ ≤
          (‖normalizedFiniteZeroClusterComplementContribution S T beta y‖ +
            ‖normalizedFiniteZeroClusterApproximationError T beta y‖) +
            ‖normalizedZeroPackageClosedTerms beta y‖ :=
        add_le_add (norm_add_le _ _) (le_refl _)
      _ = A + B + D := rfl
  have hnonneg :
      0 ≤
        ‖normalizedFiniteZeroClusterComplementContribution S T beta y +
          normalizedFiniteZeroClusterApproximationError T beta y +
          normalizedZeroPackageClosedTerms beta y‖ :=
    norm_nonneg _
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  have hD : 0 ≤ D := norm_nonneg _
  have hsumSq :
      (A + B + D) ^ 2 ≤ 3 * (A ^ 2 + B ^ 2 + D ^ 2) := by
    nlinarith [sq_nonneg (A - B), sq_nonneg (A - D),
      sq_nonneg (B - D)]
  dsimp [A, B, D] at hsumSq
  nlinarith

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
