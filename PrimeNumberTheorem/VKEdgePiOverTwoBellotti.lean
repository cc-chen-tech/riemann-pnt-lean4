import PrimeNumberTheorem.VKEdgePiOverTwoEpsilonOscillation
import PrimeNumberTheorem.VKEdgePiOverTwoPositiveMeasure

open Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/--
The distinct zeta-zero locations in Bellotti's open-height convention:
`0 < Im rho < T` and `sigma < Re rho`.

Unlike `ZeroDensity.zeroDensityCount`, this finset does not attach analytic
multiplicity.  This is the exact convention needed for the odd-harmonic
pigeonhole argument.
-/
def bellottiZeroLocationsFinset (sigma T : ℝ) : Finset ℂ :=
  (ZeroDensity.zeroDensityZerosFinset sigma T).filter fun rho =>
    rho.im < T

theorem mem_bellottiZeroLocationsFinset
    {rho : ℂ} {sigma T : ℝ} :
    rho ∈ bellottiZeroLocationsFinset sigma T ↔
      RiemannHypothesis.IsNontrivialZero rho ∧
        0 < rho.im ∧ rho.im < T ∧ sigma < rho.re := by
  rw [bellottiZeroLocationsFinset, Finset.mem_filter,
    ZeroDensity.mem_zeroDensityZerosFinset]
  constructor
  · rintro ⟨⟨hzero, him, _himLe, hre⟩, himLt⟩
    exact ⟨hzero, him, himLt, hre⟩
  · rintro ⟨hzero, him, himLt, hre⟩
    exact ⟨⟨hzero, him, himLt.le, hre⟩, himLt⟩

/-- Bellotti-style zero count: distinct locations, positive ordinate, and
strict upper height. -/
def bellottiZeroLocationCount (sigma T : ℝ) : ℕ :=
  (bellottiZeroLocationsFinset sigma T).card

/-- The Vinogradov--Korobov edge scale used in the Bellotti specialization. -/
def vinogradovKorobovEdgeWidth (T : ℝ) : ℝ :=
  (Real.log T) ^ (-2 / 3 : ℝ) *
    (Real.log (Real.log T)) ^ (-1 / 3 : ℝ)

/--
The distinct-location count is bounded by the repository's
multiplicity-counted zero-density count.  The converse is deliberately not
asserted: it would require simplicity or an independent multiplicity bound.
-/
theorem bellottiZeroLocationCount_le_zeroDensityCount
    (sigma T : ℝ) :
    bellottiZeroLocationCount sigma T ≤
      ZeroDensity.zeroDensityCount sigma T := by
  classical
  unfold bellottiZeroLocationCount ZeroDensity.zeroDensityCount
  rw [Finset.card_eq_sum_ones]
  calc
    (∑ _rho ∈ bellottiZeroLocationsFinset sigma T, 1) ≤
        ∑ rho ∈ bellottiZeroLocationsFinset sigma T,
          analyticOrderNatAt riemannZeta rho := by
      apply Finset.sum_le_sum
      intro rho hrho
      have hrhoData :=
        mem_bellottiZeroLocationsFinset.mp hrho
      exact
        ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
          (by
            intro hrhoOne
            have hre := congrArg Complex.re hrhoOne
            simp at hre
            linarith [hrhoData.1.2.2])
          hrhoData.1.1
    _ ≤ ∑ rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T,
          analyticOrderNatAt riemannZeta rho := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)

/--
An upper bound for Bellotti's distinct-location count is already enough to
force a missing member among the first `M + 1` positive odd harmonics.
-/
theorem
    exists_riemannZeta_ne_zero_at_oddHarmonic_of_bellottiCount_le
    {beta gamma sigma : ℝ} {M : ℕ}
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (hgamma : 0 < gamma) (hsigma : sigma < beta)
    (hcount :
      bellottiZeroLocationCount sigma
          (((2 * M + 2 : ℕ) : ℝ) * gamma) ≤ M) :
    ∃ k : ℕ, k < M + 1 ∧
      riemannZeta (oddHarmonicPoint beta gamma k) ≠ 0 := by
  classical
  by_contra hmissing
  push Not at hmissing
  let S : Finset ℂ :=
    (Finset.range (M + 1)).image (oddHarmonicPoint beta gamma)
  have hS_subset :
      S ⊆ bellottiZeroLocationsFinset sigma
        (((2 * M + 2 : ℕ) : ℝ) * gamma) := by
    intro rho hrho
    rcases Finset.mem_image.mp hrho with ⟨k, hk, rfl⟩
    have hklt : k < M + 1 := Finset.mem_range.mp hk
    have hzero :
        riemannZeta (oddHarmonicPoint beta gamma k) = 0 :=
      hmissing k hklt
    have hoddPos : 0 < (2 * k + 1 : ℕ) := by omega
    have himPos :
        0 < (oddHarmonicPoint beta gamma k).im := by
      simp only [oddHarmonicPoint_im]
      exact mul_pos (by exact_mod_cast hoddPos) hgamma
    have hoddLt : 2 * k + 1 < 2 * M + 2 := by omega
    have himLt :
        (oddHarmonicPoint beta gamma k).im <
          ((2 * M + 2 : ℕ) : ℝ) * gamma := by
      simp only [oddHarmonicPoint_im]
      exact mul_lt_mul_of_pos_right
        (by exact_mod_cast hoddLt) hgamma
    exact mem_bellottiZeroLocationsFinset.mpr
      ⟨⟨hzero, by simpa using hbeta0, by simpa using hbeta1⟩,
        himPos, himLt, by simpa using hsigma⟩
  have hcard : S.card = M + 1 := by
    dsimp [S]
    rw [Finset.card_image_of_injective _
      (oddHarmonicPoint_injective beta hgamma)]
    simp
  have hcardLe :
      S.card ≤ bellottiZeroLocationCount sigma
        (((2 * M + 2 : ℕ) : ℝ) * gamma) := by
    exact Finset.card_le_card hS_subset
  omega

/--
The uniform strict oscillation constant when the missing harmonic is known
to occur among indices `0, ..., M`.
-/
def finiteStrictPiOverTwoOscillationConstant (M : ℕ) : ℝ :=
  strictPiOverTwoOscillationConstant M

theorem pi_div_two_lt_finiteStrictPiOverTwoOscillationConstant (M : ℕ) :
    Real.pi / 2 < finiteStrictPiOverTwoOscillationConstant M :=
  pi_div_two_lt_strictPiOverTwoOscillationConstant M

private theorem sharpenedMissingHarmonicDenominator_mono
    {k M : ℕ} (hkM : k ≤ M) :
    sharpenedMissingHarmonicDenominator k ≤
      sharpenedMissingHarmonicDenominator M := by
  let n : ℝ := ((2 * k + 1 : ℕ) : ℝ)
  let N : ℝ := ((2 * M + 1 : ℕ) : ℝ)
  have hnPos : 0 < n := by positivity
  have hnLe : n ≤ N := by
    dsimp [n, N]
    exact_mod_cast (show 2 * k + 1 ≤ 2 * M + 1 by omega)
  have hsqLe : n ^ 2 ≤ N ^ 2 :=
    (sq_le_sq₀ hnPos.le (hnPos.le.trans hnLe)).2 hnLe
  have hpiMul :
      Real.pi * n ^ 2 ≤ Real.pi * N ^ 2 :=
    mul_le_mul_of_nonneg_left hsqLe Real.pi_pos.le
  have hinv :
      1 / (Real.pi * N ^ 2) ≤
        1 / (Real.pi * n ^ 2) :=
    one_div_le_one_div_of_le
      (mul_pos Real.pi_pos (sq_pos_of_pos hnPos)) hpiMul
  unfold sharpenedMissingHarmonicDenominator
  change
    2 / Real.pi - 1 / (Real.pi * n ^ 2) ≤
      2 / Real.pi - 1 / (Real.pi * N ^ 2)
  linarith

private theorem sharpenedMissingHarmonicLowerBound_antitone
    {k M : ℕ} (hkM : k ≤ M) :
    sharpenedMissingHarmonicLowerBound M ≤
      sharpenedMissingHarmonicLowerBound k := by
  unfold sharpenedMissingHarmonicLowerBound
  exact one_div_le_one_div_of_le
    (sharpenedMissingHarmonicDenominator_pos k)
    (sharpenedMissingHarmonicDenominator_mono hkM)

theorem finiteStrictPiOverTwoOscillationConstant_le
    {k M : ℕ} (hkM : k ≤ M) :
    finiteStrictPiOverTwoOscillationConstant M ≤
      strictPiOverTwoOscillationConstant k := by
  unfold finiteStrictPiOverTwoOscillationConstant
    strictPiOverTwoOscillationConstant
  linarith [sharpenedMissingHarmonicLowerBound_antitone hkM]

/--
Exact translation from a Bellotti-style distinct-location count to a
missing odd harmonic carrying a uniform strict gap depending only on `M`.
-/
theorem exists_missing_oddHarmonic_with_uniform_gap_of_bellottiCount_le
    {beta gamma sigma : ℝ} {M : ℕ}
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (hgamma : 0 < gamma) (hsigma : sigma < beta)
    (hcount :
      bellottiZeroLocationCount sigma
          (((2 * M + 2 : ℕ) : ℝ) * gamma) ≤ M) :
    ∃ k : ℕ, k ≤ M ∧
      riemannZeta (oddHarmonicPoint beta gamma k) ≠ 0 ∧
      finiteStrictPiOverTwoOscillationConstant M ≤
        strictPiOverTwoOscillationConstant k := by
  rcases
      exists_riemannZeta_ne_zero_at_oddHarmonic_of_bellottiCount_le
        hbeta0 hbeta1 hgamma hsigma hcount with
    ⟨k, hk, hmissing⟩
  have hkM : k ≤ M := by omega
  exact
    ⟨k, hkM, hmissing,
      finiteStrictPiOverTwoOscillationConstant_le hkM⟩

/--
Bellotti's distinct-location count convention yields a uniform strict
`pi / 2` oscillation constant in every sufficiently late epsilon power
window.
-/
theorem
    eventually_exists_psiError_in_powerOnePlusEpsilonWindow_gt_uniformBellottiGap
    {ε : ℝ} {rho : ℂ} {sigma : ℝ} {M : ℕ}
    (hε : 0 < ε)
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hσrho : sigma < rho.re)
    (hcount :
      bellottiZeroLocationCount sigma
          (((2 * M + 2 : ℕ) : ℝ) * rho.im) ≤ M) :
    ∀ᶠ Y : ℝ in atTop,
      ∃ x ∈ powerOnePlusEpsilonWindow ε Y,
        (analyticOrderNatAt riemannZeta rho : ℝ) *
              finiteStrictPiOverTwoOscillationConstant M *
              (x ^ rho.re / ‖rho‖) <
            |chebyshevPsi x - x| := by
  rcases
      exists_missing_oddHarmonic_with_uniform_gap_of_bellottiCount_le
        hrhoRe0 hrhoRe1 hgamma hσrho hcount with
    ⟨k, _hk, hmissing, hconstant⟩
  have hmissing' :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 := by
    simpa [missingHarmonicContourCenter] using hmissing
  have hlocal :=
    eventually_exists_psiError_in_powerOnePlusEpsilonWindow_gt_strictPiOverTwo
      hε hrhoRe0 hrhoRe1 hgamma hzero hmissing'
  filter_upwards [hlocal, eventually_ge_atTop (1 : ℝ)] with Y hY hYOne
  rcases hY with ⟨x, hx, hlarge⟩
  refine ⟨x, hx, ?_⟩
  have hxNonneg : 0 ≤ x :=
    zero_le_one.trans (hYOne.trans hx.1)
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hconstant (Nat.cast_nonneg _))
    (div_nonneg (Real.rpow_nonneg hxNonneg _) (norm_nonneg _))).trans_lt hlarge

/--
The same Bellotti-style count forces a positive-logarithmic-measure set
above one uniform strict `pi / 2` threshold in every sufficiently late
epsilon log window.
-/
theorem
    eventually_positive_measure_in_epsilonLogWindow_gt_uniformBellottiGap
    {ε : ℝ} {rho : ℂ} {sigma : ℝ} {M : ℕ}
    (hε : 0 < ε)
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hσrho : sigma < rho.re)
    (hcount :
      bellottiZeroLocationCount sigma
          (((2 * M + 2 : ℕ) : ℝ) * rho.im) ≤ M) :
    ∀ᶠ Y : ℝ in atTop,
      0 <
        volume.real
          {y ∈ Icc (Real.log Y) ((1 + ε) * Real.log Y) |
            (analyticOrderNatAt riemannZeta rho : ℝ) *
                finiteStrictPiOverTwoOscillationConstant M <
              |normalizedPsiError rho y|} := by
  rcases
      exists_missing_oddHarmonic_with_uniform_gap_of_bellottiCount_le
        hrhoRe0 hrhoRe1 hgamma hσrho hcount with
    ⟨k, _hk, hmissing, hconstant⟩
  have hmissing' :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 := by
    simpa [missingHarmonicContourCenter] using hmissing
  have hlocal :=
    eventually_positive_measure_normalizedPsiError_gt_strictPiOverTwo
      (epsilonCenterCoefficient_ge_sixteen hε)
      (epsilonRadiusCoefficient_pos hε)
      (epsilonRadiusCoefficient_lt_center hε)
      (epsilonRadius_sq_ge_sixteen_mul hε)
      hrhoRe0 hrhoRe1 hgamma hzero hmissing'
  have hscaled :=
    (tendsto_epsilonGaussianScale_atTop hε).eventually hlocal
  filter_upwards [hscaled] with Y hY
  let window : Set ℝ :=
    Icc (Real.log Y) ((1 + ε) * Real.log Y)
  let strictSet : Set ℝ :=
    {y ∈ window |
      (analyticOrderNatAt riemannZeta rho : ℝ) *
          strictPiOverTwoOscillationConstant k <
        |normalizedPsiError rho y|}
  let uniformSet : Set ℝ :=
    {y ∈ window |
      (analyticOrderNatAt riemannZeta rho : ℝ) *
          finiteStrictPiOverTwoOscillationConstant M <
        |normalizedPsiError rho y|}
  have hsubset : strictSet ⊆ uniformSet := by
    intro y hy
    exact
      ⟨hy.1,
        (mul_le_mul_of_nonneg_left hconstant (Nat.cast_nonneg _)).trans_lt
          hy.2⟩
  have hfinite : volume uniformSet ≠ ⊤ :=
    measure_ne_top_of_subset
      (show uniformSet ⊆ window from fun _ hy => hy.1)
      isCompact_Icc.measure_lt_top.ne
  have hY' : 0 < volume.real strictSet := by
    simpa only [
      localizedGaussianLogWindow_epsilonGaussianScale hε Y] using hY
  exact hY'.trans_le (measureReal_mono hsubset hfinite)

/--
Pointwise Bellotti-edge specialization.  The hypotheses expose exactly the
two inputs supplied outside this module:

* Bellotti's distinct-location count at `sigma = 1 - B * g(R * gamma)`;
* the elementary VK-scale comparison
  `A * g(gamma) < B * g(R * gamma)`.

No multiplicity convention is imposed on the external count.
-/
theorem
    eventually_exists_psiError_in_powerOnePlusEpsilonWindow_gt_of_bellottiEdgeCount
    {ε A B : ℝ} {rho : ℂ} {M : ℕ}
    (hε : 0 < ε)
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hedge :
      1 - A * vinogradovKorobovEdgeWidth rho.im ≤ rho.re)
    (hscale :
      A * vinogradovKorobovEdgeWidth rho.im <
        B * vinogradovKorobovEdgeWidth
          (((2 * M + 2 : ℕ) : ℝ) * rho.im))
    (hcount :
      bellottiZeroLocationCount
          (1 - B * vinogradovKorobovEdgeWidth
            (((2 * M + 2 : ℕ) : ℝ) * rho.im))
          (((2 * M + 2 : ℕ) : ℝ) * rho.im) ≤ M) :
    ∀ᶠ Y : ℝ in atTop,
      ∃ x ∈ powerOnePlusEpsilonWindow ε Y,
        (analyticOrderNatAt riemannZeta rho : ℝ) *
              finiteStrictPiOverTwoOscillationConstant M *
              (x ^ rho.re / ‖rho‖) <
            |chebyshevPsi x - x| := by
  have hσrho :
      1 - B * vinogradovKorobovEdgeWidth
          (((2 * M + 2 : ℕ) : ℝ) * rho.im) <
        rho.re := by
    have :
        1 - B * vinogradovKorobovEdgeWidth
            (((2 * M + 2 : ℕ) : ℝ) * rho.im) <
          1 - A * vinogradovKorobovEdgeWidth rho.im := by
      linarith
    exact this.trans_le hedge
  exact
    eventually_exists_psiError_in_powerOnePlusEpsilonWindow_gt_uniformBellottiGap
      hε hrhoRe0 hrhoRe1 hgamma hzero hσrho hcount

/--
Positive-measure counterpart of the pointwise Bellotti-edge specialization.
The strict constant depends only on the location-count budget `M`.
-/
theorem
    eventually_positive_measure_in_epsilonLogWindow_gt_of_bellottiEdgeCount
    {ε A B : ℝ} {rho : ℂ} {M : ℕ}
    (hε : 0 < ε)
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hedge :
      1 - A * vinogradovKorobovEdgeWidth rho.im ≤ rho.re)
    (hscale :
      A * vinogradovKorobovEdgeWidth rho.im <
        B * vinogradovKorobovEdgeWidth
          (((2 * M + 2 : ℕ) : ℝ) * rho.im))
    (hcount :
      bellottiZeroLocationCount
          (1 - B * vinogradovKorobovEdgeWidth
            (((2 * M + 2 : ℕ) : ℝ) * rho.im))
          (((2 * M + 2 : ℕ) : ℝ) * rho.im) ≤ M) :
    ∀ᶠ Y : ℝ in atTop,
      0 <
        volume.real
          {y ∈ Icc (Real.log Y) ((1 + ε) * Real.log Y) |
            (analyticOrderNatAt riemannZeta rho : ℝ) *
                finiteStrictPiOverTwoOscillationConstant M <
              |normalizedPsiError rho y|} := by
  have hσrho :
      1 - B * vinogradovKorobovEdgeWidth
          (((2 * M + 2 : ℕ) : ℝ) * rho.im) <
        rho.re := by
    have :
        1 - B * vinogradovKorobovEdgeWidth
            (((2 * M + 2 : ℕ) : ℝ) * rho.im) <
          1 - A * vinogradovKorobovEdgeWidth rho.im := by
      linarith
    exact this.trans_le hedge
  exact
    eventually_positive_measure_in_epsilonLogWindow_gt_uniformBellottiGap
      hε hrhoRe0 hrhoRe1 hgamma hzero hσrho hcount

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
