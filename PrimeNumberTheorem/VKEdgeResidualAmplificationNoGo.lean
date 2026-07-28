import PrimeNumberTheorem.VKEdgeCosineModelAnnihilator

open MeasureTheory Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# A single-pair obstruction to residual amplification

The existing local second-moment lower bound does not by itself force another
zero frequency. A single cosine pair already has linear local `L²` energy,
while the frequency-tuned symmetric annihilator kills it identically.
-/

/-- Lower companion to `integral_Icc_cosinePairModel_sq_le`. -/
theorem integral_Icc_cosinePairModel_sq_ge
    {m gamma phase a b : ℝ}
    (hab : a ≤ b) (hgamma : gamma ≠ 0) :
    2 * m ^ 2 * (b - a) - 2 * m ^ 2 / |gamma| ≤
      ∫ y in Icc a b, cosinePairModel m gamma phase y ^ 2 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab,
    intervalIntegral_cosinePairModel_sq hgamma]
  let delta : ℝ :=
    Real.sin (2 * gamma * b - 2 * phase) -
      Real.sin (2 * gamma * a - 2 * phase)
  have hdelta : |delta| ≤ 2 := by
    dsimp [delta]
    calc
      |Real.sin (2 * gamma * b - 2 * phase) -
          Real.sin (2 * gamma * a - 2 * phase)| ≤
          |Real.sin (2 * gamma * b - 2 * phase)| +
            |Real.sin (2 * gamma * a - 2 * phase)| :=
        abs_sub _ _
      _ ≤ 1 + 1 :=
        add_le_add (Real.abs_sin_le_one _)
          (Real.abs_sin_le_one _)
      _ = 2 := by norm_num
  have hgammaAbs : 0 < |gamma| := abs_pos.mpr hgamma
  have habs :
      |m ^ 2 / gamma * delta| =
        m ^ 2 / |gamma| * |delta| := by
    rw [abs_mul, abs_div, abs_pow, sq_abs]
  have htermAbs :
      |m ^ 2 / gamma * delta| ≤
        2 * m ^ 2 / |gamma| := by
    rw [habs]
    calc
      m ^ 2 / |gamma| * |delta| ≤
          m ^ 2 / |gamma| * 2 :=
        mul_le_mul_of_nonneg_left hdelta
          (div_nonneg (sq_nonneg m) hgammaAbs.le)
      _ = 2 * m ^ 2 / |gamma| := by ring
  have htermLower :
      -(2 * m ^ 2 / |gamma|) ≤
        m ^ 2 / gamma * delta := by
    linarith [neg_abs_le (m ^ 2 / gamma * delta)]
  dsimp [delta] at htermLower
  linarith

/--
On every interval longer than two reciprocal frequencies, one cosine pair
already supplies a linear local second moment.
-/
theorem integral_Icc_cosinePairModel_sq_ge_linear
    {m gamma phase a b : ℝ}
    (hab : a ≤ b) (hgamma : gamma ≠ 0)
    (hlength : 2 / |gamma| ≤ b - a) :
    m ^ 2 * (b - a) ≤
      ∫ y in Icc a b, cosinePairModel m gamma phase y ^ 2 := by
  have hbase :=
    integral_Icc_cosinePairModel_sq_ge
      (m := m) (gamma := gamma) (phase := phase) hab hgamma
  have hscaled :=
    mul_le_mul_of_nonneg_left hlength (sq_nonneg m)
  have hcost :
      2 * m ^ 2 / |gamma| ≤ m ^ 2 * (b - a) := by
    calc
      2 * m ^ 2 / |gamma| = m ^ 2 * (2 / |gamma|) := by ring
      _ ≤ m ^ 2 * (b - a) := hscaled
  linarith

/--
No-go theorem for the current amplification strategy: linear local energy is
compatible with a pure target cosine pair, but the tuned annihilator has
exactly zero energy. Therefore a local `L²` lower bound alone cannot force an
additional zero frequency.
-/
theorem pureCosineModel_linearEnergy_and_annihilator_zero
    {m gamma phase a b h : ℝ}
    (hab : a ≤ b) (hgamma : gamma ≠ 0)
    (hlength : 2 / |gamma| ≤ b - a) :
    m ^ 2 * (b - a) ≤
        ∫ y in Icc a b,
          cosinePairModel m gamma phase y ^ 2 ∧
      (∫ y in Icc a b,
        symmetricFrequencyAnnihilator h gamma
          (cosinePairModel m gamma phase) y ^ 2) = 0 := by
  constructor
  · exact
      integral_Icc_cosinePairModel_sq_ge_linear
        hab hgamma hlength
  · simp_rw [symmetricFrequencyAnnihilator_cosineModelPair_eq_zero]
    simp

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
