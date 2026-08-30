import HardyTheorem.OscillatoryGammaLowerTail
import HardyTheorem.OscillatoryGammaBoundaryFormula

/-! Exact Gamma replacement of the positive-frequency Mellin hard core. -/

open Complex MeasureTheory Filter Topology
open HardyTheorem.OscillatoryGammaTail
open HardyTheorem.OscillatoryGammaBoundaryFormula

namespace HardyTheorem.AFE

private theorem positiveWhole_eq_lower_add_boundary {z : ℂ} {c : ℝ}
    (hz1 : z.re < 1) (hc : 0 < c) :
    oscillatoryGammaPosWhole z c =
      (∫ u in (0 : ℝ)..1, (u : ℂ) ^ (z - 1) * Complex.exp (I * (c * u))) +
        oscillatoryGammaBoundary z c := by
  have hlim : Tendsto (oscillatoryGammaPosFullPartial z c) atTop
      (𝓝 ((∫ u in (0 : ℝ)..1,
        (u : ℂ) ^ (z - 1) * Complex.exp (I * (c * u))) +
          oscillatoryGammaBoundary z c)) := by
    exact tendsto_const_nhds.add (tendsto_oscillatoryGammaPartial_atTop hz1 hc)
  exact tendsto_nhds_unique (tendsto_oscillatoryGammaPosFullPartial_atTop hz1 hc) hlim

/-- The hard core differs from the canonical conditional Gamma value by
the lower endpoint tail and the uniform nonstationary upper tail. -/
theorem norm_oscillatoryGammaPosWhole_sub_mellinCore_le
    {sigma c t x : ℝ} {N : ℕ} (hs0 : 0 < sigma) (hs1 : sigma < 1)
    (hc : 0 < c) (hx : 0 < x) (hgap : c * x < t)
    (hN : 1 ≤ N) (hfar : 2 * t ≤ c * (N : ℝ)) :
    let s : ℂ := (sigma : ℂ) + I * t
    ‖oscillatoryGammaPosWhole (1 - s) c -
      ∫ u in x..(N : ℝ), (u : ℂ) ^ (-s) * Complex.exp (I * (c * u))‖ ≤
        2 * x ^ (1 - sigma) / (t - c * x) + 8 * (N : ℝ) ^ (-sigma) / c := by
  let s : ℂ := (sigma : ℂ) + I * t
  let z : ℂ := 1 - s
  let f : ℝ → ℂ := fun u => (u : ℂ) ^ (-s) * Complex.exp (I * (c * u))
  have hz1 : z.re < 1 := by simp [z, s]; linarith
  have hzpow : z - 1 = -s := by dsimp only [z]; ring
  have hzre : z.re - 1 = -sigma := by simp [z, s]
  have hzim : z.im = -t := by simp [z, s]
  have ht : 0 < t := (mul_pos hc hx).trans hgap
  have hi (a b : ℝ) : IntervalIntegrable f volume a b := by
    apply (intervalIntegral.intervalIntegrable_cpow' (r := -s)
      (by simp [s]; linarith)).mul_continuousOn
    fun_prop
  have hwhole := positiveWhole_eq_lower_add_boundary hz1 hc
  rw [hzpow] at hwhole
  have hpartial : oscillatoryGammaPartial z c N = ∫ u in (1 : ℝ)..(N : ℝ), f u := by
    simp only [oscillatoryGammaPartial, hzpow, f]
  have hdecomp : oscillatoryGammaPosWhole z c - (∫ u in x..(N : ℝ), f u) =
      (oscillatoryGammaBoundary z c - oscillatoryGammaPartial z c N) +
        (∫ u in (0 : ℝ)..x, f u) := by
    rw [hwhole, hpartial]
    change (∫ u in (0 : ℝ)..1, f u) + oscillatoryGammaBoundary z c -
      (∫ u in x..(N : ℝ), f u) =
        (oscillatoryGammaBoundary z c - (∫ u in (1 : ℝ)..(N : ℝ), f u)) +
          (∫ u in (0 : ℝ)..x, f u)
    have h01N := intervalIntegral.integral_add_adjacent_intervals (hi 0 1) (hi 1 N)
    have h0xN := intervalIntegral.integral_add_adjacent_intervals (hi 0 x) (hi x N)
    linear_combination h01N - h0xN
  have hupper : ‖oscillatoryGammaBoundary z c - oscillatoryGammaPartial z c N‖ ≤
      8 * (N : ℝ) ^ (-sigma) / c := by
    have htime : 2 * |z.im| ≤ c * (N : ℝ) := by
      simpa only [hzim, abs_neg, abs_of_pos ht] using hfar
    simpa only [hzre] using norm_oscillatoryGammaBoundary_sub_partial_le hz1 hc hN htime
  have hlower : ‖∫ u in (0 : ℝ)..x, f u‖ ≤
      2 * x ^ (1 - sigma) / (t - c * x) :=
    norm_intervalIntegral_mellin_linear_zero_lower_le hs1 hc.le hx hgap
  change ‖oscillatoryGammaPosWhole z c - (∫ u in x..(N : ℝ), f u)‖ ≤ _
  rw [hdecomp]
  calc
    _ ≤ ‖oscillatoryGammaBoundary z c - oscillatoryGammaPartial z c N‖ +
        ‖∫ u in (0 : ℝ)..x, f u‖ := norm_add_le _ _
    _ ≤ 8 * (N : ℝ) ^ (-sigma) / c + 2 * x ^ (1 - sigma) / (t - c * x) :=
      add_le_add hupper hlower
    _ = _ := add_comm _ _

/-- Exact positive-frequency Gamma coefficient, with the correct phase sign.
The frequency will be `c=2*pi*m` for the negative Poisson index `-m`. -/
theorem norm_mellinCore_sub_gammaValue_le
    {sigma c t x : ℝ} {N : ℕ} (hs0 : 0 < sigma) (hs1 : sigma < 1)
    (hc : 0 < c) (hx : 0 < x) (hgap : c * x < t)
    (hN : 1 ≤ N) (hfar : 2 * t ≤ c * (N : ℝ)) :
    let s : ℂ := (sigma : ℂ) + I * t
    ‖(∫ u in x..(N : ℝ), (u : ℂ) ^ (-s) * Complex.exp (I * (c * u))) -
      (c : ℂ) ^ (s - 1) *
        (Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ) * (1 - s)) * Complex.Gamma (1 - s))‖ ≤
      2 * x ^ (1 - sigma) / (t - c * x) + 8 * (N : ℝ) ^ (-sigma) / c := by
  let s : ℂ := (sigma : ℂ) + I * t
  have hz0 : 0 < (1 - s).re := by simp [s]; linarith
  have hz1 : (1 - s).re < 1 := by simp [s]; linarith
  have h := norm_oscillatoryGammaPosWhole_sub_mellinCore_le hs0 hs1 hc hx hgap hN hfar
  change ‖oscillatoryGammaPosWhole (1 - s) c -
    (∫ u in x..(N : ℝ), (u : ℂ) ^ (-s) * Complex.exp (I * (c * u)))‖ ≤ _ at h
  rw [oscillatoryGammaPosWhole_eq_of_pos hz0 hz1 hc,
    show -(1 - s) = s - 1 by ring, norm_sub_rev] at h
  exact h

end HardyTheorem.AFE
