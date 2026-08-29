import HardyTheorem.AFEExplicitPlateauCutoff
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Derivatives of the explicit compact Mellin amplitude

This file records the exact first and second derivatives of
`w_{x,N}(u) u^{-sigma}` on the positive support interval.  The amplitude is
kept real until the final `ofReal` embedding, so all size estimates can use
ordinary absolute values.
-/

noncomputable section

namespace HardyTheorem
namespace AFE

noncomputable def mellinRpow (sigma u : ℝ) : ℝ :=
  u ^ (-sigma)

noncomputable def mellinRpowDeriv (sigma u : ℝ) : ℝ :=
  (-sigma) * u ^ (-sigma - 1)

noncomputable def mellinRpowSecondDeriv (sigma u : ℝ) : ℝ :=
  (-sigma) * ((-sigma - 1) * u ^ (-sigma - 1 - 1))

theorem mellinRpowSecondDeriv_eq (sigma u : ℝ) :
    mellinRpowSecondDeriv sigma u =
      (-sigma) * (-sigma - 1) * u ^ (-sigma - 2) := by
  rw [mellinRpowSecondDeriv]
  have hexp : -sigma - 1 - 1 = -sigma - 2 := by ring
  rw [hexp]
  ring

theorem mellinRpow_hasDerivAt {sigma u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (mellinRpow sigma) (mellinRpowDeriv sigma u) u := by
  simpa only [mellinRpow, mellinRpowDeriv] using!
    (Real.hasDerivAt_rpow_const (x := u) (p := -sigma) (Or.inl hu))

theorem mellinRpowDeriv_hasDerivAt {sigma u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (mellinRpowDeriv sigma) (mellinRpowSecondDeriv sigma u) u := by
  have h := (Real.hasDerivAt_rpow_const
    (x := u) (p := -sigma - 1) (Or.inl hu)).const_mul (-sigma)
  simpa only [mellinRpowDeriv, mellinRpowSecondDeriv] using! h

noncomputable def explicitMellinAmplitude
    (sigma x N u : ℝ) : ℝ :=
  explicitIntervalPlateau x N u * mellinRpow sigma u

noncomputable def explicitMellinAmplitudeDeriv
    (sigma x N u : ℝ) : ℝ :=
  explicitIntervalPlateauDeriv x N u * mellinRpow sigma u +
    explicitIntervalPlateau x N u * mellinRpowDeriv sigma u

noncomputable def explicitMellinAmplitudeSecondDeriv
    (sigma x N u : ℝ) : ℝ :=
  explicitIntervalPlateauSecondDeriv x N u * mellinRpow sigma u +
    2 * explicitIntervalPlateauDeriv x N u * mellinRpowDeriv sigma u +
    explicitIntervalPlateau x N u * mellinRpowSecondDeriv sigma u

theorem explicitMellinAmplitude_hasDerivAt
    (sigma x N : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (explicitMellinAmplitude sigma x N)
      (explicitMellinAmplitudeDeriv sigma x N u) u := by
  simpa only [explicitMellinAmplitude, explicitMellinAmplitudeDeriv] using!
    (explicitIntervalPlateau_hasDerivAt x N u).mul
      (mellinRpow_hasDerivAt (sigma := sigma) hu)

theorem explicitMellinAmplitudeDeriv_hasDerivAt
    (sigma x N : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (explicitMellinAmplitudeDeriv sigma x N)
      (explicitMellinAmplitudeSecondDeriv sigma x N u) u := by
  have h₁ := (explicitIntervalPlateauDeriv_hasDerivAt x N u).mul
    (mellinRpow_hasDerivAt (sigma := sigma) hu)
  have h₂ := (explicitIntervalPlateau_hasDerivAt x N u).mul
    (mellinRpowDeriv_hasDerivAt (sigma := sigma) hu)
  convert! h₁.add h₂ using 1
  simp [explicitMellinAmplitudeSecondDeriv]
  ring

/-- The complex amplitude used in the Fourier phase integral. -/
noncomputable def explicitComplexMellinAmplitude
    (sigma x N u : ℝ) : ℂ :=
  explicitMellinAmplitude sigma x N u

noncomputable def explicitComplexMellinAmplitudeDeriv
    (sigma x N u : ℝ) : ℂ :=
  explicitMellinAmplitudeDeriv sigma x N u

noncomputable def explicitComplexMellinAmplitudeSecondDeriv
    (sigma x N u : ℝ) : ℂ :=
  explicitMellinAmplitudeSecondDeriv sigma x N u

theorem explicitComplexMellinAmplitude_hasDerivAt
    (sigma x N : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (explicitComplexMellinAmplitude sigma x N)
      (explicitComplexMellinAmplitudeDeriv sigma x N u) u := by
  simpa only [explicitComplexMellinAmplitude,
    explicitComplexMellinAmplitudeDeriv] using!
    (explicitMellinAmplitude_hasDerivAt sigma x N hu).ofReal_comp

theorem explicitComplexMellinAmplitudeDeriv_hasDerivAt
    (sigma x N : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (explicitComplexMellinAmplitudeDeriv sigma x N)
      (explicitComplexMellinAmplitudeSecondDeriv sigma x N u) u := by
  simpa only [explicitComplexMellinAmplitudeDeriv,
    explicitComplexMellinAmplitudeSecondDeriv] using!
    (explicitMellinAmplitudeDeriv_hasDerivAt sigma x N hu).ofReal_comp

end AFE
end HardyTheorem
