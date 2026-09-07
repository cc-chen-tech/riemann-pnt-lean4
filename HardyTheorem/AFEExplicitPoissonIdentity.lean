import HardyTheorem.AFEExplicitPoissonFarTail

/-! Poisson summation for exactly the quantitative width-one cutoff. -/

noncomputable section

open Complex Filter Set MeasureTheory
open scoped FourierTransform SchwartzMap Topology

namespace HardyTheorem.AFE

noncomputable def explicitWeightedPoissonCutoff (s : ℂ) (x N u : ℝ) : ℂ :=
  (explicitIntervalPlateau x N u : ℂ) * Complex.exp (-s * (Real.log u : ℂ))

theorem explicitWeightedPoissonCutoff_hasCompactSupport (s : ℂ) (x N : ℝ) :
    HasCompactSupport (explicitWeightedPoissonCutoff s x N) := by
  have h : HasCompactSupport (fun u : ℝ => (explicitIntervalPlateau x N u : ℂ)) :=
    (explicitIntervalPlateau_hasCompactSupport x N).comp_left Complex.ofReal_zero
  exact h.mul_right

/-- The apparent logarithmic singularity is killed on a neighborhood of zero. -/
theorem explicitWeightedPoissonCutoff_contDiff (s : ℂ) {x N : ℝ} (hx : 1 < x) :
    ContDiff ℝ (⊤ : ℕ∞) (explicitWeightedPoissonCutoff s x N) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u = 0
  · subst u
    apply (contDiffAt_const (x := (0 : ℝ)) (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < x - 1 by linarith)] with v hv
    simp [explicitWeightedPoissonCutoff, explicitIntervalPlateau_eq_zero_of_le hv.le]
  · have hb : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun v : ℝ => (explicitIntervalPlateau x N v : ℂ)) u :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp u
        (explicitIntervalPlateau_contDiff x N).contDiffAt
    have hlog : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : ℝ => (Real.log v : ℂ)) u :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp u (Real.contDiffAt_log.mpr hu)
    exact hb.mul ((contDiffAt_const.mul hlog).cexp)

theorem explicitWeightedPoissonCutoff_eq_cpow (s : ℂ) {x N u : ℝ}
    (hx : 0 < x) (hu : u ∈ Icc x N) :
    explicitWeightedPoissonCutoff s x N u = (u : ℂ) ^ (-s) := by
  have hu0 : 0 < u := hx.trans_le hu.1
  rw [explicitWeightedPoissonCutoff, explicitIntervalPlateau_eq_one hu,
    ofReal_one, one_mul, Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hu0.ne')]
  rw [Complex.ofReal_log hu0.le]
  congr 1
  ring

theorem explicitWeightedPoissonCutoff_fourierIntegrand_eq
    (sigma t x N u : ℝ) (k : ℤ) (hu : 0 < u) :
    Complex.exp ((-2 * Real.pi * u * (k : ℝ) : ℝ) * I) •
        explicitWeightedPoissonCutoff ((sigma : ℂ) + I * t) x N u =
      explicitComplexMellinAmplitude sigma x N u *
        Complex.exp (I * weightedPoissonPhase t k u) := by
  rw [explicitWeightedPoissonCutoff, explicitComplexMellinAmplitude,
    explicitMellinAmplitude, mellinRpow, Real.rpow_def_of_pos hu]
  simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]
  let A : ℂ := Complex.exp (-(2 : ℂ) * Real.pi * u * (k : ℂ) * I)
  let B : ℂ := Complex.exp (-((sigma : ℂ) + I * t) * (Real.log u : ℂ))
  let C : ℂ := Complex.exp ((Real.log u : ℂ) * (-sigma : ℂ))
  let D : ℂ := Complex.exp (I * (weightedPoissonPhase t k u : ℂ))
  let b : ℂ := explicitIntervalPlateau x N u
  change A * (b * B) = b * C * D
  calc
    A * (b * B) = b * (A * B) := by ring
    _ = b * (C * D) := by
      congr 1
      dsimp only [A, B, C, D]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      apply Complex.ext <;> simp [weightedPoissonPhase] <;> ring
    _ = b * C * D := by ring

theorem fourier_explicitWeightedPoissonCutoff_eq_mode
    (sigma t : ℝ) {x N : ℝ} (hx : 1 < x) (hxN : x ≤ N) (k : ℤ) :
    𝓕 (explicitWeightedPoissonCutoff ((sigma : ℂ) + I * t) x N) k =
      explicitPoissonMode sigma x N t k := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hsupport : Function.support
      (fun u : ℝ => Complex.exp ((-2 * Real.pi * u * (k : ℝ) : ℝ) * I) •
        explicitWeightedPoissonCutoff ((sigma : ℂ) + I * t) x N u) ⊆
      Ioc (x - 1) (N + 1) := by
    intro u hu
    have hleft : x - 1 < u := by
      apply lt_of_not_ge
      intro hul
      apply hu
      simp [explicitWeightedPoissonCutoff, explicitIntervalPlateau_eq_zero_of_le hul]
    have hright : u < N + 1 := by
      apply lt_of_not_ge
      intro hur
      apply hu
      simp [explicitWeightedPoissonCutoff, explicitIntervalPlateau_eq_zero_of_ge hur]
    exact ⟨hleft, hright.le⟩
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupport]
  unfold explicitPoissonMode
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc (x - 1) (N + 1) := by
    simpa only [uIcc_of_le (show x - 1 ≤ N + 1 by linarith)] using hu
  exact explicitWeightedPoissonCutoff_fourierIntegrand_eq sigma t x N u k
    (by linarith [hu'.1])

/-- Poisson summation for the exact function whose distant modes were bounded. -/
theorem explicitWeightedPoissonCutoff_tsum_eq_mode_tsum
    (sigma t : ℝ) {x N : ℝ} (hx : 1 < x) (hxN : x ≤ N) :
    (∑' n : ℤ, explicitWeightedPoissonCutoff ((sigma : ℂ) + I * t) x N n) =
      ∑' k : ℤ, explicitPoissonMode sigma x N t k := by
  let s : ℂ := (sigma : ℂ) + I * t
  let F : 𝓢(ℝ, ℂ) :=
    (explicitWeightedPoissonCutoff_hasCompactSupport s x N).toSchwartzMap
      (explicitWeightedPoissonCutoff_contDiff s hx)
  have h := SchwartzMap.tsum_eq_tsum_fourier F 0
  simp_rw [SchwartzMap.fourier_coe] at h
  have hpoisson : (∑' n : ℤ, explicitWeightedPoissonCutoff s x N n) =
      ∑' n : ℤ, 𝓕 (explicitWeightedPoissonCutoff s x N) n := by
    change (∑' n : ℤ, F n) = ∑' n : ℤ, 𝓕 (F : ℝ → ℂ) n
    simpa using h
  exact hpoisson.trans (tsum_congr fun k =>
    fourier_explicitWeightedPoissonCutoff_eq_mode sigma t hx hxN k)

/-- The width-one transitions contain no additional nonzero integer terms. -/
theorem explicitWeightedPoissonCutoff_tsum_eq_core (s : ℂ) {m n : ℕ}
    (hm : 1 < m) (_hmn : m ≤ n) :
    (∑' k : ℤ, explicitWeightedPoissonCutoff s m n k) =
      ∑ k ∈ Finset.Icc (m : ℤ) n, (k : ℂ) ^ (-s) := by
  calc
    _ = ∑ k ∈ Finset.Icc (m : ℤ) n, explicitWeightedPoissonCutoff s m n k := by
      apply tsum_eq_sum
      intro k hk
      by_cases hlow : k < (m : ℤ)
      · have hkZ : k ≤ (m : ℤ) - 1 := by omega
        have hkR : (k : ℝ) ≤ (m : ℝ) - 1 := by exact_mod_cast hkZ
        simp [explicitWeightedPoissonCutoff, explicitIntervalPlateau_eq_zero_of_le hkR]
      · have hkZ : (n : ℤ) + 1 ≤ k := by
          simp only [Finset.mem_Icc] at hk
          omega
        have hkR : (n : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hkZ
        simp [explicitWeightedPoissonCutoff, explicitIntervalPlateau_eq_zero_of_ge hkR]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkR : (k : ℝ) ∈ Icc (m : ℝ) n := by
        rcases Finset.mem_Icc.mp hk with ⟨hkm, hkn⟩
        exact ⟨by exact_mod_cast hkm, by exact_mod_cast hkn⟩
      simpa only [Complex.ofReal_intCast] using
        explicitWeightedPoissonCutoff_eq_cpow s
          (show 0 < (m : ℝ) by exact_mod_cast (show 0 < m by omega)) hkR

end HardyTheorem.AFE
