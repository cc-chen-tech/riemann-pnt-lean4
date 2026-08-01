import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicCompactAnnulus

namespace PrimeNumberTheorem

open Complex Set

/-- On every fixed finite-height segment of the imaginary axis, zeta is
analytic and nonzero.  Compactness therefore supplies a uniform right-hand
thickening on which the actual logarithmic derivative is bounded. -/
theorem exists_norm_logDeriv_riemannZeta_bound_on_right_thickening_of_imaginary_segment
    (T : ℝ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ σ t : ℝ, 0 ≤ σ → σ ≤ δ → |t| ≤ T →
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ C := by
  let K : Set ℂ := Set.Icc (0 : ℝ) 0 ×ℂ Set.Icc (-T) T
  let U : Set ℂ := {z | AnalyticAt ℂ (logDeriv riemannZeta) z}
  have hK : IsCompact K := by
    simpa [K] using
      ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 0)).reProdIm
        (isCompact_Icc : IsCompact (Set.Icc (-T) T)))
  have hUopen : IsOpen U := by
    simpa [U] using (isOpen_analyticAt ℂ (logDeriv riemannZeta))
  have hKU : K ⊆ U := by
    intro z hz
    change z ∈ Set.Icc (0 : ℝ) 0 ×ℂ Set.Icc (-T) T at hz
    rw [mem_reProdIm] at hz
    have hre0 : z.re = 0 := le_antisymm hz.1.2 hz.1.1
    have hz1 : z ≠ 1 := by
      intro hz1
      have hre := congrArg Complex.re hz1
      simp [hre0] at hre
    have htrivial : ∀ n : ℕ, z ≠ -2 * ((n : ℂ) + 1) := by
      intro n hn
      have hre := congrArg Complex.re hn
      simp [hre0] at hre
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hzeta : riemannZeta z ≠ 0 :=
      PrimeNumberTheorem.riemannZeta_ne_zero_of_re_le_zero hre0.le htrivial
    exact ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero
      z hz1 hzeta
  rcases hK.exists_cthickening_subset_open hUopen hKU with
    ⟨δ, hδ, hδU⟩
  have hKδ : IsCompact (Metric.cthickening δ K) := hK.cthickening
  have hcont : ContinuousOn (fun z : ℂ => ‖logDeriv riemannZeta z‖)
      (Metric.cthickening δ K) := by
    intro z hz
    exact (hδU hz).continuousAt.norm.continuousWithinAt
  rcases hKδ.bddAbove_image hcont with ⟨C0, hC0⟩
  let C : ℝ := max C0 0
  refine ⟨δ, C, hδ, le_max_right _ _, ?_⟩
  intro σ t hσ0 hσδ ht
  let z : ℂ := (σ : ℂ) + I * t
  let y : ℂ := I * t
  have hyK : y ∈ K := by
    change y ∈ Set.Icc (0 : ℝ) 0 ×ℂ Set.Icc (-T) T
    rw [mem_reProdIm]
    constructor
    · simp [y]
    · have him := abs_le.mp ht
      simpa [y] using him
  have hdist : dist z y ≤ δ := by
    rw [dist_eq_norm]
    have hsub : z - y = (σ : ℂ) := by
      apply Complex.ext <;> simp [z, y]
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ0]
    exact hσδ
  have hzKδ : z ∈ Metric.cthickening δ K :=
    Metric.mem_cthickening_of_dist_le z y δ K hyK hdist
  have hzBound : ‖logDeriv riemannZeta z‖ ≤ C0 :=
    hC0 ⟨z, hzKδ, rfl⟩
  exact hzBound.trans (le_max_left _ _)

end PrimeNumberTheorem
