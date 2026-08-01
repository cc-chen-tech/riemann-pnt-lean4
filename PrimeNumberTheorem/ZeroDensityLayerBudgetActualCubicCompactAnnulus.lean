import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicDynamicLeftPole

namespace PrimeNumberTheorem

open Complex Set

/-- A fixed positive-height annulus on `Re s = 1` has a uniform zero-free
thickening to its left, and `logDeriv zeta` is uniformly bounded there.  This
is the compact complement of the punctured pole ball in the low-height part
of the dynamic cubic left edge. -/
theorem exists_norm_logDeriv_riemannZeta_bound_on_left_thickening_of_unit_annulus
    {R T : ℝ} (hR : 0 < R) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ σ t : ℝ, 1 - δ ≤ σ → σ ≤ 1 →
        R ≤ |t| → |t| ≤ T →
          ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ C := by
  let K : Set ℂ :=
    Set.Icc (1 : ℝ) 1 ×ℂ (Set.Icc R T ∪ Set.Icc (-T) (-R))
  let U : Set ℂ := {z | AnalyticAt ℂ (logDeriv riemannZeta) z}
  have hK : IsCompact K := by
    have him : IsCompact (Set.Icc R T ∪ Set.Icc (-T) (-R)) :=
      (isCompact_Icc : IsCompact (Set.Icc R T)).union
        (isCompact_Icc : IsCompact (Set.Icc (-T) (-R)))
    simpa [K] using
      ((isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 1)).reProdIm him)
  have hUopen : IsOpen U := by
    simpa [U] using (isOpen_analyticAt ℂ (logDeriv riemannZeta))
  have hKU : K ⊆ U := by
    intro z hz
    change z ∈ Set.Icc (1 : ℝ) 1 ×ℂ
      (Set.Icc R T ∪ Set.Icc (-T) (-R)) at hz
    rw [mem_reProdIm] at hz
    have hre : 1 ≤ z.re := hz.1.1
    have himAbs : R ≤ |z.im| := by
      rcases hz.2 with hpos | hneg
      · have himNonneg : 0 ≤ z.im := by linarith [hpos.1, hR]
        simpa [abs_of_nonneg himNonneg] using hpos.1
      · have himNonpos : z.im ≤ 0 := by linarith [hneg.2, hR]
        rw [abs_of_nonpos himNonpos]
        linarith [hneg.2]
    have hz1 : z ≠ 1 := by
      intro hz1
      have him0 := congrArg Complex.im hz1
      simp at him0
      rw [him0, abs_zero] at himAbs
      linarith
    exact ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_one_le_re_of_ne_one
      hre hz1
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
  intro σ t hσlower hσupper htLower htUpper
  let z : ℂ := (σ : ℂ) + I * t
  let y : ℂ := (1 : ℂ) + I * t
  have hyK : y ∈ K := by
    change y ∈ Set.Icc (1 : ℝ) 1 ×ℂ
      (Set.Icc R T ∪ Set.Icc (-T) (-R))
    rw [mem_reProdIm]
    constructor
    · simp [y]
    · by_cases htNonneg : 0 ≤ t
      · left
        constructor
        · simpa [y, abs_of_nonneg htNonneg] using htLower
        · simpa [y, abs_of_nonneg htNonneg] using htUpper
      · right
        have htNonpos : t ≤ 0 := le_of_lt (lt_of_not_ge htNonneg)
        constructor
        · have : -T ≤ t := by
            rw [abs_of_nonpos htNonpos] at htUpper
            linarith
          simpa [y] using this
        · have : t ≤ -R := by
            rw [abs_of_nonpos htNonpos] at htLower
            linarith
          simpa [y] using this
  have hdist : dist z y ≤ δ := by
    rw [dist_eq_norm]
    have hsub : z - y = ((σ - 1 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [z, y]
    rw [hsub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have hzKδ : z ∈ Metric.cthickening δ K :=
    Metric.mem_cthickening_of_dist_le z y δ K hyK hdist
  have hzBound : ‖logDeriv riemannZeta z‖ ≤ C0 :=
    hC0 ⟨z, hzKδ, rfl⟩
  exact hzBound.trans (le_max_left _ _)

end PrimeNumberTheorem
