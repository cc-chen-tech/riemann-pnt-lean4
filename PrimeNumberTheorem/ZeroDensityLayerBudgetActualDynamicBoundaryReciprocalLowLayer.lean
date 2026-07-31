import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryAutomaticLowLayer

/-!
# Reciprocal-mass low layer for a dynamic boundary

The older automatic low-layer proof bounds every reciprocal zero denominator
by one fixed constant and then counts all zeros up to height `H`.  This costs a
factor `H`, hence one full polynomial-height exponent.

Here the denominator is retained inside the sum.  The global
multiplicity-weighted reciprocal-zero estimate is only `O(log^2 H)`, so the
normalized low layer has power `x^(sigma - beta)` rather than
`x^(sigma - beta + alpha)`.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Complex Filter

noncomputable section

/-- A finite outside-cluster layer is controlled directly by the global
multiplicity-weighted reciprocal-zero mass, without a uniform norm guard. -/
theorem
    PositiveZeroOutsideClusterBucketInput.norm_layer_sum_le_rpow_mul_globalReciprocal
    {T : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n)
    (i : Fin n) {sigma x : ℝ}
    (hx : 1 ≤ x)
    (hre : ∀ rho ∈ input.layer i, rho.re ≤ sigma) :
    ‖∑ rho ∈ input.layer i, pntRelativeZeroContribution x rho‖ ≤
      x ^ (sigma - 1) *
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
  classical
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hxNonneg : 0 ≤ x := hxPos.le
  have hsubset : input.layer i ⊆ nontrivialZerosFinset T := by
    intro rho hrho
    have hOutside :=
      mem_positiveNontrivialZerosOutsideClusterFinset.mp
        (Finset.mem_filter.mp hrho).1
    apply mem_nontrivialZerosFinset.mpr
    refine ⟨hOutside.1, ?_⟩
    rw [abs_of_pos hOutside.2.1]
    exact hOutside.2.2.1
  have hmass :
      (∑ rho ∈ input.layer i,
          (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) ≤
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
    unfold ExplicitFormulaAux.globalReciprocalZeroMultiplicity
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun rho _ _ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg rho))
  calc
    ‖∑ rho ∈ input.layer i, pntRelativeZeroContribution x rho‖
        ≤ ∑ rho ∈ input.layer i,
            ‖pntRelativeZeroContribution x rho‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈ input.layer i,
          x ^ (sigma - 1) *
            ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) := by
      apply Finset.sum_le_sum
      intro rho hrho
      have hrpow : x ^ (rho.re - 1) ≤ x ^ (sigma - 1) :=
        Real.rpow_le_rpow_of_exponent_le hx (by linarith [hre rho hrho])
      have hmult : 0 ≤ (analyticOrderNatAt riemannZeta rho : ℝ) :=
        Nat.cast_nonneg _
      rw [norm_pntRelativeZeroContribution_eq_multiplicity_mul_norm,
        norm_pntRelativeSimpleZeroKernel_eq hxPos]
      calc
        (analyticOrderNatAt riemannZeta rho : ℝ) *
              (x ^ (rho.re - 1) / ‖rho‖)
            ≤ (analyticOrderNatAt riemannZeta rho : ℝ) *
                (x ^ (sigma - 1) / ‖rho‖) := by
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hrpow (norm_nonneg rho)) hmult
        _ = x ^ (sigma - 1) *
              ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) := by
          ring_nf
    _ = x ^ (sigma - 1) *
          (∑ rho ∈ input.layer i,
            (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) := by
      rw [Finset.mul_sum]
    _ ≤ x ^ (sigma - 1) *
          ExplicitFormulaAux.globalReciprocalZeroMultiplicity T :=
      mul_le_mul_of_nonneg_left hmass
        (Real.rpow_nonneg hxNonneg _)

/-- Polylogarithmic majorant for the reciprocal-mass normalized low layer. -/
noncomputable def actualReciprocalLowNormalizedLogPowerMajorant
    (C alpha beta sigma x : ℝ) : ℝ :=
  C * (alpha + 2) ^ 2 * x ^ (sigma - beta) *
    Real.log x ^ (8 : ℕ)

/-- A strict real-part gap absorbs the reciprocal low layer independently of
the polynomial selected-height exponent `alpha`. -/
theorem tendsto_actualReciprocalLowNormalizedLogPowerMajorant_zero
    {C alpha beta sigma epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + epsilon < 0) :
    Tendsto
      (actualReciprocalLowNormalizedLogPowerMajorant
        C alpha beta sigma)
      atTop (nhds 0) := by
  have hepsilonHalf : 0 < epsilon / 2 := by
    linarith
  have hmarginHalf :
      (sigma - beta) / 2 + epsilon / 2 < 0 := by
    linarith
  have hbase :
      Tendsto
        (fun x : ℝ =>
          x ^ ((sigma - beta) / 2) * Real.log x ^ (4 : ℕ))
        atTop (nhds 0) :=
    tendsto_rpow_mul_log_four_atTop_nhds_zero
      hepsilonHalf hmarginHalf
  have hsquare :
      Tendsto
        (fun x : ℝ =>
          (x ^ ((sigma - beta) / 2) * Real.log x ^ (4 : ℕ)) *
            (x ^ ((sigma - beta) / 2) * Real.log x ^ (4 : ℕ)))
        atTop (nhds 0) := by
    simpa using hbase.mul hbase
  have hconst :
      Tendsto (fun _ : ℝ => C * (alpha + 2) ^ 2) atTop
        (nhds (C * (alpha + 2) ^ 2)) :=
    tendsto_const_nhds
  have hscaled :
      Tendsto
        (fun x : ℝ =>
          (C * (alpha + 2) ^ 2) *
            ((x ^ ((sigma - beta) / 2) * Real.log x ^ (4 : ℕ)) *
              (x ^ ((sigma - beta) / 2) * Real.log x ^ (4 : ℕ))))
        atTop (nhds 0) := by
    simpa using hconst.mul hsquare
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold actualReciprocalLowNormalizedLogPowerMajorant
  have hrpow :
      x ^ (sigma - beta) =
        x ^ ((sigma - beta) / 2) * x ^ ((sigma - beta) / 2) := by
    rw [← Real.rpow_add hx]
    ring_nf
  rw [hrpow]
  ring_nf

/-- The canonical dynamic low layer is negligible under the improved margin
`sigma - beta + epsilon < 0`; the selected-height exponent affects only the
polylogarithmic coefficient. -/
theorem actualDynamicBoundaryCanonicalLowNormalizedSum_tendsto_zero_reciprocal
    {H : ℝ → ℝ} {beta sigma alpha epsilon : ℝ}
    (hHle :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hHtop : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + epsilon < 0) :
    Tendsto
      (actualDynamicBoundaryLowNormalizedSum H beta
        (actualDynamicBoundaryCanonicalTwoStripInput H beta sigma)
        (0 : Fin 2))
      atTop (nhds 0) := by
  rcases ExplicitFormulaAux.exists_globalReciprocalZeroMultiplicity_le_log_sq with
    ⟨C, hC, hglobal⟩
  have hlogReal :=
    eventually_one_add_log_polynomialHeight_add_six_le_log_four halpha
  have hlog :
      ∀ᶠ m : ℕ in atTop,
        1 + Real.log ((m : ℝ) ^ alpha + 6) ≤
          (alpha + 2) * Real.log (m : ℝ) ^ 4 :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hlogReal
  have hmajor :
      Tendsto
        (fun m : ℕ =>
          actualReciprocalLowNormalizedLogPowerMajorant
            C alpha beta sigma (m : ℝ))
        atTop (nhds 0) :=
    (tendsto_actualReciprocalLowNormalizedLogPowerMajorant_zero
      hepsilon hmargin).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact div_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le m)) _)
  · filter_upwards [
      eventually_ge_atTop (1 : ℕ),
      hHtop.eventually (eventually_ge_atTop (4 : ℝ)),
      hHle, hlog] with m hm hHfour hHupper hlogBound
    have hmPos : 0 < (m : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hm)
    have hmNonneg : 0 ≤ (m : ℝ) := hmPos.le
    have hAmplitude :
        0 < targetZeroPowerAmplitude beta (m : ℝ) :=
      Real.rpow_pos_of_pos hmPos _
    let input :=
      actualDynamicBoundaryCanonicalTwoStripInput H beta sigma m
    have hphysical :
        ‖∑ rho ∈ input.layer (0 : Fin 2),
            pntRelativeZeroContribution (m : ℝ) rho‖ ≤
          (m : ℝ) ^ (sigma - 1) *
            ExplicitFormulaAux.globalReciprocalZeroMultiplicity
              (H (m : ℝ)) := by
      exact input.norm_layer_sum_le_rpow_mul_globalReciprocal
        (0 : Fin 2)
        (by exact_mod_cast hm)
        (fun rho hrho =>
          actualDynamicBoundaryCanonicalTwoStripInput_low_re_le m hrho)
    have hglobalBound :
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity (H (m : ℝ)) ≤
          C * (1 + Real.log (H (m : ℝ) + 6)) ^ 2 :=
      hglobal (H (m : ℝ)) hHfour
    have hlogMono :
        1 + Real.log (H (m : ℝ) + 6) ≤
          1 + Real.log ((m : ℝ) ^ alpha + 6) := by
      have hlogRaw :
          Real.log (H (m : ℝ) + 6) ≤
            Real.log ((m : ℝ) ^ alpha + 6) := by
        apply Real.log_le_log
        · linarith
        · simpa [carlsonPolynomialHeight] using hHupper
      linarith
    have hleftNonneg :
        0 ≤ 1 + Real.log (H (m : ℝ) + 6) := by
      have hlogPos : 0 < Real.log (H (m : ℝ) + 6) :=
        Real.log_pos (by linarith)
      linarith
    have hlogCombined :
        1 + Real.log (H (m : ℝ) + 6) ≤
          (alpha + 2) * Real.log (m : ℝ) ^ 4 :=
      hlogMono.trans hlogBound
    have hrightNonneg :
        0 ≤ (alpha + 2) * Real.log (m : ℝ) ^ 4 :=
      hleftNonneg.trans hlogCombined
    have hfactorNonneg :
        0 ≤
          ((alpha + 2) * Real.log (m : ℝ) ^ 4 -
              (1 + Real.log (H (m : ℝ) + 6))) *
            ((alpha + 2) * Real.log (m : ℝ) ^ 4 +
              (1 + Real.log (H (m : ℝ) + 6))) :=
      mul_nonneg (sub_nonneg.mpr hlogCombined)
        (add_nonneg hrightNonneg hleftNonneg)
    have hlogSquare :
        (1 + Real.log (H (m : ℝ) + 6)) ^ 2 ≤
          ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2 := by
      nlinarith
    have hreciprocal :
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity (H (m : ℝ)) ≤
          C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2 := by
      exact hglobalBound.trans
        (mul_le_mul_of_nonneg_left hlogSquare hC)
    have hphysicalBound :
        ‖∑ rho ∈ input.layer (0 : Fin 2),
            pntRelativeZeroContribution (m : ℝ) rho‖ ≤
          (m : ℝ) ^ (sigma - 1) *
            (C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2) :=
      hphysical.trans
        (mul_le_mul_of_nonneg_left hreciprocal
          (Real.rpow_nonneg hmNonneg _))
    have hnormalized :
        actualDynamicBoundaryLowNormalizedSum H beta
            (actualDynamicBoundaryCanonicalTwoStripInput H beta sigma)
            (0 : Fin 2) m ≤
          ((m : ℝ) ^ (sigma - 1) *
              (C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2)) /
            targetZeroPowerAmplitude beta (m : ℝ) := by
      unfold actualDynamicBoundaryLowNormalizedSum
      exact (div_le_div_iff_of_pos_right hAmplitude).2
        (by simpa [input] using hphysicalBound)
    calc
      actualDynamicBoundaryLowNormalizedSum H beta
          (actualDynamicBoundaryCanonicalTwoStripInput H beta sigma)
          (0 : Fin 2) m
          ≤ ((m : ℝ) ^ (sigma - 1) *
                (C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2)) /
              targetZeroPowerAmplitude beta (m : ℝ) :=
        hnormalized
      _ = C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2 *
            ((m : ℝ) ^ (sigma - 1) /
              (m : ℝ) ^ (beta - 1)) := by
        unfold targetZeroPowerAmplitude
        ring_nf
      _ = C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2 *
            (m : ℝ) ^ ((sigma - 1) - (beta - 1)) := by
        rw [← Real.rpow_sub hmPos]
      _ = actualReciprocalLowNormalizedLogPowerMajorant
            C alpha beta sigma (m : ℝ) := by
        unfold actualReciprocalLowNormalizedLogPowerMajorant
        ring_nf

/-- The complete canonical dynamic positive tail inherits the improved
reciprocal low-layer margin; the high Carlson layer is unchanged. -/
theorem
    actualDynamicBoundaryCanonicalPositiveNormalizedSum_tendsto_zero_reciprocal
    {H : ℝ → ℝ} {beta sigma alpha epsilon : ℝ}
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hHle :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hHtop : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + epsilon < 0)
    (hright :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta) :
    Tendsto
      (actualDynamicBoundaryPositiveNormalizedSum H beta)
      atTop (nhds 0) := by
  apply actualDynamicBoundaryPositiveNormalizedSum_tendsto_zero
    (actualDynamicBoundaryCanonicalTwoStripInput H beta sigma)
    (0 : Fin 2) hhalf hone hHtop
  · exact fun m rho hrho =>
      actualDynamicBoundaryCanonicalTwoStripInput_low_re_le m hrho
  · exact fun m rho hrho hre =>
      actualDynamicBoundaryCanonicalTwoStripInput_low_cover m hrho hre
  · exact hright
  · exact
      actualDynamicBoundaryCanonicalLowNormalizedSum_tendsto_zero_reciprocal
        hHle hHtop halpha hepsilon hmargin

end

end PrimeNumberTheorem
