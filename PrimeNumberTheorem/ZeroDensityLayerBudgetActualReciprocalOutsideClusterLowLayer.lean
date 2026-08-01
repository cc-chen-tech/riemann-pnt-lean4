import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryReciprocalLowLayer

/-!
# Reciprocal low layer outside an arbitrary fixed cluster

The reciprocal-mass estimate used for the dynamic equal-real-part package is
in fact independent of that package.  This module exposes the generic fixed-
cluster statement needed to rebuild the Carlson boundary transfer without the
old polynomial-height loss.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Complex Filter

noncomputable section

/-- For any fixed visible cluster and any outside-cluster bucket whose selected
layer lies in `Re rho <= sigma`, the normalized layer tends to zero under the
reciprocal margin `sigma - beta + epsilon < 0`.  The height exponent affects
only a polylogarithmic coefficient. -/
theorem
    tendsto_dynamicPositiveOutsideClusterPNTLayerNorm_div_targetAmplitude_zero_reciprocal
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {beta sigma alpha epsilon : ℝ}
    (input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (H x) S n)
    (i : Fin n)
    (hHle : ∀ᶠ x : ℝ in atTop,
      H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + epsilon < 0)
    (hre : ∀ x rho, rho ∈ (input x).layer i → rho.re ≤ sigma) :
    Tendsto
      (fun m : ℕ =>
        dynamicPositiveOutsideClusterPNTLayerNorm H S input i (m : ℝ) /
          targetZeroPowerAmplitude beta (m : ℝ))
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
  have hHleNat :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hHle
  have hHtopNat : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop :=
    hHtop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmPos : 0 < (m : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hm)
    exact div_nonneg (norm_nonneg _)
      (Real.rpow_nonneg hmPos.le _)
  · filter_upwards [
      eventually_ge_atTop (1 : ℕ),
      hHtopNat.eventually (eventually_ge_atTop (4 : ℝ)),
      hHleNat, hlog] with m hm hHfour hHupper hlogBound
    have hmPos : 0 < (m : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hm)
    have hmNonneg : 0 ≤ (m : ℝ) := hmPos.le
    have hAmplitude :
        0 < targetZeroPowerAmplitude beta (m : ℝ) :=
      Real.rpow_pos_of_pos hmPos _
    have hphysical :
        ‖∑ rho ∈ (input (m : ℝ)).layer i,
            pntRelativeZeroContribution (m : ℝ) rho‖ ≤
          (m : ℝ) ^ (sigma - 1) *
            ExplicitFormulaAux.globalReciprocalZeroMultiplicity
              (H (m : ℝ)) :=
      (input (m : ℝ)).norm_layer_sum_le_rpow_mul_globalReciprocal
        i (by exact_mod_cast hm) (hre (m : ℝ))
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
          C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2 :=
      hglobalBound.trans
        (mul_le_mul_of_nonneg_left hlogSquare hC)
    have hphysicalBound :
        ‖∑ rho ∈ (input (m : ℝ)).layer i,
            pntRelativeZeroContribution (m : ℝ) rho‖ ≤
          (m : ℝ) ^ (sigma - 1) *
            (C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2) :=
      hphysical.trans
        (mul_le_mul_of_nonneg_left hreciprocal
          (Real.rpow_nonneg hmNonneg _))
    have hnormalized :
        dynamicPositiveOutsideClusterPNTLayerNorm H S input i (m : ℝ) /
            targetZeroPowerAmplitude beta (m : ℝ) ≤
          ((m : ℝ) ^ (sigma - 1) *
              (C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2)) /
            targetZeroPowerAmplitude beta (m : ℝ) := by
      unfold dynamicPositiveOutsideClusterPNTLayerNorm
      exact (div_le_div_iff_of_pos_right hAmplitude).2 hphysicalBound
    calc
      dynamicPositiveOutsideClusterPNTLayerNorm H S input i (m : ℝ) /
          targetZeroPowerAmplitude beta (m : ℝ)
          ≤ ((m : ℝ) ^ (sigma - 1) *
                (C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2)) /
              targetZeroPowerAmplitude beta (m : ℝ) := hnormalized
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

end

end PrimeNumberTheorem
