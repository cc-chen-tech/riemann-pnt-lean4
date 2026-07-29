import PrimeNumberTheorem.ZeroDensityLayerBudgetClassicalAdmissibleFiniteZeroDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTFixedResidualDecay

open Complex Filter Set Topology

namespace PrimeNumberTheorem

/-- The proved classical zero-free region, the admissibly optimal dynamic
height, and the actual natural-point explicit formula together imply the PNT
relative error along natural samples.

Every analytic contribution is evaluated at the same selected good height:
the complete multiplicity-weighted finite zero sum, the contour remainder,
and the truncated explicit-formula certificate. -/
theorem exists_classicalAdmissibleSelectedHeight_relativePNT_tendsto_zero :
    ∃ b : ℝ, 0 < b ∧
      ∀ selection : UniformNaturalPointGoodHeightSelection,
        Tendsto
          (fun m : ℕ =>
            relativeChebyshevPsi0Error (m : ℝ))
          atTop (nhds 0) := by
  rcases
      exists_selectedClassicalAdmissibleFiniteZeroSum_relative_tendsto
      with ⟨b, C, hb, hC, hzero⟩
  refine ⟨b, hb, ?_⟩
  intro selection
  let height : ℕ → ℝ := fun m =>
    selectedClassicalAdmissibleGoodHeight b selection (m : ℝ)
  let contour : ℕ → ℝ := fun m =>
    cofinalPNTFormulaRemainderBound selection.constant
      (pintzCarlsonGoodHeightBase
        (classicalAdmissibleBalancedRate b) (m : ℝ))
      (height m) m 0 / (m : ℝ)
  let fixed : ℕ → ℝ := fun m =>
    (‖deriv riemannZeta 0 / riemannZeta 0‖ +
      ‖cofinalTrivialZeroContribution m 0‖) / (m : ℝ)
  let zeros : ℕ → ℝ := fun m =>
    ‖finiteNontrivialZeroSumWithMultiplicity
        (m : ℝ) (height m)‖ / (m : ℝ)
  have hzeroLimit :
      Tendsto zeros atTop (nhds 0) := by
    simpa [zeros, height] using hzero selection
  have hfixedLimit :
      Tendsto fixed atTop (nhds 0) := by
    simpa [fixed] using
      tendsto_naturalPoint_fixedPNTConstants_zeroDepth_relative
  have hcontourLimit :
      Tendsto contour atTop (nhds 0) := by
    simpa [contour, height] using
      selectedClassicalAdmissibleGoodHeight_contourRelative_tendsto
        hb selection
  have htotal :
      Tendsto (fun m => zeros m + fixed m + contour m)
        atTop (nhds 0) := by
    simpa only [zero_add, add_zero] using
      (hzeroLimit.add hfixedLimit).add hcontourLimit
  have hheightReal :=
    eventually_selectedClassicalAdmissibleGoodHeight_mem hb selection
  have hheightNat :=
    tendsto_natCast_atTop_atTop.eventually hheightReal
  let alpha : ℝ := classicalAdmissibleBalancedRate b
  have halpha : 0 < alpha :=
    classicalAdmissibleBalancedRate_pos hb
  have hHeightLargeReal :
      ∀ᶠ x : ℝ in atTop,
        9 ≤ pintzCarlsonHeight alpha x :=
    (tendsto_atTop.1
      (tendsto_pintzCarlsonHeight_atTop halpha)) 9
  have hHeightLargeNat :=
    tendsto_natCast_atTop_atTop.eventually hHeightLargeReal
  have hupper :
      ∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| ≤
          zeros m + fixed m + contour m := by
    filter_upwards
        [hheightNat, hHeightLargeNat,
          eventually_ge_atTop (3 : ℕ)]
        with m hmHeight hmHeightLarge hm
    let x : ℝ := m
    have hx : 0 < x := by
      dsimp [x]
      exact_mod_cast (show 0 < m by omega)
    have hbase :
        8 ≤ pintzCarlsonGoodHeightBase
          (classicalAdmissibleBalancedRate b) (m : ℝ) := by
      dsimp [alpha, pintzCarlsonGoodHeightBase] at hmHeightLarge ⊢
      linarith
    rcases
        selectedClassicalAdmissibleGoodHeight_truncatedCertificate
          selection m 0 hm hbase
      with ⟨certificate, htrivial, hremainder⟩
    have hcertificate :=
      certificate.abs_chebyshevPsi0_sub_id_le
    rw [htrivial, hremainder] at hcertificate
    have hdivide :=
      div_le_div_of_nonneg_right hcertificate hx.le
    rw [relativeChebyshevPsi0Error, abs_div,
      abs_of_pos hx]
    calc
      |chebyshevPsi0 x - x| / x ≤
          (‖finiteNontrivialZeroSumWithMultiplicity x
              (selectedClassicalAdmissibleGoodHeight
                b selection (m : ℝ))‖ +
            ‖deriv riemannZeta 0 / riemannZeta 0‖ +
            ‖cofinalTrivialZeroContribution m 0‖ +
            cofinalPNTFormulaRemainderBound selection.constant
              (pintzCarlsonGoodHeightBase
                (classicalAdmissibleBalancedRate b) (m : ℝ))
              (selectedClassicalAdmissibleGoodHeight
                b selection (m : ℝ)) m 0) / x :=
        hdivide
      _ = zeros m + fixed m + contour m := by
        dsimp [zeros, fixed, contour, height, x]
        ring
  have habs :
      Tendsto
        (fun m : ℕ =>
          |relativeChebyshevPsi0Error (m : ℝ)|)
        atTop (nhds 0) := by
    refine squeeze_zero' ?_ hupper htotal
    filter_upwards with m
    exact abs_nonneg _
  have hnorm :
      Tendsto
        (fun m : ℕ => ‖relativeChebyshevPsi0Error (m : ℝ)‖)
        atTop (nhds 0) := by
    simpa [Real.norm_eq_abs] using habs
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

end PrimeNumberTheorem
