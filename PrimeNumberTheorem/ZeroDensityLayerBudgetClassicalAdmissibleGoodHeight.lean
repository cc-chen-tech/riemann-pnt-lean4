import PrimeNumberTheorem.ZeroDensityLayerBudgetClassicalAdmissibleBalancedRate
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTFormulaRemainderDecay

open Complex Filter Set Topology

namespace PrimeNumberTheorem

/-- Select the uniform explicit-formula good height in the unit interval below
the admissibly optimal classical square-root-logarithmic height. -/
noncomputable def selectedClassicalAdmissibleGoodHeight
    (b : ℝ) (selection : UniformNaturalPointGoodHeightSelection)
    (x : ℝ) : ℝ :=
  selection.height
    (pintzCarlsonGoodHeightBase
      (classicalAdmissibleBalancedRate b) x)

/-- The admissibly optimal selected height eventually lies in exactly the
unit interval required by the proved contour remainder theorem. -/
theorem eventually_selectedClassicalAdmissibleGoodHeight_mem
    {b : ℝ} (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ x : ℝ in atTop,
      selectedClassicalAdmissibleGoodHeight b selection x ∈
        Set.Icc
          (pintzCarlsonGoodHeightBase
            (classicalAdmissibleBalancedRate b) x)
          (pintzCarlsonGoodHeightBase
            (classicalAdmissibleBalancedRate b) x + 1) := by
  have hheight :
      Tendsto
        (pintzCarlsonHeight (classicalAdmissibleBalancedRate b))
        atTop atTop :=
    tendsto_pintzCarlsonHeight_atTop
      (classicalAdmissibleBalancedRate_pos hb)
  have hlarge :
      ∀ᶠ x : ℝ in atTop,
        9 ≤ pintzCarlsonHeight
          (classicalAdmissibleBalancedRate b) x :=
    (tendsto_atTop.1 hheight) 9
  filter_upwards [hlarge] with x hx
  have hbase :
      8 ≤ pintzCarlsonGoodHeightBase
        (classicalAdmissibleBalancedRate b) x := by
    dsimp [pintzCarlsonGoodHeightBase]
    linarith
  exact selection.height_mem _ hbase

/-- The same admissibly optimal schedule consists eventually of analytic good
heights. -/
theorem eventually_selectedClassicalAdmissibleGoodHeight_good
    {b : ℝ} (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ x : ℝ in atTop,
      ExplicitFormulaAux.goodHeight
        (selectedClassicalAdmissibleGoodHeight b selection x) := by
  have hheight :
      Tendsto
        (pintzCarlsonHeight (classicalAdmissibleBalancedRate b))
        atTop atTop :=
    tendsto_pintzCarlsonHeight_atTop
      (classicalAdmissibleBalancedRate_pos hb)
  have hlarge :
      ∀ᶠ x : ℝ in atTop,
        9 ≤ pintzCarlsonHeight
          (classicalAdmissibleBalancedRate b) x :=
    (tendsto_atTop.1 hheight) 9
  filter_upwards [hlarge] with x hx
  have hbase :
      8 ≤ pintzCarlsonGoodHeightBase
        (classicalAdmissibleBalancedRate b) x := by
    dsimp [pintzCarlsonGoodHeightBase]
    linarith
  exact selection.good_height _ hbase

/-- Every admissible natural point receives the full truncated explicit
formula at the admissibly optimal selected height. -/
theorem selectedClassicalAdmissibleGoodHeight_truncatedCertificate
    {b : ℝ} (selection : UniformNaturalPointGoodHeightSelection)
    (m N : ℕ) (hm : 3 ≤ m)
    (hbase :
      8 ≤ pintzCarlsonGoodHeightBase
        (classicalAdmissibleBalancedRate b) (m : ℝ)) :
    ∃ certificate :
        TruncatedPNTErrorCertificate (m : ℝ)
          (selectedClassicalAdmissibleGoodHeight b selection (m : ℝ)),
      certificate.trivialContribution =
          cofinalTrivialZeroContribution m N ∧
        certificate.remainderBound =
          cofinalPNTFormulaRemainderBound selection.constant
            (pintzCarlsonGoodHeightBase
              (classicalAdmissibleBalancedRate b) (m : ℝ))
            (selectedClassicalAdmissibleGoodHeight b selection (m : ℝ))
            m N := by
  simpa [selectedClassicalAdmissibleGoodHeight] using
    selection.truncated_certificate
      (pintzCarlsonGoodHeightBase
        (classicalAdmissibleBalancedRate b) (m : ℝ))
      hbase m N hm

/-- At the admissibly optimal selected height, the actual depth-zero contour
remainder divided by `m` tends to zero. -/
theorem selectedClassicalAdmissibleGoodHeight_contourRelative_tendsto
    {b : ℝ} (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (fun m : ℕ =>
        cofinalPNTFormulaRemainderBound selection.constant
          (pintzCarlsonGoodHeightBase
            (classicalAdmissibleBalancedRate b) (m : ℝ))
          (selectedClassicalAdmissibleGoodHeight b selection (m : ℝ))
          m 0 / (m : ℝ))
      atTop (nhds 0) := by
  apply cofinalPNTFormulaRemainderBound_zero_relative_tendsto
    selection.constant_nonneg
    (classicalAdmissibleBalancedRate_pos hb)
    (classicalAdmissibleBalancedRate_le_one b)
  exact tendsto_natCast_atTop_atTop.eventually
    (eventually_selectedClassicalAdmissibleGoodHeight_mem hb selection)

end PrimeNumberTheorem
