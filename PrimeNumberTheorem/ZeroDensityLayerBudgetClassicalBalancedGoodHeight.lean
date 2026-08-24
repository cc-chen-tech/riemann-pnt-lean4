import PrimeNumberTheorem.ZeroDensityLayerBudgetClassicalZeroFreeProfile
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightGoodHeightChoice

open Complex Filter Set Topology

namespace PrimeNumberTheorem

/-- The optimally balanced base height associated with the classical
`b / log T` zero-free region. -/
noncomputable def classicalBalancedHeightBase (b x : ℝ) : ℝ :=
  Real.exp (Real.sqrt b * Real.sqrt (Real.log x))

/-- Select the uniform explicit-formula good height in the unit interval
ending at the optimally balanced base height. -/
noncomputable def selectedClassicalBalancedGoodHeight
    (b : ℝ) (selection : UniformNaturalPointGoodHeightSelection)
    (x : ℝ) : ℝ :=
  selection.height (classicalBalancedHeightBase b x - 1)

theorem classicalBalancedHeightBase_tendsto_atTop {b : ℝ} (hb : 0 < b) :
    Tendsto (classicalBalancedHeightBase b) atTop atTop := by
  have hsqrtLog :
      Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hscaled :
      Tendsto
        (fun x : ℝ => Real.sqrt b * Real.sqrt (Real.log x))
        atTop atTop :=
    hsqrtLog.const_mul_atTop (Real.sqrt_pos.2 hb)
  change
    Tendsto
      (Real.exp ∘ fun x : ℝ =>
        Real.sqrt b * Real.sqrt (Real.log x))
      atTop atTop
  exact Real.tendsto_exp_atTop.comp hscaled

/-- The selected height lies eventually in the optimal unit window. -/
theorem eventually_selectedClassicalBalancedGoodHeight_mem
    {b : ℝ} (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ x : ℝ in atTop,
      selectedClassicalBalancedGoodHeight b selection x ∈
        Set.Icc (classicalBalancedHeightBase b x - 1)
          (classicalBalancedHeightBase b x) := by
  have hlarge :
      ∀ᶠ x : ℝ in atTop, 9 ≤ classicalBalancedHeightBase b x :=
    (tendsto_atTop.1 (classicalBalancedHeightBase_tendsto_atTop hb)) 9
  filter_upwards [hlarge] with x hx
  have hbase : 8 ≤ classicalBalancedHeightBase b x - 1 := by
    linarith
  simpa [selectedClassicalBalancedGoodHeight] using
    selection.height_mem (classicalBalancedHeightBase b x - 1) hbase

/-- The optimal unit-window schedule consists eventually of analytic good
heights. -/
theorem eventually_selectedClassicalBalancedGoodHeight_good
    {b : ℝ} (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ x : ℝ in atTop,
      ExplicitFormulaAux.goodHeight
        (selectedClassicalBalancedGoodHeight b selection x) := by
  have hlarge :
      ∀ᶠ x : ℝ in atTop, 9 ≤ classicalBalancedHeightBase b x :=
    (tendsto_atTop.1 (classicalBalancedHeightBase_tendsto_atTop hb)) 9
  filter_upwards [hlarge] with x hx
  have hbase : 8 ≤ classicalBalancedHeightBase b x - 1 := by
    linarith
  exact selection.good_height
    (classicalBalancedHeightBase b x - 1) hbase

/-- The selected balanced height retains the full natural-point truncated
explicit-formula certificate. -/
theorem selectedClassicalBalancedGoodHeight_truncatedCertificate
    {b : ℝ} (selection : UniformNaturalPointGoodHeightSelection)
    (m N : ℕ) (hm : 3 ≤ m)
    (hbase : 8 ≤ classicalBalancedHeightBase b (m : ℝ) - 1) :
    ∃ certificate :
        TruncatedPNTErrorCertificate (m : ℝ)
          (selectedClassicalBalancedGoodHeight b selection (m : ℝ)),
      certificate.trivialContribution =
          cofinalTrivialZeroContribution m N ∧
        certificate.remainderBound =
          cofinalPNTFormulaRemainderBound selection.constant
            (classicalBalancedHeightBase b (m : ℝ) - 1)
            (selectedClassicalBalancedGoodHeight b selection (m : ℝ))
            m N := by
  simpa [selectedClassicalBalancedGoodHeight] using
    selection.truncated_certificate
      (classicalBalancedHeightBase b (m : ℝ) - 1) hbase m N hm

/-- The additive `+6` in the actual finite-zero theorem costs only an
arbitrarily small amount in the balanced exponent.  If
`T ≤ exp (sqrt b * u)`, then beyond an explicit threshold the zero-free width
is at least `(sqrt b - epsilon) / u`. -/
theorem classicalBalancedHeight_zeroFreeWidth_ge
    {b epsilon u T : ℝ}
    (hb : 0 < b) (hepsilon : 0 < epsilon)
    (hepsilonSqrt : epsilon < Real.sqrt b)
    (hu : 0 < u)
    (hthreshold :
      ((Real.sqrt b - epsilon) * Real.log 8) /
          (epsilon * Real.sqrt b) ≤ u)
    (hT : 4 ≤ T)
    (hTupper : T ≤ Real.exp (Real.sqrt b * u)) :
    (Real.sqrt b - epsilon) / u ≤ b / Real.log (T + 6) := by
  have hsqrt : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hsquare : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb.le
  have hgap : 0 ≤ Real.sqrt b - epsilon := by
    linarith
  let A : ℝ := Real.exp (Real.sqrt b * u)
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hAone : 1 ≤ A := by
    dsimp [A]
    exact Real.one_le_exp (mul_nonneg hsqrt.le hu.le)
  have hTplus : T + 6 ≤ 8 * A := by
    dsimp [A] at hTupper ⊢
    nlinarith
  have hlogUpper :
      Real.log (T + 6) ≤ Real.log 8 + Real.sqrt b * u := by
    have hlog :=
      Real.log_le_log (by linarith : 0 < T + 6) hTplus
    have hlogA : Real.log A = Real.sqrt b * u := by
      simp [A]
    rw [Real.log_mul (by norm_num) hApos.ne', hlogA] at hlog
    exact hlog
  have hthresholdMul :
      (Real.sqrt b - epsilon) * Real.log 8 ≤
        epsilon * Real.sqrt b * u := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (div_le_iff₀ (mul_pos hepsilon hsqrt)).mp hthreshold
  have hmain :
      (Real.sqrt b - epsilon) *
          (Real.log 8 + Real.sqrt b * u) ≤ b * u := by
    calc
      (Real.sqrt b - epsilon) *
          (Real.log 8 + Real.sqrt b * u) ≤
          (Real.sqrt b) ^ 2 * u := by
        nlinarith
      _ = b * u := by rw [hsquare]
  have hnumerator :
      (Real.sqrt b - epsilon) * Real.log (T + 6) ≤ b * u :=
    (mul_le_mul_of_nonneg_left hlogUpper hgap).trans hmain
  have hlogT : 0 < Real.log (T + 6) :=
    Real.log_pos (by linarith)
  exact (div_le_div_iff₀ hu hlogT).2 hnumerator

/-- The actual selected good height inherits the proved classical moving
right edge, including the compact low-zero patch. -/
theorem exists_eventually_selectedClassicalBalancedGoodHeight_zeroCap
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∃ b : ℝ, 0 < b ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ rho ∈ nontrivialZerosFinset
            (selectedClassicalBalancedGoodHeight b selection x),
          rho.re ≤ classicalTruncationRightEdge b
            (selectedClassicalBalancedGoodHeight b selection x) := by
  rcases exists_classicalTruncationRightEdge_nontrivialZerosFinset with
    ⟨b, hb, hcap⟩
  refine ⟨b, hb, ?_⟩
  have hlarge :
      ∀ᶠ x : ℝ in atTop, 9 ≤ classicalBalancedHeightBase b x :=
    (tendsto_atTop.1 (classicalBalancedHeightBase_tendsto_atTop hb)) 9
  filter_upwards
      [eventually_selectedClassicalBalancedGoodHeight_mem hb selection,
        hlarge]
      with x hx hxlarge
  have hT : 4 ≤ selectedClassicalBalancedGoodHeight b selection x := by
    have hbase :
        8 ≤ classicalBalancedHeightBase b x - 1 := by
      linarith
    exact le_trans (by norm_num) (hbase.trans hx.1)
  exact hcap _ hT

end PrimeNumberTheorem
