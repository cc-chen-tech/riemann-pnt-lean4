import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDyadicCarlsonSelectedHeightPNT
import PrimeNumberTheorem.ZeroDensityLayerBudgetClassicalAdmissibleFiniteZeroDecay

/-!
# Classical selected heights satisfy the automatic dyadic Carlson gap

At the admissibly balanced classical height

`T(x) = exp (O (sqrt (log x)))`,

the proved classical zero-free region has width of order
`1 / sqrt (log x)`.  This is large enough to pay both the Carlson
fourth-logarithm loss and the logarithmic cost of the automatically selected
minimal dyadic layer count.
-/

namespace PrimeNumberTheorem

open Complex Filter Set Topology

noncomputable section

/-- A globally positive representative of the classical
`1 / sqrt (log m)` zero-free width. -/
noncomputable def classicalAdmissibleDyadicCarlsonGapWidth
    (rate : ℝ) (m : ℕ) : ℝ :=
  rate / (1 + pntSqrtLog m)

theorem classicalAdmissibleDyadicCarlsonGapWidth_pos
    {rate : ℝ} (hrate : 0 < rate) (m : ℕ) :
    0 < classicalAdmissibleDyadicCarlsonGapWidth rate m := by
  unfold classicalAdmissibleDyadicCarlsonGapWidth
  exact div_pos hrate (by
    have hsqrt : 0 ≤ pntSqrtLog m := by
      unfold pntSqrtLog
      positivity
    linarith)

theorem classicalAdmissibleDyadicCarlsonGapWidth_nonneg
    {rate : ℝ} (hrate : 0 < rate) (m : ℕ) :
    0 ≤ classicalAdmissibleDyadicCarlsonGapWidth rate m :=
  (classicalAdmissibleDyadicCarlsonGapWidth_pos hrate m).le

/-- The classical moving width eventually lies in the range required by the
minimal dyadic cover. -/
theorem eventually_classicalAdmissibleDyadicCarlsonGapWidth_le_eighth
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᶠ m : ℕ in atTop,
      classicalAdmissibleDyadicCarlsonGapWidth rate m ≤ 1 / 8 := by
  have hlarge :
      ∀ᶠ m : ℕ in atTop, 8 * rate ≤ pntSqrtLog m :=
    tendsto_pntSqrtLog_atTop.eventually
      (eventually_ge_atTop (8 * rate))
  filter_upwards [hlarge] with m hm
  unfold classicalAdmissibleDyadicCarlsonGapWidth
  have hden : 0 < 1 + pntSqrtLog m := by
    have hsqrt : 0 ≤ pntSqrtLog m := by
      unfold pntSqrtLog
      positivity
    linarith
  apply (div_le_iff₀ hden).2
  nlinarith

/-- The square-root-logarithmic classical width pays the complete automatic
dyadic Carlson logarithmic cost. -/
theorem isCarlsonMovingDyadicLogPowerGap_classicalAdmissible
    {rate : ℝ} (hrate : 0 < rate) :
    IsCarlsonMovingDyadicLogPowerGap
      (classicalAdmissibleDyadicCarlsonGapWidth rate) := by
  unfold IsCarlsonMovingDyadicLogPowerGap
  have hscale : Tendsto pntSqrtLog atTop atTop :=
    tendsto_pntSqrtLog_atTop
  have hlogSmallReal :
      ∀ᶠ u : ℝ in atTop,
        ‖Real.log u‖ ≤ (rate / 176) * ‖u‖ :=
    Real.isLittleO_log_id_atTop.bound (by positivity)
  have hlogSmall :
      ∀ᶠ m : ℕ in atTop,
        ‖Real.log (pntSqrtLog m)‖ ≤
          (rate / 176) * ‖pntSqrtLog m‖ :=
    hscale.eventually hlogSmallReal
  have hmodelReal :
      Tendsto
        (fun u : ℝ =>
          rate / 8 * u - 3 * Real.log (2 / rate))
        atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop
        (-3 * Real.log (2 / rate))
        ((tendsto_id : Tendsto (fun u : ℝ => u) atTop atTop)
          |>.const_mul_atTop (by positivity : 0 < rate / 8))
  have hmodel :
      Tendsto
        (fun m : ℕ =>
          rate / 8 * pntSqrtLog m -
            3 * Real.log (2 / rate))
        atTop atTop :=
    hmodelReal.comp hscale
  apply tendsto_atTop_mono' atTop ?_ hmodel
  filter_upwards [
      eventually_ge_atTop (2 : ℕ),
      hscale.eventually (eventually_ge_atTop (2 : ℝ)),
      hlogSmall] with m hm huTwo hlogSmallM
  let u : ℝ := pntSqrtLog m
  have hmReal : (1 : ℝ) < (m : ℝ) := by
    exact_mod_cast hm
  have hlogmPos : 0 < Real.log (m : ℝ) :=
    Real.log_pos hmReal
  have huPos : 0 < u := by
    dsimp [u, pntSqrtLog]
    exact Real.sqrt_pos.2 hlogmPos
  have huOne : 1 ≤ u := by
    dsimp [u]
    linarith
  have hscaleSq : u ^ 2 = Real.log (m : ℝ) := by
    dsimp [u, pntSqrtLog]
    exact Real.sq_sqrt hlogmPos.le
  have hden : 0 < 1 + u := by linarith
  have hpositive :
      rate / (1 + u) / 2 * Real.log (m : ℝ) ≥
        rate / 4 * u := by
    have hratio : u / 2 ≤ u ^ 2 / (1 + u) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    rw [← hscaleSq]
    calc
      rate / (1 + u) / 2 * u ^ 2 =
          rate / 2 * (u ^ 2 / (1 + u)) := by
        field_simp
        <;> ring
      _ ≥ rate / 2 * (u / 2) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = rate / 4 * u := by ring
  have hgapInvPos :
      0 <
        (classicalAdmissibleDyadicCarlsonGapWidth rate m)⁻¹ :=
    inv_pos.mpr
      (classicalAdmissibleDyadicCarlsonGapWidth_pos hrate m)
  have hgapInvLe :
      (classicalAdmissibleDyadicCarlsonGapWidth rate m)⁻¹ ≤
        (2 / rate) * u := by
    unfold classicalAdmissibleDyadicCarlsonGapWidth
    dsimp [u]
    rw [inv_div]
    apply (div_le_iff₀ hrate).2
    field_simp [hrate.ne']
    nlinarith
  have htwoRatePos : 0 < 2 / rate := by positivity
  have hproductPos : 0 < (2 / rate) * u :=
    mul_pos htwoRatePos huPos
  have hlogGapInv :
      Real.log
          (classicalAdmissibleDyadicCarlsonGapWidth rate m)⁻¹ ≤
        Real.log (2 / rate) + Real.log u := by
    have hle :=
      Real.log_le_log hgapInvPos hgapInvLe
    rw [Real.log_mul htwoRatePos.ne' huPos.ne'] at hle
    exact hle
  have hloglog :
      Real.log (Real.log (m : ℝ)) = 2 * Real.log u := by
    rw [← hscaleSq, pow_two,
      Real.log_mul huPos.ne' huPos.ne']
    ring
  have hloguNonneg : 0 ≤ Real.log u :=
    Real.log_nonneg huOne
  have hloguSmall :
      Real.log u ≤ rate / 176 * u := by
    simpa [u, Real.norm_eq_abs, abs_of_nonneg hloguNonneg,
      abs_of_nonneg huPos.le] using hlogSmallM
  unfold classicalAdmissibleDyadicCarlsonGapWidth
  unfold classicalAdmissibleDyadicCarlsonGapWidth at hlogGapInv
  dsimp [u] at hpositive hlogGapInv hloglog hloguSmall ⊢
  rw [hloglog]
  nlinarith

/-- The proved classical truncation right edge implies the selected-height
dynamic zero-free predicate for the same square-root-logarithmic width. -/
theorem
    isSelectedHeightDynamicZeroFree_selectedClassicalAdmissible
    {b rate : ℝ}
    (hb : 0 < b) (hrate : 0 < rate)
    (hmargin :
      rate * classicalAdmissibleBalancedRate b < b)
    (hzeros :
      ∀ T : ℝ, 4 ≤ T →
        ∀ rho ∈ nontrivialZerosFinset T,
          rho.re ≤ classicalTruncationRightEdge b T)
    (selection : UniformNaturalPointGoodHeightSelection) :
    IsSelectedHeightDynamicZeroFree
      (selectedClassicalAdmissibleGoodHeight b selection)
      (classicalAdmissibleDyadicCarlsonGapWidth rate) := by
  unfold IsSelectedHeightDynamicZeroFree
  let alpha : ℝ := classicalAdmissibleBalancedRate b
  have halpha : 0 < alpha :=
    classicalAdmissibleBalancedRate_pos hb
  have hheight :
      ∀ᶠ m : ℕ in atTop,
        selectedClassicalAdmissibleGoodHeight b selection (m : ℝ) ∈
          Set.Icc
            (pintzCarlsonGoodHeightBase alpha (m : ℝ))
            (pintzCarlsonGoodHeightBase alpha (m : ℝ) + 1) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_selectedClassicalAdmissibleGoodHeight_mem hb selection)
  have hbaseLargeReal :
      ∀ᶠ x : ℝ in atTop, 9 ≤ pintzCarlsonHeight alpha x :=
    (tendsto_atTop.1
      (tendsto_pintzCarlsonHeight_atTop halpha)) 9
  have hbaseLarge :
      ∀ᶠ m : ℕ in atTop,
        9 ≤ pintzCarlsonHeight alpha (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hbaseLargeReal
  have hscaleLarge :
      ∀ᶠ m : ℕ in atTop,
        max 1
            (rate * Real.log 8 / (b - rate * alpha)) ≤
          pntSqrtLog m :=
    tendsto_pntSqrtLog_atTop.eventually
      (eventually_ge_atTop
        (max 1
          (rate * Real.log 8 / (b - rate * alpha))))
  filter_upwards [hheight, hbaseLarge, hscaleLarge]
      with m hmHeight hmBase hmScale
  intro rho hrhoZero hrhoIm hrhoHeight
  let x : ℝ := m
  let u : ℝ := pntSqrtLog m
  let T : ℝ :=
    selectedClassicalAdmissibleGoodHeight b selection (m : ℝ)
  have hu : 0 < u := by
    dsimp [u]
    linarith [le_trans (le_max_left _ _) hmScale]
  have hthreshold :
      rate * Real.log 8 / (b - rate * alpha) ≤ u := by
    dsimp [u]
    exact (le_max_right _ _).trans hmScale
  have hTupper : T ≤ Real.exp (alpha * u) := by
    have hupper := hmHeight.2
    dsimp [T, alpha, u]
    simpa [pintzCarlsonGoodHeightBase, pintzCarlsonHeight,
      pintzCarlsonSqrtLogScale, pntSqrtLog] using hupper
  have hbase :
      8 ≤ pintzCarlsonGoodHeightBase alpha (m : ℝ) := by
    dsimp [pintzCarlsonGoodHeightBase] at hmBase ⊢
    linarith
  have hT : 4 ≤ T := by
    exact le_trans (by norm_num) (hbase.trans hmHeight.1)
  have hwidth :
      rate / u ≤ b / Real.log (T + 6) := by
    exact dynamicHeight_classicalZeroFreeWidth_ge
      halpha hrate hmargin hu hthreshold hT hTupper
  have hgapLeRate :
      classicalAdmissibleDyadicCarlsonGapWidth rate m ≤
        rate / u := by
    unfold classicalAdmissibleDyadicCarlsonGapWidth
    dsimp [u]
    exact div_le_div_of_nonneg_left hrate.le hu (by linarith)
  have hrhoFinset : rho ∈ nontrivialZerosFinset T := by
    exact mem_nontrivialZerosFinset.mpr
      ⟨hrhoZero, by
        simpa [T, abs_of_pos hrhoIm] using hrhoHeight⟩
  have hre := hzeros T hT rho hrhoFinset
  have hgapWidth :
      classicalAdmissibleDyadicCarlsonGapWidth rate m ≤
        b / Real.log (T + 6) :=
    hgapLeRate.trans hwidth
  unfold classicalTruncationRightEdge at hre
  linarith

/-- Canonical constants simultaneously close the automatic dyadic Carlson
margin and the selected-height classical zero-free predicate. -/
theorem exists_selectedClassicalAdmissibleDyadicCarlsonZeroFreeGap :
    ∃ b rate : ℝ,
      0 < b ∧
      0 < rate ∧
      IsCarlsonMovingDyadicLogPowerGap
        (classicalAdmissibleDyadicCarlsonGapWidth rate) ∧
      ∀ selection : UniformNaturalPointGoodHeightSelection,
        IsSelectedHeightDynamicZeroFree
          (selectedClassicalAdmissibleGoodHeight b selection)
          (classicalAdmissibleDyadicCarlsonGapWidth rate) := by
  rcases
      exists_classicalTruncationRightEdge_nontrivialZerosFinset
      with ⟨b, hb, hzeros⟩
  let alpha : ℝ := classicalAdmissibleBalancedRate b
  let rate : ℝ := alpha / 2
  have halpha : 0 < alpha :=
    classicalAdmissibleBalancedRate_pos hb
  have hrate : 0 < rate := by
    dsimp [rate]
    linarith
  have halphaSquare : alpha ^ 2 ≤ b := by
    have hzeroFree :=
      classicalAdmissibleBalancedRate_le_zeroFreeRate hb
    have hmul := (le_div_iff₀ halpha).mp hzeroFree
    nlinarith
  have hmargin : rate * alpha < b := by
    dsimp [rate]
    nlinarith [sq_pos_of_pos halpha]
  refine ⟨b, rate, hb, hrate,
    isCarlsonMovingDyadicLogPowerGap_classicalAdmissible hrate, ?_⟩
  intro selection
  exact
    isSelectedHeightDynamicZeroFree_selectedClassicalAdmissible
      hb hrate hmargin hzeros selection

end

end PrimeNumberTheorem
