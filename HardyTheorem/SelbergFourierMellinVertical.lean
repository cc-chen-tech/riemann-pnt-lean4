import HardyTheorem.SelbergFourierMellinDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Complex MeasureTheory Set Filter Topology
open scoped Interval

namespace HardyTheorem

/-!
# Infinite-height vertical contour shift for Selberg's Mellin transform

The polynomial-times-exponential estimate proved for the horizontal sides
also gives absolute integrability on every fixed vertical line in the strip.
After this analytic tail issue is discharged, the finite rectangle identity
passes to the limit without any appeal to a zero-density theorem.
-/

/-- Away from the zeta pole's real coordinate, the raw Selberg integrand is
continuous along a fixed vertical line in the open right half-plane. -/
theorem continuous_selbergMellinRaw_vertical
    (delta y : ℝ) (X : ℕ) {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma ≠ 1) :
    Continuous (fun t : ℝ =>
      selbergMellinRawIntegrand (selbergFourierZ delta y) X
        ((sigma : ℂ) + I * t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  let s : ℂ := (sigma : ℂ) + I * t
  have hsre : 0 < s.re := by
    dsimp [s]
    simpa using hsigma0
  have hs1 : s ≠ 1 := by
    intro h
    apply hsigma1
    have hre := congrArg Complex.re h
    simpa [s] using hre
  have hraw : ContinuousAt
      (fun w : ℂ => selbergMellinRawIntegrand
        (selbergFourierZ delta y) X w) s := by
    unfold selbergMellinRawIntegrand
    exact ((analyticOnNhd_selbergMellinWeight
      (selbergFourierZ_ne_zero delta y) X s hsre).continuousAt).mul
        (differentiableAt_riemannZeta hs1).continuousAt
  have hline : ContinuousAt
      (fun u : ℝ => (sigma : ℂ) + I * u) t := by
    fun_prop
  dsimp [s] at hraw
  change ContinuousAt
    ((fun w : ℂ => selbergMellinRawIntegrand
      (selbergFourierZ delta y) X w) ∘
        (fun u : ℝ => (sigma : ℂ) + I * u)) t
  exact ContinuousAt.comp
    (f := fun u : ℝ => (sigma : ℂ) + I * u) hraw hline

private theorem eventually_shifted_pow_four_mul_exp_le_one
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ T : ℝ in atTop,
      1 ≤ T ∧ (T + 3) ^ 4 * Real.exp (-a * T) ≤ 1 := by
  have hlt : ∀ᶠ T : ℝ in atTop,
      (T + 3) ^ 4 * Real.exp (-a * T) < 1 :=
    (tendsto_order.1 (tendsto_shifted_pow_four_mul_exp_neg ha)).2
      1 (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hlt] with T hT hdecay
  exact ⟨hT, hdecay.le⟩

/-- Absolute integrability of the raw Mellin integrand on a fixed vertical
line of the contour strip.  The exclusion `sigma ≠ 1` removes the zeta pole. -/
theorem integrable_selbergMellinRaw_vertical
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X : ℕ)
    {sigma : ℝ} (hsigma : sigma ∈ Set.Icc (1 / 2 : ℝ) 2)
    (hsigma1 : sigma ≠ 1) :
    Integrable (fun t : ℝ =>
      selbergMellinRawIntegrand (selbergFourierZ delta y) X
        ((sigma : ℂ) + I * t)) := by
  let f : ℝ → ℂ := fun t =>
    selbergMellinRawIntegrand (selbergFourierZ delta y) X
      ((sigma : ℂ) + I * t)
  let a : ℝ := delta / 8
  have ha : 0 < a := by dsimp [a]; positivity
  rcases exists_norm_selbergMellinRaw_horizontal_le
    hdelta0 hdeltaPi y X with ⟨K, hK, hbound⟩
  rcases (eventually_atTop.1
    (eventually_shifted_pow_four_mul_exp_le_one ha)) with ⟨R, hR⟩
  have hRone : 1 ≤ R := (hR R le_rfl).1
  have hcontinuous : Continuous f := by
    exact continuous_selbergMellinRaw_vertical delta y X
      (lt_of_lt_of_le (by norm_num) hsigma.1) hsigma1
  have hrightEnvelope : IntegrableOn
      (fun t : ℝ => K * Real.exp (-a * t)) (Set.Ioi R) := by
    exact (integrableOn_exp_mul_Ioi (c := R)
      (show -a < 0 by linarith)).const_mul K
  have hright : IntegrableOn f (Set.Ioi R) := by
    apply hrightEnvelope.mono' hcontinuous.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htR : R ≤ t := ht.le
    have ht1 : 1 ≤ t := hRone.trans htR
    have ht0 : 0 ≤ t := zero_le_one.trans ht1
    have hsmall := (hR t htR).2
    have hb := hbound sigma t hsigma (by simpa [abs_of_nonneg ht0] using ht1)
    have hsplit : Real.exp (-(delta / 4) * t) =
        Real.exp (-a * t) * Real.exp (-a * t) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [a]
      ring
    change ‖f t‖ ≤ K * Real.exp (-a * t)
    calc
      ‖f t‖ ≤ K * (t + 3) ^ 4 * Real.exp (-(delta / 4) * t) := by
        simpa [f, abs_of_nonneg ht0] using hb
      _ = K * ((t + 3) ^ 4 * Real.exp (-a * t)) *
          Real.exp (-a * t) := by rw [hsplit]; ring
      _ ≤ K * 1 * Real.exp (-a * t) := by
        gcongr
      _ = K * Real.exp (-a * t) := by ring
  have hleftEnvelope : IntegrableOn
      (fun t : ℝ => K * Real.exp (a * t)) (Set.Iic (-R)) := by
    exact (integrableOn_exp_mul_Iic (c := -R) ha).const_mul K
  have hleft : IntegrableOn f (Set.Iic (-R)) := by
    apply hleftEnvelope.mono' hcontinuous.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    change t ≤ -R at ht
    have huR : R ≤ -t := by simpa using neg_le_neg ht
    have hu1 : 1 ≤ -t := hRone.trans huR
    have ht0 : t ≤ 0 := by linarith
    have hsmall := (hR (-t) huR).2
    have hb := hbound sigma t hsigma (by simpa [abs_of_nonpos ht0] using hu1)
    have hsplit : Real.exp (-(delta / 4) * (-t)) =
        Real.exp (-a * (-t)) * Real.exp (-a * (-t)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [a]
      ring
    change ‖f t‖ ≤ K * Real.exp (a * t)
    calc
      ‖f t‖ ≤ K * ((-t) + 3) ^ 4 *
          Real.exp (-(delta / 4) * (-t)) := by
        simpa [f, abs_of_nonpos ht0] using hb
      _ = K * (((-t) + 3) ^ 4 * Real.exp (-a * (-t))) *
          Real.exp (-a * (-t)) := by rw [hsplit]; ring
      _ ≤ K * 1 * Real.exp (-a * (-t)) := by
        gcongr
      _ = K * Real.exp (a * t) := by
        congr 2 <;> ring
  have hmiddle : IntegrableOn f (Set.Icc (-R) R) :=
    hcontinuous.continuousOn.integrableOn_compact isCompact_Icc
  have hunion : Set.Iic (-R) ∪ Set.Icc (-R) R ∪ Set.Ioi R =
      (Set.univ : Set ℝ) := by
    ext t
    simp only [mem_union, mem_Iic, mem_Icc, mem_Ioi, mem_univ, iff_true]
    by_cases ht : t ≤ -R
    · exact Or.inl (Or.inl ht)
    by_cases ht' : t ≤ R
    · exact Or.inl (Or.inr ⟨le_of_not_ge ht, ht'⟩)
    · exact Or.inr (lt_of_not_ge ht')
  rw [← integrableOn_univ, ← hunion]
  exact (hleft.union hmiddle).union hright

/-- Symmetric finite-height vertical integrals converge to the full vertical
integral. -/
theorem tendsto_selbergMellinRaw_vertical_intervalIntegral
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X : ℕ)
    {sigma : ℝ} (hsigma : sigma ∈ Set.Icc (1 / 2 : ℝ) 2)
    (hsigma1 : sigma ≠ 1) :
    Tendsto
      (fun T : ℝ => ∫ t : ℝ in (-T)..T,
        selbergMellinRawIntegrand (selbergFourierZ delta y) X
          ((sigma : ℂ) + I * t))
      atTop
      (𝓝 (∫ t : ℝ,
        selbergMellinRawIntegrand (selbergFourierZ delta y) X
          ((sigma : ℂ) + I * t))) := by
  exact intervalIntegral_tendsto_integral
    (integrable_selbergMellinRaw_vertical hdelta0 hdeltaPi y X hsigma hsigma1)
    tendsto_neg_atTop_atBot tendsto_id

/-- Infinite-height form of Selberg's contour shift.  The factor `I` from
`ds = I dt` cancels the `I` in the residue theorem, leaving `2*pi` times
the residue coefficient. -/
theorem integral_selbergMellinRaw_vertical_sub
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X : ℕ) :
    (∫ t : ℝ, selbergMellinRawIntegrand (selbergFourierZ delta y) X
          ((2 : ℂ) + I * t)) -
        (∫ t : ℝ, selbergMellinRawIntegrand (selbergFourierZ delta y) X
          ((1 / 2 : ℂ) + I * t)) =
      (2 * Real.pi : ℂ) *
        (selbergFourierZ delta y * selbergSqrtZetaPsi X 1 *
          selbergSqrtZetaPsi X 0) := by
  let z := selbergFourierZ delta y
  let F : ℂ → ℂ := selbergMellinRawIntegrand z X
  let V2 : ℂ := ∫ t : ℝ, F ((2 : ℂ) + I * t)
  let Vhalf : ℂ := ∫ t : ℝ, F ((1 / 2 : ℂ) + I * t)
  let residue : ℂ := z * selbergSqrtZetaPsi X 1 *
    selbergSqrtZetaPsi X 0
  let Q : ℝ → ℂ := fun T =>
    MathlibAux.boundaryRectIntegral F (1 / 2) 2 (-T) T
  have hbottom : Tendsto
      (fun T : ℝ => ∫ sigma : ℝ in (1 / 2)..2,
        F ((sigma : ℂ) + (-T : ℝ) * I)) atTop (𝓝 0) := by
    simpa [z, F, sub_eq_add_neg, mul_comm] using
      tendsto_selbergMellinRaw_lower_horizontalIntegral_zero
        hdelta0 hdeltaPi y X
  have htop : Tendsto
      (fun T : ℝ => ∫ sigma : ℝ in (1 / 2)..2,
        F ((sigma : ℂ) + (T : ℝ) * I)) atTop (𝓝 0) := by
    simpa [z, F, mul_comm] using
      tendsto_selbergMellinRaw_upper_horizontalIntegral_zero
        hdelta0 hdeltaPi y X
  have hright : Tendsto
      (fun T : ℝ => ∫ t : ℝ in (-T)..T,
        F ((2 : ℂ) + (t : ℝ) * I)) atTop (𝓝 V2) := by
    simpa [z, F, V2, mul_comm] using
      tendsto_selbergMellinRaw_vertical_intervalIntegral
      hdelta0 hdeltaPi y X
        (show (2 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 2 by norm_num)
        (by norm_num : (2 : ℝ) ≠ 1)
  have hleft : Tendsto
      (fun T : ℝ => ∫ t : ℝ in (-T)..T,
        F ((1 / 2 : ℂ) + (t : ℝ) * I)) atTop (𝓝 Vhalf) := by
    simpa [z, F, Vhalf, mul_comm] using
      tendsto_selbergMellinRaw_vertical_intervalIntegral
      hdelta0 hdeltaPi y X
        (show (1 / 2 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 2 by norm_num)
        (by norm_num : (1 / 2 : ℝ) ≠ 1)
  have hQ : Tendsto Q atTop (𝓝 (I • V2 - I • Vhalf)) := by
    have hcombined := (hbottom.sub htop).add
      (hright.const_smul I) |>.sub (hleft.const_smul I)
    simpa [Q, MathlibAux.boundaryRectIntegral] using hcombined
  have hQeq : ∀ᶠ T : ℝ in atTop,
      Q T = (2 * Real.pi * I) * residue := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact boundaryRectIntegral_selbergMellinRaw
      (selbergFourierZ_ne_zero delta y) X (by norm_num) hT
  have hQconst : Tendsto Q atTop
      (𝓝 ((2 * Real.pi * I) * residue)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hQeq] with T hT
    exact hT.symm
  have hlimit : I • V2 - I • Vhalf =
      (2 * Real.pi * I) * residue :=
    tendsto_nhds_unique hQ hQconst
  change V2 - Vhalf = (2 * Real.pi : ℂ) * residue
  apply mul_left_cancel₀ I_ne_zero
  calc
    I * (V2 - Vhalf) = I • V2 - I • Vhalf := by
      simp only [smul_eq_mul]
      ring
    _ = (2 * Real.pi * I) * residue := hlimit
    _ = I * ((2 * Real.pi : ℂ) * residue) := by ring

/-- Selberg's `1/(4*pi)` vertical normalization gives exactly half the
residue after the infinite-height contour shift. -/
theorem normalized_integral_selbergMellinRaw_vertical_sub
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X : ℕ) :
    (1 / (4 * Real.pi) : ℂ) *
      ((∫ t : ℝ, selbergMellinRawIntegrand (selbergFourierZ delta y) X
            ((2 : ℂ) + I * t)) -
        (∫ t : ℝ, selbergMellinRawIntegrand (selbergFourierZ delta y) X
            ((1 / 2 : ℂ) + I * t))) =
      (1 / 2 : ℂ) *
        (selbergFourierZ delta y * selbergSqrtZetaPsi X 1 *
          selbergSqrtZetaPsi X 0) := by
  rw [integral_selbergMellinRaw_vertical_sub hdelta0 hdeltaPi y X]
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi]
  ring

end HardyTheorem
