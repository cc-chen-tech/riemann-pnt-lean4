import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Function MeasureTheory Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The mass-one Gaussian used in the localized contour argument. -/
def normalizedGaussian (m t : ℝ) : ℝ :=
  Real.exp (-t ^ 2 / (4 * m)) / (2 * Real.sqrt (Real.pi * m))

/-- The pointwise derivative of `normalizedGaussian m`. -/
def normalizedGaussianDeriv (m t : ℝ) : ℝ :=
  -(t / (2 * m)) * normalizedGaussian m t

/-- The mean of a real function over one period. -/
def periodicMean (f : ℝ → ℝ) (P : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..P, f t) / P

theorem normalizedGaussian_pos {m : ℝ} (hm : 0 < m) (t : ℝ) :
    0 < normalizedGaussian m t := by
  unfold normalizedGaussian
  positivity

theorem hasDerivAt_normalizedGaussian {m : ℝ} (hm : 0 < m) (t : ℝ) :
    HasDerivAt (normalizedGaussian m)
      (normalizedGaussianDeriv m t) t := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hinner :
      HasDerivAt (fun x : ℝ => -x ^ 2 / (4 * m))
        (-(t / (2 * m))) t := by
    convert ((hasDerivAt_pow 2 t).neg.div_const (4 * m)) using 1 <;>
      field_simp <;> ring
  have hexp :
      HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 / (4 * m)))
        (-(t / (2 * m)) * Real.exp (-t ^ 2 / (4 * m))) t := by
    simpa only [mul_comm] using hinner.exp
  convert hexp.div_const (2 * Real.sqrt (Real.pi * m)) using 1 <;>
    simp only [normalizedGaussian, normalizedGaussianDeriv] <;> ring

theorem integrable_normalizedGaussian {m : ℝ} (hm : 0 < m) :
    Integrable (normalizedGaussian m) := by
  have hb : 0 < (1 / (4 * m) : ℝ) := by positivity
  have hbase := integrable_exp_neg_mul_sq hb
  have hconst := hbase.div_const (2 * Real.sqrt (Real.pi * m))
  convert hconst using 1
  ext t
  simp only [normalizedGaussian]
  congr 2
  field_simp

theorem integral_normalizedGaussian {m : ℝ} (hm : 0 < m) :
    ∫ t : ℝ, normalizedGaussian m t = 1 := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hb : 0 < (1 / (4 * m) : ℝ) := by positivity
  have hpim : 0 < Real.pi * m := mul_pos Real.pi_pos hm
  have hradicand :
      Real.pi / (1 / (4 * m)) = 4 * (Real.pi * m) := by
    field_simp
  have hsqrt :
      Real.sqrt (Real.pi / (1 / (4 * m))) =
        2 * Real.sqrt (Real.pi * m) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
    rw [Real.sq_sqrt (div_nonneg Real.pi_pos.le hb.le),
      mul_pow, Real.sq_sqrt hpim.le, hradicand]
    ring
  simp_rw [normalizedGaussian]
  rw [integral_div]
  have hfun :
      (fun t : ℝ => Real.exp (-t ^ 2 / (4 * m))) =
        (fun t : ℝ => Real.exp (-(1 / (4 * m)) * t ^ 2)) := by
    funext t
    congr 1
    field_simp
  rw [hfun, integral_gaussian, hsqrt]
  field_simp [Real.sqrt_ne_zero'.mpr hpim]

theorem integrable_normalizedGaussianDeriv {m : ℝ} (hm : 0 < m) :
    Integrable (normalizedGaussianDeriv m) := by
  have hb : 0 < (1 / (4 * m) : ℝ) := by positivity
  have hbase := integrable_mul_exp_neg_mul_sq hb
  have hscale :
      normalizedGaussianDeriv m =
        fun t : ℝ =>
          (-1 / (4 * m * Real.sqrt (Real.pi * m))) *
            (t * Real.exp (-(1 / (4 * m)) * t ^ 2)) := by
    funext t
    simp only [normalizedGaussianDeriv, normalizedGaussian]
    field_simp
    <;> ring
  rw [hscale]
  exact hbase.const_mul _

private theorem normalizedGaussian_tendsto_atTop {m : ℝ} (hm : 0 < m) :
    Tendsto (normalizedGaussian m) atTop (𝓝 0) := by
  exact tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
    (fun t _ => hasDerivAt_normalizedGaussian hm t)
    (integrable_normalizedGaussianDeriv hm).integrableOn
    (integrable_normalizedGaussian hm).integrableOn

private theorem normalizedGaussian_tendsto_atBot {m : ℝ} (hm : 0 < m) :
    Tendsto (normalizedGaussian m) atBot (𝓝 0) := by
  exact tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
    (fun t _ => hasDerivAt_normalizedGaussian hm t)
    (integrable_normalizedGaussianDeriv hm).integrableOn
    (integrable_normalizedGaussian hm).integrableOn

theorem integral_abs_normalizedGaussianDeriv_le_inv_sqrt
    {m : ℝ} (hm : 0 < m) :
    (∫ t : ℝ, |normalizedGaussianDeriv m t|) ≤
      1 / Real.sqrt m := by
  have hderivInt := integrable_normalizedGaussianDeriv hm
  have hleftSign :
      ∀ t ∈ Set.Iic (0 : ℝ), 0 ≤ normalizedGaussianDeriv m t := by
    intro t ht
    rw [normalizedGaussianDeriv]
    exact mul_nonneg (by
      have hden : 0 < 2 * m := mul_pos (by norm_num) hm
      exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg ht hden.le))
      (normalizedGaussian_pos hm t).le
  have hrightSign :
      ∀ t ∈ Set.Ioi (0 : ℝ), normalizedGaussianDeriv m t ≤ 0 := by
    intro t ht
    rw [normalizedGaussianDeriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by
      have hden : 0 < 2 * m := mul_pos (by norm_num) hm
      exact neg_nonpos.mpr (div_nonneg ht.le hden.le))
      (normalizedGaussian_pos hm t).le
  have hleft :
      (∫ t : ℝ in Set.Iic 0, |normalizedGaussianDeriv m t|) =
        normalizedGaussian m 0 := by
    calc
      (∫ t : ℝ in Set.Iic 0, |normalizedGaussianDeriv m t|) =
          ∫ t : ℝ in Set.Iic 0, normalizedGaussianDeriv m t := by
            apply setIntegral_congr_fun measurableSet_Iic
            intro t ht
            exact abs_of_nonneg (hleftSign t ht)
      _ = normalizedGaussian m 0 - 0 :=
        integral_Iic_of_hasDerivAt_of_tendsto'
          (fun t _ => hasDerivAt_normalizedGaussian hm t)
          hderivInt.integrableOn
          (normalizedGaussian_tendsto_atBot hm)
      _ = normalizedGaussian m 0 := sub_zero _
  have hright :
      (∫ t : ℝ in Set.Ioi 0, |normalizedGaussianDeriv m t|) =
        normalizedGaussian m 0 := by
    calc
      (∫ t : ℝ in Set.Ioi 0, |normalizedGaussianDeriv m t|) =
          ∫ t : ℝ in Set.Ioi 0, -normalizedGaussianDeriv m t := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            exact abs_of_nonpos (hrightSign t ht)
      _ = -(∫ t : ℝ in Set.Ioi 0, normalizedGaussianDeriv m t) := by
        rw [integral_neg]
      _ = -(0 - normalizedGaussian m 0) := by
        rw [integral_Ioi_of_hasDerivAt_of_tendsto'
          (fun t _ => hasDerivAt_normalizedGaussian hm t)
          hderivInt.integrableOn
          (normalizedGaussian_tendsto_atTop hm)]
      _ = normalizedGaussian m 0 := by ring
  have habsInt : Integrable (fun t : ℝ => |normalizedGaussianDeriv m t|) :=
    hderivInt.abs
  have hsplit :
      (∫ t : ℝ, |normalizedGaussianDeriv m t|) =
        (∫ t : ℝ in Set.Iic 0, |normalizedGaussianDeriv m t|) +
          ∫ t : ℝ in Set.Ioi 0, |normalizedGaussianDeriv m t| := by
    rw [← setIntegral_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)),
      setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        habsInt.integrableOn habsInt.integrableOn]
  rw [hsplit, hleft, hright, normalizedGaussian]
  have hpi : (1 : ℝ) ≤ Real.pi := by
    linarith [Real.two_le_pi]
  have hmle : m ≤ Real.pi * m := by
    nlinarith
  have hsqrtle : Real.sqrt m ≤ Real.sqrt (Real.pi * m) :=
    Real.sqrt_le_sqrt hmle
  have hinv :
      1 / Real.sqrt (Real.pi * m) ≤ 1 / Real.sqrt m :=
    one_div_le_one_div_of_le (Real.sqrt_pos.2 hm) hsqrtle
  have hpim : 0 < Real.pi * m := mul_pos Real.pi_pos hm
  calc
    Real.exp (-0 ^ 2 / (4 * m)) / (2 * Real.sqrt (Real.pi * m)) +
        Real.exp (-0 ^ 2 / (4 * m)) / (2 * Real.sqrt (Real.pi * m)) =
        1 / Real.sqrt (Real.pi * m) := by
          simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), neg_zero,
            zero_div, Real.exp_zero]
          field_simp [Real.sqrt_ne_zero'.mpr hpim]
          norm_num
    _ ≤ 1 / Real.sqrt m := hinv

private def centeredPeriodicFunction (f : ℝ → ℝ) (P : ℝ) (t : ℝ) : ℝ :=
  f t - periodicMean f P

private def centeredPeriodicPrimitive (f : ℝ → ℝ) (P : ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, centeredPeriodicFunction f P t

private theorem centeredPeriodicFunction_periodic
    {f : ℝ → ℝ} {P : ℝ} (hperiodic : Function.Periodic f P) :
    Function.Periodic (centeredPeriodicFunction f P) P := by
  intro x
  simp only [centeredPeriodicFunction]
  rw [hperiodic x]

private theorem centeredPeriodicFunction_continuous
    {f : ℝ → ℝ} {P : ℝ} (hcontinuous : Continuous f) :
    Continuous (centeredPeriodicFunction f P) := by
  exact hcontinuous.sub continuous_const

private theorem integral_centeredPeriodicFunction_period_eq_zero
    {f : ℝ → ℝ} {P : ℝ} (hP : 0 < P)
    (hcontinuous : Continuous f) :
    ∫ t in (0 : ℝ)..P, centeredPeriodicFunction f P t = 0 := by
  rw [show centeredPeriodicFunction f P =
      fun t => f t - periodicMean f P by rfl]
  rw [intervalIntegral.integral_sub
    (hcontinuous.intervalIntegrable 0 P) intervalIntegrable_const]
  simp only [periodicMean, intervalIntegral.integral_const, sub_zero,
    smul_eq_mul]
  field_simp
  ring

private theorem centeredPeriodicPrimitive_periodic
    {f : ℝ → ℝ} {P : ℝ} (hP : 0 < P)
    (hperiodic : Function.Periodic f P)
    (hcontinuous : Continuous f) :
    Function.Periodic (centeredPeriodicPrimitive f P) P := by
  let g := centeredPeriodicFunction f P
  have hgPeriodic : Function.Periodic g P :=
    centeredPeriodicFunction_periodic hperiodic
  have hgContinuous : Continuous g :=
    centeredPeriodicFunction_continuous hcontinuous
  have hgInt : ∀ a b : ℝ, IntervalIntegrable g volume a b :=
    fun a b => hgContinuous.intervalIntegrable a b
  have hgPeriodZero : ∫ t in (0 : ℝ)..P, g t = 0 :=
    integral_centeredPeriodicFunction_period_eq_zero hP hcontinuous
  intro x
  change (∫ t in (0 : ℝ)..x + P, g t) = ∫ t in (0 : ℝ)..x, g t
  calc
    (∫ t in (0 : ℝ)..x + P, g t) =
        (∫ t in (0 : ℝ)..x, g t) + ∫ t in x..x + P, g t :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hgInt 0 x) (hgInt x (x + P))).symm
    _ = (∫ t in (0 : ℝ)..x, g t) + ∫ t in (0 : ℝ)..P, g t := by
      rw [hgPeriodic.intervalIntegral_add_eq x 0, zero_add]
    _ = ∫ t in (0 : ℝ)..x, g t := by rw [hgPeriodZero, add_zero]

private theorem centeredPeriodicPrimitive_continuous
    {f : ℝ → ℝ} {P : ℝ} (hcontinuous : Continuous f) :
    Continuous (centeredPeriodicPrimitive f P) := by
  exact intervalIntegral.continuous_primitive
    (fun a b =>
      (centeredPeriodicFunction_continuous hcontinuous).intervalIntegrable a b)
    0

private theorem hasDerivAt_centeredPeriodicPrimitive
    {f : ℝ → ℝ} {P x : ℝ} (hcontinuous : Continuous f) :
    HasDerivAt (centeredPeriodicPrimitive f P)
      (centeredPeriodicFunction f P x) x := by
  exact ((centeredPeriodicFunction_continuous hcontinuous).integral_hasStrictDerivAt
    0 x).hasDerivAt

private theorem exists_centeredPeriodicPrimitive_bound
    {f : ℝ → ℝ} {P : ℝ} (hP : 0 < P)
    (hperiodic : Function.Periodic f P)
    (hcontinuous : Continuous f) :
    ∃ B ≥ 0, ∀ x : ℝ, |centeredPeriodicPrimitive f P x| ≤ B := by
  have hbounded :=
    Function.Periodic.isBounded_of_continuous
      (centeredPeriodicPrimitive_periodic hP hperiodic hcontinuous)
      hP.ne' (centeredPeriodicPrimitive_continuous hcontinuous)
  rcases hbounded.exists_norm_le with ⟨B, hB⟩
  refine ⟨B, ?_, ?_⟩
  · exact (norm_nonneg (centeredPeriodicPrimitive f P 0)).trans
      (hB _ ⟨0, rfl⟩)
  · intro x
    simpa using hB (centeredPeriodicPrimitive f P x) (Set.mem_range_self x)

private theorem integrable_mul_of_integrable_left_of_bounded
    {g h : ℝ → ℝ} {B : ℝ}
    (hg : Integrable g) (hh : Continuous h)
    (hB : ∀ x, |h x| ≤ B) :
    Integrable (fun x => g x * h x) := by
  exact hg.mul_bdd hh.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hB x)

private theorem integrable_mul_of_bounded_left_of_integrable
    {g h : ℝ → ℝ} {B : ℝ}
    (hg : Continuous g) (hB : ∀ x, |g x| ≤ B)
    (hh : Integrable h) :
    Integrable (fun x => g x * h x) := by
  exact hh.bdd_mul hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hB x)

theorem exists_uniform_normalizedGaussian_periodicMean_bound
    {f : ℝ → ℝ} {P : ℝ}
    (hP : 0 < P) (hperiodic : Function.Periodic f P)
    (hcontinuous : Continuous f) :
    ∃ C ≥ 0, ∀ {m : ℝ}, 1 ≤ m → ∀ c : ℝ,
      |(∫ t : ℝ, normalizedGaussian m t * f (c - t)) -
          periodicMean f P| ≤ C / Real.sqrt m := by
  let g := centeredPeriodicFunction f P
  let F := centeredPeriodicPrimitive f P
  have hgContinuous : Continuous g :=
    centeredPeriodicFunction_continuous hcontinuous
  have hgPeriodic : Function.Periodic g P :=
    centeredPeriodicFunction_periodic hperiodic
  have hFContinuous : Continuous F :=
    centeredPeriodicPrimitive_continuous hcontinuous
  obtain ⟨B, hBnonneg, hFBound⟩ :=
    exists_centeredPeriodicPrimitive_bound hP hperiodic hcontinuous
  have hgBounded :=
    Function.Periodic.isBounded_of_continuous
      hgPeriodic hP.ne' hgContinuous
  rcases hgBounded.exists_norm_le with ⟨D, hDBound⟩
  refine ⟨B, hBnonneg, ?_⟩
  intro m hmOne c
  have hm : 0 < m := zero_lt_one.trans_le hmOne
  let H : ℝ → ℝ := fun t => -F (c - t)
  let gShift : ℝ → ℝ := fun t => g (c - t)
  have hHContinuous : Continuous H := by
    exact (hFContinuous.comp (continuous_const.sub continuous_id)).neg
  have hgShiftContinuous : Continuous gShift :=
    hgContinuous.comp (continuous_const.sub continuous_id)
  have hHBound : ∀ t : ℝ, |H t| ≤ B := by
    intro t
    simpa [H] using hFBound (c - t)
  have hgShiftBound : ∀ t : ℝ, |gShift t| ≤ D := by
    intro t
    simpa [gShift, Real.norm_eq_abs] using
      hDBound (g (c - t)) ⟨c - t, rfl⟩
  have hHDeriv : ∀ t : ℝ, HasDerivAt H (gShift t) t := by
    intro t
    have hcomp :=
      (hasDerivAt_centeredPeriodicPrimitive
        (f := f) (P := P) (x := c - t) hcontinuous).comp t
        ((hasDerivAt_const t c).sub (hasDerivAt_id t))
    convert hcomp.neg using 1 <;>
      simp only [gShift, g] <;> ring
  have hGaussianContinuous : Continuous (normalizedGaussian m) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hasDerivAt_normalizedGaussian hm t).continuousAt
  have hGaussianInt := integrable_normalizedGaussian hm
  have hGaussianDerivInt := integrable_normalizedGaussianDeriv hm
  have hHGaussianDerivInt :
      Integrable (fun t => H t * normalizedGaussianDeriv m t) :=
    integrable_mul_of_bounded_left_of_integrable
      hHContinuous hHBound hGaussianDerivInt
  have hgShiftGaussianInt :
      Integrable (fun t => gShift t * normalizedGaussian m t) :=
    integrable_mul_of_bounded_left_of_integrable
      hgShiftContinuous hgShiftBound hGaussianInt
  have hHGaussianInt :
      Integrable (fun t => H t * normalizedGaussian m t) :=
    integrable_mul_of_bounded_left_of_integrable
      hHContinuous hHBound hGaussianInt
  have hibp :
      (∫ t : ℝ, H t * normalizedGaussianDeriv m t) =
        -(∫ t : ℝ, gShift t * normalizedGaussian m t) :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := H) (u' := gShift)
      (v := normalizedGaussian m) (v' := normalizedGaussianDeriv m)
      (fun t _ => hHDeriv t)
      (fun t _ => hasDerivAt_normalizedGaussian hm t)
      hHGaussianDerivInt hgShiftGaussianInt hHGaussianInt
  have hcenteredEq :
      (∫ t : ℝ, normalizedGaussian m t * gShift t) =
        -(∫ t : ℝ, H t * normalizedGaussianDeriv m t) := by
    have hcomm :
        (∫ t : ℝ, normalizedGaussian m t * gShift t) =
          ∫ t : ℝ, gShift t * normalizedGaussian m t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by ring
    rw [hcomm]
    linarith
  have hmajorantInt :
      Integrable (fun t : ℝ => B * |normalizedGaussianDeriv m t|) :=
    hGaussianDerivInt.abs.const_mul B
  have hfilteredBound :
      |∫ t : ℝ, H t * normalizedGaussianDeriv m t| ≤
        B * (∫ t : ℝ, |normalizedGaussianDeriv m t|) := by
    calc
      |∫ t : ℝ, H t * normalizedGaussianDeriv m t| ≤
          ∫ t : ℝ, B * |normalizedGaussianDeriv m t| := by
        change ‖∫ t : ℝ, H t * normalizedGaussianDeriv m t‖ ≤
          ∫ t : ℝ, B * |normalizedGaussianDeriv m t|
        apply norm_integral_le_of_norm_le hmajorantInt
        exact Filter.Eventually.of_forall fun t => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (hHBound t) (abs_nonneg _)
      _ = B * (∫ t : ℝ, |normalizedGaussianDeriv m t|) := by
        rw [integral_const_mul]
  have hcenteredBound :
      |∫ t : ℝ, normalizedGaussian m t * gShift t| ≤
        B / Real.sqrt m := by
    rw [hcenteredEq, abs_neg]
    calc
      |∫ t : ℝ, H t * normalizedGaussianDeriv m t| ≤
          B * (∫ t : ℝ, |normalizedGaussianDeriv m t|) :=
        hfilteredBound
      _ ≤ B * (1 / Real.sqrt m) :=
        mul_le_mul_of_nonneg_left
          (integral_abs_normalizedGaussianDeriv_le_inv_sqrt hm)
          hBnonneg
      _ = B / Real.sqrt m := by ring
  have hmeanGaussianInt :
      Integrable (fun t : ℝ => periodicMean f P * normalizedGaussian m t) :=
    hGaussianInt.const_mul _
  have haverageDecomp :
      (∫ t : ℝ, normalizedGaussian m t * f (c - t)) =
        (∫ t : ℝ, normalizedGaussian m t * gShift t) +
          periodicMean f P := by
    have hpoint :
        (fun t : ℝ => normalizedGaussian m t * f (c - t)) =
          fun t =>
            normalizedGaussian m t * gShift t +
              periodicMean f P * normalizedGaussian m t := by
      funext t
      simp only [gShift, g, centeredPeriodicFunction]
      ring
    rw [hpoint, integral_add]
    · rw [integral_const_mul, integral_normalizedGaussian hm, mul_one]
    · exact hgShiftGaussianInt.congr
        (Filter.Eventually.of_forall fun t => by ring)
    · exact hmeanGaussianInt
  rw [haverageDecomp, add_sub_cancel_right]
  exact hcenteredBound

theorem eventually_uniform_normalizedGaussian_periodicMean
    {f : ℝ → ℝ} {P : ℝ}
    (hP : 0 < P) (hperiodic : Function.Periodic f P)
    (hcontinuous : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∀ c : ℝ,
      |(∫ t : ℝ, normalizedGaussian m t * f (c - t)) -
          periodicMean f P| < ε := by
  obtain ⟨C, _hCnonneg, hC⟩ :=
    exists_uniform_normalizedGaussian_periodicMean_bound
      hP hperiodic hcontinuous
  have hratio :
      Tendsto (fun m : ℝ => C / Real.sqrt m) atTop (𝓝 0) :=
    Real.tendsto_sqrt_atTop.const_div_atTop C
  have hratioSmall : ∀ᶠ m : ℝ in atTop, C / Real.sqrt m < ε :=
    (tendsto_order.1 hratio).2 _ hε
  filter_upwards [eventually_ge_atTop (1 : ℝ), hratioSmall] with m hm hsmall
  intro c
  exact (hC hm c).trans_lt hsmall

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
