import HardyTheorem.ConreyEquation41Global
import MathlibAux.ContinuousLogPhaseLimits

/-!
# Finite phase endpoints of actual eta components

For `g ≠ 0`, eta has finite analytic order at every endpoint, including
nonzeros (order zero). Local factor logarithms transfer finite imaginary
limits to any chosen logarithm on a zero-free open component. No value of
that component logarithm at a zero endpoint is used.
-/

open Complex Set Filter Topology

namespace HardyTheorem

private theorem exists_conreyDegreeOneEta_component_left_argument_limit
    {g g0 g1 L a b : ℝ} {ell : ℝ → ℂ} (hg : g ≠ 0) (hab : a < b)
    (hell : ContinuousOn ell (Ioo a b))
    (hexp : ∀ t ∈ Ioo a b, Complex.exp (ell t) =
      conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t)) :
    ∃ A : ℝ, Tendsto (fun t => (ell t).im) (nhdsWithin a (Ioi a)) (nhds A) := by
  let m := analyticOrderNatAt (conreyDegreeOneEta g g0 g1 L) (conreyCriticalPoint a)
  have horder : analyticOrderAt (conreyDegreeOneEta g g0 g1 L)
      (conreyCriticalPoint a) = m :=
    (Nat.cast_analyticOrderNatAt
      (analyticOrderAt_conreyDegreeOneEta_ne_top_of_g_ne_zero hg _)).symm
  obtain ⟨delta, reg, hdelta, hreg, _, hrightExp, _⟩ :=
    exists_conreyDegreeOneEta_local_argument_bridge horder
  let c := min b (a + delta)
  have hac : a < c := lt_min hab (by linarith)
  have hsub : Ioo a c ⊆ Ioo a b :=
    Ioo_subset_Ioo le_rfl (min_le_left _ _)
  have hsubReg : Ioo a c ⊆ Ioo (a - delta) (a + delta) := by
    intro t ht
    exact ⟨by linarith [ht.1], lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  let model : ℝ → ℂ := fun t => MathlibAux.verticalPowerRightLog m (t - a) + reg t
  have hmodel : ContinuousOn model (Ioo a c) := by
    apply ContinuousOn.add _ (hreg.mono hsubReg)
    intro t ht
    have hlog : ContinuousAt (fun t : ℝ => Real.log (t - a)) t :=
      (continuousAt_id.sub continuousAt_const).log
        (sub_ne_zero.mpr (ne_of_gt ht.1))
    exact (continuousAt_const.mul
      ((Complex.continuous_ofReal.continuousAt.comp hlog).add
        continuousAt_const)).continuousWithinAt
  have hregAt : ContinuousAt reg a :=
    hreg.continuousAt (isOpen_Ioo.mem_nhds (by constructor <;> linarith))
  have hregIm : Tendsto (fun t => (reg t).im)
      (nhdsWithin a (Ioi a)) (nhds (reg a).im) :=
    (Complex.continuous_im.continuousAt.comp hregAt).tendsto.mono_left
      nhdsWithin_le_nhds
  have hlim : Tendsto (fun t => (model t).im) (nhdsWithin a (Ioi a))
      (nhds ((m : ℝ) * (Real.pi / 2) + (reg a).im)) := by
    simpa [model, MathlibAux.verticalPowerRightLog, Complex.mul_im] using
      hregIm.const_add ((m : ℝ) * (Real.pi / 2))
  have heq : ∀ t ∈ Ioo a c, Complex.exp (ell t) = Complex.exp (model t) := by
    intro t ht
    rw [hexp t (hsub ht)]
    exact (hrightExp t ⟨ht.1, (hsubReg ht).2⟩).symm
  obtain ⟨k, hk⟩ := MathlibAux.exists_int_tendsto_im_continuousLog
    hac (hell.mono hsub) hmodel heq (Ioo_mem_nhdsGT hac) hlim
  exact ⟨_, hk⟩

private theorem exists_conreyDegreeOneEta_component_right_argument_limit
    {g g0 g1 L a b : ℝ} {ell : ℝ → ℂ} (hg : g ≠ 0) (hab : a < b)
    (hell : ContinuousOn ell (Ioo a b))
    (hexp : ∀ t ∈ Ioo a b, Complex.exp (ell t) =
      conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t)) :
    ∃ B : ℝ, Tendsto (fun t => (ell t).im) (nhdsWithin b (Iio b)) (nhds B) := by
  let m := analyticOrderNatAt (conreyDegreeOneEta g g0 g1 L) (conreyCriticalPoint b)
  have horder : analyticOrderAt (conreyDegreeOneEta g g0 g1 L)
      (conreyCriticalPoint b) = m :=
    (Nat.cast_analyticOrderNatAt
      (analyticOrderAt_conreyDegreeOneEta_ne_top_of_g_ne_zero hg _)).symm
  obtain ⟨delta, reg, hdelta, hreg, hleftExp, _, _⟩ :=
    exists_conreyDegreeOneEta_local_argument_bridge horder
  let c := max a (b - delta)
  have hcb : c < b := max_lt hab (by linarith)
  have hsub : Ioo c b ⊆ Ioo a b :=
    Ioo_subset_Ioo (le_max_left _ _) le_rfl
  have hsubReg : Ioo c b ⊆ Ioo (b - delta) (b + delta) := by
    intro t ht
    exact ⟨lt_of_le_of_lt (le_max_right _ _) ht.1, by linarith [ht.2]⟩
  let model : ℝ → ℂ := fun t => MathlibAux.verticalPowerLeftLog m (b - t) + reg t
  have hmodel : ContinuousOn model (Ioo c b) := by
    apply ContinuousOn.add _ (hreg.mono hsubReg)
    intro t ht
    have hlog : ContinuousAt (fun t : ℝ => Real.log (b - t)) t :=
      (Real.continuousAt_log (sub_ne_zero.mpr (ne_of_gt ht.2))).comp
        (continuousAt_const.sub continuousAt_id)
    exact (continuousAt_const.mul
      ((Complex.continuous_ofReal.continuousAt.comp hlog).add
        continuousAt_const)).continuousWithinAt
  have hregAt : ContinuousAt reg b :=
    hreg.continuousAt (isOpen_Ioo.mem_nhds (by constructor <;> linarith))
  have hregIm : Tendsto (fun t => (reg t).im)
      (nhdsWithin b (Iio b)) (nhds (reg b).im) :=
    (Complex.continuous_im.continuousAt.comp hregAt).tendsto.mono_left
      nhdsWithin_le_nhds
  have hlim : Tendsto (fun t => (model t).im) (nhdsWithin b (Iio b))
      (nhds ((m : ℝ) * (-Real.pi / 2) + (reg b).im)) := by
    simpa [model, MathlibAux.verticalPowerLeftLog, Complex.mul_im] using
      hregIm.const_add ((m : ℝ) * (-Real.pi / 2))
  have heq : ∀ t ∈ Ioo c b, Complex.exp (ell t) = Complex.exp (model t) := by
    intro t ht
    rw [hexp t (hsub ht)]
    exact (hleftExp t ⟨(hsubReg ht).1, ht.2⟩).symm
  obtain ⟨k, hk⟩ := MathlibAux.exists_int_tendsto_im_continuousLog
    hcb (hell.mono hsub) hmodel heq (Ioo_mem_nhdsLT hcb) hlim
  exact ⟨_, hk⟩

/-- Any supplied component logarithm of actual eta has finite phase limits
at both endpoints. The endpoints themselves may be zeros of any finite order. -/
theorem exists_conreyDegreeOneEta_component_argument_limits
    {g g0 g1 L a b : ℝ} {ell : ℝ → ℂ} (hg : g ≠ 0) (hab : a < b)
    (hell : ContinuousOn ell (Ioo a b))
    (hexp : ∀ t ∈ Ioo a b, Complex.exp (ell t) =
      conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t)) :
    ∃ A B : ℝ,
      Tendsto (fun t => (ell t).im) (nhdsWithin a (Ioi a)) (nhds A) ∧
      Tendsto (fun t => (ell t).im) (nhdsWithin b (Iio b)) (nhds B) := by
  obtain ⟨A, hA⟩ := exists_conreyDegreeOneEta_component_left_argument_limit
    hg hab hell hexp
  obtain ⟨B, hB⟩ := exists_conreyDegreeOneEta_component_right_argument_limit
    hg hab hell hexp
  exact ⟨A, B, hA, hB⟩

/-- A zero-free open component of actual eta admits a continuous logarithm
and two finite phase endpoints, without any boundary nonvanishing assumption. -/
theorem exists_conreyDegreeOneEta_continuousLog_with_argument_limits
    {g g0 g1 L a b : ℝ} (hg : g ≠ 0) (hab : a < b)
    (hne : ∀ t ∈ Ioo a b,
      conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) ≠ 0) :
    ∃ ell : ℝ → ℂ, ∃ A B : ℝ,
      ContinuousOn ell (Ioo a b) ∧
      (∀ t ∈ Ioo a b, Complex.exp (ell t) =
        conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t)) ∧
      Tendsto (fun t => (ell t).im) (nhdsWithin a (Ioi a)) (nhds A) ∧
      Tendsto (fun t => (ell t).im) (nhdsWithin b (Iio b)) (nhds B) := by
  have hcritical : Continuous conreyCriticalPoint := by
    unfold conreyCriticalPoint
    fun_prop
  have hcontinuous : ContinuousOn
      (fun t => conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t)) (Ioo a b) := by
    intro t _
    exact ((analyticAt_conreyDegreeOneEta g g0 g1 L
      (conreyCriticalPoint t)).continuousAt.comp hcritical.continuousAt).continuousWithinAt
  obtain ⟨ell, hell, hexp⟩ := MathlibAux.exists_continuousLogOn_Ioo hab hcontinuous hne
  obtain ⟨A, B, hA, hB⟩ := exists_conreyDegreeOneEta_component_argument_limits
    hg hab hell hexp
  exact ⟨ell, A, B, hell, hexp, hA, hB⟩

end HardyTheorem
