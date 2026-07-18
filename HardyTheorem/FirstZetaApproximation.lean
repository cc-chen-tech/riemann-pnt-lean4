import HardyTheorem.OscillatoryIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ZetaValues
import ZeroFreeRegion.MeromorphicAux

open Complex MeasureTheory Set
open Filter Asymptotics

namespace HardyTheorem

private noncomputable def centeredFloorError (x : ℝ) : ℝ :=
  ((⌊x⌋₊ : ℝ) - x) + 1 / 2

private noncomputable def localCenteredBernoulliOne (n : ℕ) (x : ℝ) : ℝ :=
  -bernoulliFun 1 (x - n)

private lemma centeredFloorError_ae_eq_localCenteredBernoulliOne (n : ℕ) :
    centeredFloorError =ᵐ[volume.restrict (Set.Ioc (n : ℝ) (n + 1 : ℕ))]
      localCenteredBernoulliOne n := by
  have hend : ∀ᵐ x : ℝ, x ≠ (n + 1 : ℕ) := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hend] with x hx hne
  have hxIco : x ∈ Set.Ico (n : ℝ) (n + 1 : ℕ) :=
    ⟨hx.1.le, lt_of_le_of_ne hx.2 hne⟩
  have hxIco' : x ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hxIco
  have hfloor : ⌊x⌋₊ = n := Nat.floor_eq_on_Ico n x hxIco'
  simp only [centeredFloorError, localCenteredBernoulliOne, hfloor,
    bernoulliFun_one]
  ring

private lemma periodizedBernoulli_two_ae_eq_local (n : ℕ) :
    (fun x : ℝ => periodizedBernoulli 2 (x : AddCircle (1 : ℝ))) =ᵐ[
      volume.restrict (Set.Ioc (n : ℝ) (n + 1 : ℕ))]
      (fun x : ℝ => bernoulliFun 2 (x - n)) := by
  have hend : ∀ᵐ x : ℝ, x ≠ (n + 1 : ℕ) := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hend] with x hx hne
  have hx' : (n : ℝ) < x ∧ x ≤ (n : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hx
  have hy : x - (n : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
    constructor
    · linarith [hx'.1]
    · have hxlt : x < (n + 1 : ℕ) := lt_of_le_of_ne hx.2 hne
      push_cast at hxlt
      linarith
  have hcoe : (x : AddCircle (1 : ℝ)) =
      ((x - (n : ℝ)) : AddCircle (1 : ℝ)) := by
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    change x - (x - (n : ℝ)) ∈ AddSubgroup.zmultiples (1 : ℝ)
    rw [sub_sub_cancel]
    exact ⟨n, by simp⟩
  rw [hcoe, periodizedBernoulli]
  exact AddCircle.liftIco_coe_apply (show x - (n : ℝ) ∈ Set.Ico 0 (0 + 1) by
    simpa only [zero_add] using hy)

private lemma intervalIntegral_centeredFloorError_cpow_eq_bernoulliTwo_unit
    {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    (∫ x in (n : ℝ)..(n + 1 : ℕ),
      ((centeredFloorError x : ℝ) : ℂ) *
        (x : ℂ) ^ (-(s + 1))) =
      ((n : ℂ) ^ (-(s + 1)) - (n + 1 : ℕ) ^ (-(s + 1))) / 12 -
        (s + 1) / 2 *
          ∫ x in (n : ℝ)..(n + 1 : ℕ),
            ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
              (x : ℂ) ^ (-(s + 2)) := by
  let K : ℝ → ℂ := fun x => (x : ℂ) ^ (-(s + 1))
  let K' : ℝ → ℂ := fun x => (-(s + 1)) * (x : ℂ) ^ (-(s + 2))
  let H : ℝ → ℝ := fun x => -bernoulliFun 2 (x - n) / 2
  let D : ℝ → ℝ := localCenteredBernoulliOne n
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hnn : (n : ℝ) ≤ (n + 1 : ℕ) := by norm_num
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, one_re, zero_re] at hre
    linarith
  have hK_deriv : ∀ x ∈ Set.Icc (n : ℝ) (n + 1 : ℕ),
      HasDerivAt K (K' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hnpos.trans_le hx.1)
    dsimp only [K, K']
    convert hasDerivAt_ofReal_cpow_const hx0 (neg_ne_zero.mpr hs1) using 1
    all_goals ring_nf
  have hD_deriv : ∀ x ∈ Set.Icc (n : ℝ) (n + 1 : ℕ),
      HasDerivAt H (D x) x := by
    intro x _hx
    have hsub : HasDerivAt (fun y : ℝ => y - (n : ℝ)) 1 x :=
      (hasDerivAt_id x).sub_const (n : ℝ)
    have hB := (hasDerivAt_bernoulliFun 2 (x - n)).comp x hsub
    dsimp only [H, D, localCenteredBernoulliOne]
    convert hB.neg.div_const 2 using 1
    all_goals simp only [Nat.cast_ofNat, Nat.reduceSub, mul_one]
    all_goals ring
  have hD_int : IntervalIntegrable D volume (n : ℝ) (n + 1 : ℕ) := by
    have hD_cont : Continuous D := by
      dsimp only [D, localCenteredBernoulliOne]
      exact ((continuous_bernoulliFun 1).comp
        (continuous_id.sub continuous_const)).neg
    exact hD_cont.intervalIntegrable _ _
  have hK'_int : IntervalIntegrable K' volume (n : ℝ) (n + 1 : ℕ) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hnn
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hnpos.trans_le hx.1)
    exact (continuousAt_const.mul
      (continuousAt_ofReal_cpow_const _ _ (Or.inr hx0))).continuousWithinAt
  have hK_int : IntervalIntegrable K volume (n : ℝ) (n + 1 : ℕ) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hnn
    intro x hx
    exact (hK_deriv x hx).continuousAt.continuousWithinAt
  have hparts := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (a := (n : ℝ)) (b := (n + 1 : ℕ))
    (u := H) (u' := D) (v := K) (v' := K')
    (fun x hx => hD_deriv x (by simpa [Set.uIcc_of_le hnn] using hx))
    (fun x hx => hK_deriv x (by simpa [Set.uIcc_of_le hnn] using hx))
    hD_int hK'_int
  have hcenter :
      (∫ x in (n : ℝ)..(n + 1 : ℕ),
        ((centeredFloorError x : ℝ) : ℂ) * K x) =
      ∫ x in (n : ℝ)..(n + 1 : ℕ), D x • K x := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [Set.uIoc_of_le hnn]
    filter_upwards [centeredFloorError_ae_eq_localCenteredBernoulliOne n] with x hx
    rw [hx]
    simp [D]
  have hperiodic :
      (∫ x in (n : ℝ)..(n + 1 : ℕ), H x • K' x) =
        (-1 / 2 : ℂ) *
          ∫ x in (n : ℝ)..(n + 1 : ℕ),
            ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) * K' x := by
    calc
      (∫ x in (n : ℝ)..(n + 1 : ℕ), H x • K' x) =
          ∫ x in (n : ℝ)..(n + 1 : ℕ),
            (-1 / 2 : ℂ) *
              (((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) * K' x) := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [Set.uIoc_of_le hnn]
        filter_upwards [periodizedBernoulli_two_ae_eq_local n] with x hx
        rw [hx]
        dsimp only [H]
        simp only [Complex.real_smul]
        norm_num
        ring
      _ = (-1 / 2 : ℂ) *
          ∫ x in (n : ℝ)..(n + 1 : ℕ),
            ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) * K' x :=
        intervalIntegral.integral_const_mul _ _
  have hparts' :
      (∫ x in (n : ℝ)..(n + 1 : ℕ), D x • K x) =
        H (n + 1 : ℕ) • K (n + 1 : ℕ) - H n • K n -
          ∫ x in (n : ℝ)..(n + 1 : ℕ), H x • K' x := by
    rw [eq_sub_iff_add_eq]
    simpa only [add_comm] using (eq_sub_iff_add_eq.mp hparts)
  have hscale :
      (∫ x in (n : ℝ)..(n + 1 : ℕ),
        ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) * K' x) =
        (-(s + 1)) *
          ∫ x in (n : ℝ)..(n + 1 : ℕ),
            ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
              (x : ℂ) ^ (-(s + 2)) := by
    calc
      (∫ x in (n : ℝ)..(n + 1 : ℕ),
        ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) * K' x) =
          ∫ x in (n : ℝ)..(n + 1 : ℕ),
            (-(s + 1)) *
              (((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
                (x : ℂ) ^ (-(s + 2))) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        dsimp only [K']
        ring
      _ = (-(s + 1)) *
          ∫ x in (n : ℝ)..(n + 1 : ℕ),
            ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
              (x : ℂ) ^ (-(s + 2)) :=
        intervalIntegral.integral_const_mul _ _
  rw [hcenter, hparts', hperiodic]
  have hHn : H n = -1 / 12 := by norm_num [H, bernoulliFun_two]
  have hHsucc : H (n + 1 : ℕ) = -1 / 12 := by
    norm_num [H, bernoulliFun_two]
  rw [hHn, hHsucc]
  rw [hscale]
  dsimp only [K, K']
  push_cast
  simp only [Complex.real_smul]
  norm_num
  ring

/-- On a finite positive integer interval, one integration by parts replaces
the centered floor error by the continuous periodic second Bernoulli
function.  This is the exact bridge that makes the Fourier-mode
nonstationary-phase estimate applicable to Abel's zeta remainder. -/
theorem intervalIntegral_centeredFloorError_cpow_eq_bernoulliTwo
    {s : ℂ} (hs : 0 < s.re) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∫ x in (N : ℝ)..(M : ℝ),
      (((((⌊x⌋₊ : ℝ) - x) + 1 / 2 : ℝ) : ℂ) *
        (x : ℂ) ^ (-(s + 1)))) =
      ((N : ℂ) ^ (-(s + 1)) - (M : ℂ) ^ (-(s + 1))) / 12 -
        (s + 1) / 2 *
          ∫ x in (N : ℝ)..(M : ℝ),
            ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
              (x : ℂ) ^ (-(s + 2)) := by
  let f : ℝ → ℂ := fun x =>
    ((centeredFloorError x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))
  let g : ℝ → ℂ := fun x =>
    ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
      (x : ℂ) ^ (-(s + 2))
  have hf_int (n : ℕ) (hn : 1 ≤ n) :
      IntervalIntegrable f volume (n : ℝ) (n + 1 : ℕ) := by
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hnn : (n : ℝ) ≤ (n + 1 : ℕ) := by norm_num
    have hlocal : IntervalIntegrable
        (fun x : ℝ => ((localCenteredBernoulliOne n x : ℝ) : ℂ) *
          (x : ℂ) ^ (-(s + 1))) volume (n : ℝ) (n + 1 : ℕ) := by
      apply ContinuousOn.intervalIntegrable_of_Icc hnn
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt (hnpos.trans_le hx.1)
      have hlocal_cont : ContinuousAt
          (fun y : ℝ => ((localCenteredBernoulliOne n y : ℝ) : ℂ)) x := by
        dsimp only [localCenteredBernoulliOne]
        fun_prop
      exact (hlocal_cont.mul
        (continuousAt_ofReal_cpow_const _ _ (Or.inr hx0))).continuousWithinAt
    apply hlocal.congr_ae
    rw [Set.uIoc_of_le hnn]
    filter_upwards [centeredFloorError_ae_eq_localCenteredBernoulliOne n] with x hx
    rw [← hx]
  have hg_int (n : ℕ) (hn : 1 ≤ n) :
      IntervalIntegrable g volume (n : ℝ) (n + 1 : ℕ) := by
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hnn : (n : ℝ) ≤ (n + 1 : ℕ) := by norm_num
    apply ContinuousOn.intervalIntegrable_of_Icc hnn
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hnpos.trans_le hx.1)
    have hB_cont : ContinuousAt
        (fun y : ℝ =>
          ((periodizedBernoulli 2 (y : AddCircle (1 : ℝ)) : ℝ) : ℂ)) x :=
      (continuous_ofReal.comp
        ((periodizedBernoulli.continuous (by norm_num : 2 ≠ 1)).comp
          continuous_quotient_mk')).continuousAt
    exact (hB_cont.mul
      (continuousAt_ofReal_cpow_const _ _ (Or.inr hx0))).continuousWithinAt
  have hsum_f :
      ∑ n ∈ Finset.Ico N M, ∫ x in (n : ℝ)..(n + 1 : ℕ), f x =
        ∫ x in (N : ℝ)..(M : ℝ), f x := by
    exact intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun n : ℕ => (n : ℝ)) hNM (fun n hn =>
        hf_int n (hN.trans hn.1))
  have hsum_g :
      ∑ n ∈ Finset.Ico N M, ∫ x in (n : ℝ)..(n + 1 : ℕ), g x =
        ∫ x in (N : ℝ)..(M : ℝ), g x := by
    exact intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun n : ℕ => (n : ℝ)) hNM (fun n hn =>
        hg_int n (hN.trans hn.1))
  have hunit (n : ℕ) (hn : n ∈ Finset.Ico N M) :
      (∫ x in (n : ℝ)..(n + 1 : ℕ), f x) =
        ((n : ℂ) ^ (-(s + 1)) - (n + 1 : ℕ) ^ (-(s + 1))) / 12 -
          (s + 1) / 2 * ∫ x in (n : ℝ)..(n + 1 : ℕ), g x := by
    simpa only [f, g] using
      intervalIntegral_centeredFloorError_cpow_eq_bernoulliTwo_unit hs
        (hN.trans (Finset.mem_Ico.mp hn).1)
  have htel :
      ∑ n ∈ Finset.Ico N M,
          ((n : ℂ) ^ (-(s + 1)) - (n + 1 : ℕ) ^ (-(s + 1))) / 12 =
        ((N : ℂ) ^ (-(s + 1)) - (M : ℂ) ^ (-(s + 1))) / 12 := by
    clear hsum_f hsum_g hunit
    induction M, hNM using Nat.le_induction with
    | base => simp
    | succ M hNM ih =>
        rw [Finset.sum_Ico_succ_top hNM, ih]
        push_cast
        ring
  change (∫ x in (N : ℝ)..(M : ℝ), f x) =
    ((N : ℂ) ^ (-(s + 1)) - (M : ℂ) ^ (-(s + 1))) / 12 -
      (s + 1) / 2 * ∫ x in (N : ℝ)..(M : ℝ), g x
  calc
    (∫ x in (N : ℝ)..(M : ℝ), f x) =
        ∑ n ∈ Finset.Ico N M, ∫ x in (n : ℝ)..(n + 1 : ℕ), f x := hsum_f.symm
    _ = ∑ n ∈ Finset.Ico N M,
        (((n : ℂ) ^ (-(s + 1)) - (n + 1 : ℕ) ^ (-(s + 1))) / 12 -
          (s + 1) / 2 * ∫ x in (n : ℝ)..(n + 1 : ℕ), g x) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hunit n hn
    _ = (∑ n ∈ Finset.Ico N M,
          ((n : ℂ) ^ (-(s + 1)) - (n + 1 : ℕ) ^ (-(s + 1))) / 12) -
        (s + 1) / 2 *
          ∑ n ∈ Finset.Ico N M, ∫ x in (n : ℝ)..(n + 1 : ℕ), g x := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.mul_sum]
    _ = ((N : ℂ) ^ (-(s + 1)) - (M : ℂ) ^ (-(s + 1))) / 12 -
        (s + 1) / 2 * ∫ x in (N : ℝ)..(M : ℝ), g x := by
      rw [htel, hsum_g]

private noncomputable def bernoulliTwoFourierCoeff (k : ℤ) : ℂ :=
  -(Nat.factorial 2 : ℂ) / (2 * Real.pi * I * k) ^ (2 : ℕ)

private lemma summable_bernoulliTwoFourierCoeff :
    Summable bernoulliTwoFourierCoeff := by
  simpa only [bernoulliTwoFourierCoeff, Nat.cast_ofNat] using
    (summable_bernoulli_fourier (by norm_num : 2 ≤ 2))

private lemma hasSum_bernoulliTwoFourier (x : ℝ) :
    HasSum
      (fun k : ℤ => bernoulliTwoFourierCoeff k *
        fourier k (x : AddCircle (1 : ℝ)))
      ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) := by
  let B : C(AddCircle (1 : ℝ), ℂ) :=
    ContinuousMap.mk ((↑) ∘ periodizedBernoulli 2)
      (continuous_ofReal.comp (periodizedBernoulli.continuous (by norm_num)))
  have hcoeff : ∀ k : ℤ, fourierCoeff B k = bernoulliTwoFourierCoeff k := by
    intro k
    change fourierCoeff ((↑) ∘ periodizedBernoulli 2) k =
      bernoulliTwoFourierCoeff k
    rw [fourierCoeff_bernoulli_eq (by norm_num : 2 ≠ 0)]
    simp only [bernoulliTwoFourierCoeff]
  have hsum := has_pointwise_sum_fourier_series_of_summable
    ((summable_bernoulliTwoFourierCoeff.congr fun k => (hcoeff k).symm))
    (x : AddCircle (1 : ℝ))
  simp_rw [hcoeff, smul_eq_mul] at hsum
  simpa only [B, ContinuousMap.coe_mk, Function.comp_apply] using hsum

private noncomputable def bernoulliTwoModeWeight (k : ℤ) : ℝ :=
  if k = 0 then 0 else ‖bernoulliTwoFourierCoeff k‖ / |(k : ℝ)|

private lemma summable_bernoulliTwoModeWeight :
    Summable bernoulliTwoModeWeight := by
  have hc : Summable (fun k : ℤ => ‖bernoulliTwoFourierCoeff k‖) :=
    summable_bernoulliTwoFourierCoeff.norm
  refine hc.of_nonneg_of_le (fun k => by
    by_cases hk : k = 0
    · simp [bernoulliTwoModeWeight, hk]
    · rw [bernoulliTwoModeWeight, if_neg hk]
      positivity) ?_
  intro k
  by_cases hk : k = 0
  · simp [bernoulliTwoModeWeight, hk]
  · rw [bernoulliTwoModeWeight, if_neg hk]
    have hkabs : 1 ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    exact div_le_self (norm_nonneg _) hkabs

/-- The absolutely convergent Fourier expansion of the periodic second
Bernoulli function, combined with nonstationary phase, gives a uniform
Mellin-oscillatory integral bound. -/
theorem exists_norm_intervalIntegral_periodizedBernoulli_two_mellin_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b t p : ℝ},
      a ≤ b → 0 < a → 0 < p → |t| ≤ a →
        ‖∫ x in a..b,
          ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
            (x ^ (-p) • Complex.exp (I * (-t * Real.log x)))‖ ≤
          C * a ^ (-p) := by
  let S : ℝ := ∑' k : ℤ, bernoulliTwoModeWeight k
  let C : ℝ := (4 / (2 * Real.pi - 1)) * S
  have hfactor : 0 ≤ 4 / (2 * Real.pi - 1) := by
    apply div_nonneg (by norm_num)
    nlinarith [Real.pi_gt_three]
  refine ⟨C, mul_nonneg hfactor (tsum_nonneg fun k => by
    by_cases hk : k = 0
    · simp [bernoulliTwoModeWeight, hk]
    · rw [bernoulliTwoModeWeight, if_neg hk]
      positivity), ?_⟩
  intro a b t p hab ha hp ht
  let W : ℝ → ℂ := fun x =>
    x ^ (-p) • Complex.exp (I * (-t * Real.log x))
  let F : ℤ → ℝ → ℂ := fun k x =>
    bernoulliTwoFourierCoeff k * fourier k (x : AddCircle (1 : ℝ)) * W x
  have hF_meas : ∀ k : ℤ,
      AEStronglyMeasurable (F k) (volume.restrict (Set.uIoc a b)) := by
    intro k
    rw [Set.uIoc_of_le hab]
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    intro x hx
    have hxpos : 0 < x := ha.trans hx.1
    have hfour : ContinuousAt
        (fun y : ℝ => fourier k (y : AddCircle (1 : ℝ))) x :=
      ((fourier k).continuous.comp continuous_quotient_mk').continuousAt
    have hW : ContinuousAt W x := by
      have hrpow : ContinuousAt (fun y : ℝ => y ^ (-p)) x :=
        Real.continuousAt_rpow_const x (-p) (Or.inl hxpos.ne')
      have hcastRpow : ContinuousAt (fun y : ℝ => ((y ^ (-p) : ℝ) : ℂ)) x :=
        continuous_ofReal.continuousAt.comp hrpow
      have hcastLog : ContinuousAt (fun y : ℝ => ((Real.log y : ℝ) : ℂ)) x :=
        continuous_ofReal.continuousAt.comp (Real.continuousAt_log hxpos.ne')
      have hexp : ContinuousAt
          (fun y : ℝ => Complex.exp (I * (-t * Real.log y))) x := by
        exact (continuousAt_const.mul (continuousAt_const.mul hcastLog)).cexp
      simpa only [W, Complex.real_smul] using hcastRpow.mul hexp
    exact ((continuousAt_const.mul hfour).mul hW).continuousWithinAt
  have hbound : ∀ k : ℤ, ∀ᵐ x ∂volume, x ∈ Set.uIoc a b →
      ‖F k x‖ ≤ ‖bernoulliTwoFourierCoeff k‖ * a ^ (-p) := by
    intro k
    filter_upwards with x hx
    rw [Set.uIoc_of_le hab] at hx
    have hxpos : 0 < x := ha.trans hx.1
    have hpow : x ^ (-p) ≤ a ^ (-p) :=
      Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (neg_nonpos.mpr hp.le)
        ha hxpos hx.1.le
    have hnormW : ‖W x‖ = x ^ (-p) := by
      dsimp only [W]
      rw [Complex.real_smul, norm_mul, norm_real, Complex.norm_exp]
      have hre : (I * (-(t : ℂ) * (Real.log x : ℂ))).re = 0 := by simp
      rw [hre, Real.exp_zero, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]
    dsimp only [F, W]
    rw [norm_mul, norm_mul, fourier_apply, Circle.norm_coe, hnormW]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
  have hbound_sum : ∀ᵐ x ∂volume, x ∈ Set.uIoc a b →
      Summable (fun k : ℤ => ‖bernoulliTwoFourierCoeff k‖ * a ^ (-p)) := by
    filter_upwards with x _hx
    exact summable_bernoulliTwoFourierCoeff.norm.mul_right _
  have hbound_int : IntervalIntegrable
      (fun _x : ℝ => ∑' k : ℤ,
        ‖bernoulliTwoFourierCoeff k‖ * a ^ (-p)) volume a b := by
    exact continuous_const.intervalIntegrable _ _
  have hpoint : ∀ᵐ x ∂volume, x ∈ Set.uIoc a b →
      HasSum (fun k : ℤ => F k x)
        (((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) * W x) := by
    filter_upwards with x _hx
    simpa only [F, mul_assoc] using (hasSum_bernoulliTwoFourier x).mul_right (W x)
  have hseries : HasSum
      (fun k : ℤ => ∫ x in a..b, F k x)
      (∫ x in a..b,
        ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) * W x) :=
    intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k _x => ‖bernoulliTwoFourierCoeff k‖ * a ^ (-p))
      hF_meas hbound hbound_sum hbound_int hpoint
  have hmode : ∀ k : ℤ,
      ‖∫ x in a..b, F k x‖ ≤
        (4 / (2 * Real.pi - 1)) * a ^ (-p) * bernoulliTwoModeWeight k := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp [F, bernoulliTwoFourierCoeff, bernoulliTwoModeWeight]
    · have hrewrite :
          (∫ x in a..b, F k x) = bernoulliTwoFourierCoeff k *
            ∫ x in a..b, x ^ (-p) •
              Complex.exp (I * OscillatoryIntegral.fourierMellinPhase k t x) := by
        calc
          (∫ x in a..b, F k x) =
              ∫ x in a..b, bernoulliTwoFourierCoeff k *
                (x ^ (-p) • Complex.exp
                  (I * OscillatoryIntegral.fourierMellinPhase k t x)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            have hxIcc : x ∈ Set.Icc a b := by
              simpa [Set.uIcc_of_le hab] using hx
            have hxpos : 0 < x := ha.trans_le hxIcc.1
            dsimp only [F, W]
            rw [fourier_coe_apply]
            norm_num
            have hphase :
                Complex.exp (2 * (Real.pi : ℂ) * I * (k : ℂ) * (x : ℂ)) *
                    Complex.exp (-(I * ((t : ℂ) * (Real.log x : ℂ)))) =
                  Complex.exp
                    (I * (OscillatoryIntegral.fourierMellinPhase k t x : ℂ)) := by
              rw [← Complex.exp_add]
              congr 1
              simp only [OscillatoryIntegral.fourierMellinPhase]
              push_cast
              ring
            calc
              bernoulliTwoFourierCoeff k *
                    Complex.exp (2 * (Real.pi : ℂ) * I * (k : ℂ) * (x : ℂ)) *
                    (((x ^ (-p) : ℝ) : ℂ) *
                      Complex.exp (-(I * ((t : ℂ) * (Real.log x : ℂ))))) =
                  bernoulliTwoFourierCoeff k * ((x ^ (-p) : ℝ) : ℂ) *
                    (Complex.exp (2 * (Real.pi : ℂ) * I * (k : ℂ) * (x : ℂ)) *
                      Complex.exp (-(I * ((t : ℂ) * (Real.log x : ℂ))))) := by ring
              _ = bernoulliTwoFourierCoeff k * ((x ^ (-p) : ℝ) : ℂ) *
                    Complex.exp
                      (I * (OscillatoryIntegral.fourierMellinPhase k t x : ℂ)) := by
                    rw [hphase]
              _ = bernoulliTwoFourierCoeff k *
                    (((x ^ (-p) : ℝ) : ℂ) *
                      Complex.exp
                        (I * (OscillatoryIntegral.fourierMellinPhase k t x : ℂ))) := by ring
          _ = bernoulliTwoFourierCoeff k *
              ∫ x in a..b, x ^ (-p) •
                Complex.exp (I * OscillatoryIntegral.fourierMellinPhase k t x) :=
            intervalIntegral.integral_const_mul _ _
      rw [hrewrite, norm_mul, bernoulliTwoModeWeight, if_neg hk]
      calc
        ‖bernoulliTwoFourierCoeff k‖ *
            ‖∫ x in a..b, x ^ (-p) •
              Complex.exp (I * OscillatoryIntegral.fourierMellinPhase k t x)‖ ≤
            ‖bernoulliTwoFourierCoeff k‖ *
              (4 * a ^ (-p) / ((2 * Real.pi - 1) * |(k : ℝ)|)) :=
          mul_le_mul_of_nonneg_left
            (OscillatoryIntegral.norm_integral_rpow_smul_cexp_fourierMellinPhase_le
              hab ha hp ht k hk)
            (norm_nonneg _)
        _ = (4 / (2 * Real.pi - 1)) * a ^ (-p) *
            (‖bernoulliTwoFourierCoeff k‖ / |(k : ℝ)|) := by
          have hfactor : 2 * Real.pi - 1 ≠ 0 := by
            nlinarith [Real.pi_gt_three]
          have hkabs : |(k : ℝ)| ≠ 0 := abs_ne_zero.mpr (Int.cast_ne_zero.mpr hk)
          field_simp
  have hmajorant : HasSum
      (fun k : ℤ => (4 / (2 * Real.pi - 1)) * a ^ (-p) *
        bernoulliTwoModeWeight k)
      ((4 / (2 * Real.pi - 1)) * a ^ (-p) * S) := by
    exact (summable_bernoulliTwoModeWeight.hasSum.mul_left
      ((4 / (2 * Real.pi - 1)) * a ^ (-p)))
  have hnorm := hseries.norm_le_of_bounded hmajorant hmode
  change ‖∫ x in a..b,
    ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) * W x‖ ≤
      C * a ^ (-p)
  exact hnorm.trans_eq (by dsimp only [C]; ring)

private lemma ofReal_cpow_neg_sigma_add_it
    {x sigma t : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (-(((sigma : ℂ) + I * t) + 2)) =
      x ^ (-(sigma + 2)) • Complex.exp (I * (-t * Real.log x)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [Complex.real_smul, Real.rpow_def_of_pos hx, Complex.ofReal_exp]
  rw [← Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_log hx.le]
  push_cast
  ring

/-- Complex-power form of the periodic-Bernoulli Mellin bound.  This is the
form consumed directly by the twice-integrated Abel remainder. -/
theorem exists_norm_intervalIntegral_periodizedBernoulli_two_cpow_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b sigma t : ℝ},
      a ≤ b → 0 < a → 0 < sigma + 2 → |t| ≤ a →
        ‖∫ x in a..b,
          ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
            (x : ℂ) ^ (-(((sigma : ℂ) + I * t) + 2))‖ ≤
          C * a ^ (-(sigma + 2)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_intervalIntegral_periodizedBernoulli_two_mellin_le
  refine ⟨C, hC, ?_⟩
  intro a b sigma t hab ha hsigma ht
  have heq :
      (∫ x in a..b,
        ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
          (x : ℂ) ^ (-(((sigma : ℂ) + I * t) + 2))) =
        ∫ x in a..b,
          ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
            (x ^ (-(sigma + 2)) •
              Complex.exp (I * (-t * Real.log x))) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxIcc : x ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hx
    change
      ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
          (x : ℂ) ^ (-(((sigma : ℂ) + I * t) + 2)) =
        ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
          (x ^ (-(sigma + 2)) • Complex.exp (I * (-t * Real.log x)))
    rw [ofReal_cpow_neg_sigma_add_it (ha.trans_le hxIcc.1)]
  rw [heq]
  exact hbound hab ha hsigma ht

private lemma inv_nat_cpow_criticalLine_eq_exp
    {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t) =
      ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
        Complex.exp ((-I * (Real.log n : ℂ)) * t) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [Complex.cpow_add _ _ hnC, one_div, mul_inv_rev]
  calc
    ((n : ℂ) ^ (I * t))⁻¹ * ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ =
        ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ * ((n : ℂ) ^ (I * t))⁻¹ :=
      mul_comm _ _
    _ = ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
        Complex.exp ((-I * (Real.log n : ℂ)) * t) := by
      congr 1
      rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.exp_neg,
        ← Complex.natCast_log]
      congr 1
      ring

/-- A nonconstant term of the critical-line Dirichlet polynomial has an
interval integral bounded by its inverse logarithmic frequency. -/
theorem norm_integral_inv_nat_cpow_criticalLine_le
    {n : ℕ} (hn : 2 ≤ n) {a b : ℝ} :
    ‖∫ t in a..b, 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)‖ ≤
      2 / (Real.sqrt n * Real.log n) := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  let c : ℂ := -I * (Real.log n : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero)
      (ofReal_ne_zero.mpr hlog.ne')
  have hnorm_c : ‖c‖ = Real.log n := by
    dsimp [c]
    rw [norm_mul, norm_neg, norm_I, one_mul, norm_real,
      Real.norm_eq_abs, abs_of_pos hlog]
  have hexp_norm (t : ℝ) : ‖Complex.exp (c * t)‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (c * (t : ℂ)).re = 0 := by
      dsimp [c]
      ring
    rw [hre, Real.exp_zero]
  have hosc : ‖∫ t in a..b, Complex.exp (c * t)‖ ≤ 2 / Real.log n := by
    rw [integral_exp_mul_complex hc]
    rw [norm_div, hnorm_c]
    apply (div_le_div_iff_of_pos_right hlog).2
    calc
      ‖Complex.exp (c * b) - Complex.exp (c * a)‖
          ≤ ‖Complex.exp (c * b)‖ + ‖Complex.exp (c * a)‖ := norm_sub_le _ _
      _ = 2 := by rw [hexp_norm, hexp_norm]; norm_num
  rw [show (fun t : ℝ => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) =
      (fun t : ℝ => ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ * Complex.exp (c * t)) by
    funext t
    simpa [c] using inv_nat_cpow_criticalLine_eq_exp hn0 t]
  have hfactor :
      (∫ t in a..b,
        ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ * Complex.exp (c * t)) =
        ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
          ∫ t in a..b, Complex.exp (c * t) :=
    intervalIntegral.integral_const_mul _ _
  rw [hfactor, norm_mul]
  have hhalf : ‖(n : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt n := by
    rw [Complex.norm_natCast_cpow_of_pos hnpos]
    simp [Real.sqrt_eq_rpow]
  rw [norm_inv, hhalf]
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hnpos)
  rw [inv_eq_one_div]
  calc
    (1 / Real.sqrt n) * ‖∫ t in a..b, Complex.exp (c * t)‖
        ≤ (1 / Real.sqrt n) * (2 / Real.log n) :=
      mul_le_mul_of_nonneg_left hosc (by positivity)
    _ = 2 / (Real.sqrt n * Real.log n) := by field_simp

private lemma sum_inv_sqrt_Icc_two_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, (Real.sqrt n)⁻¹ ≤
      Real.sqrt N * Real.sqrt (harmonic N : ℝ) := by
  let S := Finset.Icc 2 N
  have hcs := Real.sum_sqrt_mul_sqrt_le S
    (f := fun _ : ℕ => (1 : ℝ))
    (g := fun n : ℕ => ((n : ℝ))⁻¹)
    (fun _ => zero_le_one) (fun _ => by positivity)
  have hleft :
      (∑ n ∈ S, Real.sqrt (1 : ℝ) * Real.sqrt ((n : ℝ)⁻¹)) =
        ∑ n ∈ S, (Real.sqrt n)⁻¹ := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Real.sqrt_one, one_mul, Real.sqrt_inv]
  have hsubset : S ⊆ Finset.Icc 1 N := by
    exact Finset.Icc_subset_Icc (by omega) le_rfl
  have hcard : (S.card : ℝ) ≤ N := by
    exact_mod_cast (Finset.card_le_card hsubset).trans (by simp)
  have hrecip :
      (∑ n ∈ S, ((n : ℝ))⁻¹) ≤ (harmonic N : ℝ) := by
    calc
      (∑ n ∈ S, ((n : ℝ))⁻¹) ≤
          ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
          intro n hn hnot
          positivity)
      _ = (harmonic N : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
          Rat.cast_natCast]
  rw [hleft] at hcs
  calc
    ∑ n ∈ Finset.Icc 2 N, (Real.sqrt n)⁻¹ =
        ∑ n ∈ S, (Real.sqrt n)⁻¹ := rfl
    _ ≤ Real.sqrt (∑ _n ∈ S, (1 : ℝ)) *
        Real.sqrt (∑ n ∈ S, ((n : ℝ))⁻¹) := hcs
    _ ≤ Real.sqrt N * Real.sqrt (harmonic N : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact mul_le_mul (Real.sqrt_le_sqrt hcard) (Real.sqrt_le_sqrt hrecip)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The nonconstant part of a finite critical-line Dirichlet polynomial has
sublinear-size interval integral.  The bound is uniform in the endpoints. -/
theorem norm_integral_criticalLineDirichletTail_le
    {N : ℕ} {a b : ℝ} :
    ‖∫ t in a..b, ∑ n ∈ Finset.Icc 2 N,
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)‖ ≤
      (2 / Real.log 2) *
        (Real.sqrt N * Real.sqrt (harmonic N : ℝ)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsumint :
      (∫ t in a..b, ∑ n ∈ Finset.Icc 2 N,
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) =
      ∑ n ∈ Finset.Icc 2 N,
        ∫ t in a..b, 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t) := by
    rw [intervalIntegral.integral_finset_sum]
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : n ≠ 0 := by omega
    rw [show (fun t : ℝ => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) =
        (fun t : ℝ => ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
          Complex.exp ((-I * (Real.log n : ℂ)) * t)) by
      funext t
      exact inv_nat_cpow_criticalLine_eq_exp hn0 t]
    exact (by fun_prop : Continuous (fun t : ℝ =>
      ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
        Complex.exp ((-I * (Real.log n : ℂ)) * t))).intervalIntegrable
          (μ := MeasureTheory.volume) _ _
  rw [hsumint]
  calc
    ‖∑ n ∈ Finset.Icc 2 N,
        ∫ t in a..b, 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)‖ ≤
        ∑ n ∈ Finset.Icc 2 N,
          ‖∫ t in a..b, 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 2 N,
        (2 / Real.log 2) * (Real.sqrt n)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
      have hlogmono : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
      refine (norm_integral_inv_nat_cpow_criticalLine_le hn2).trans ?_
      have hfreq : 2 / Real.log n ≤ 2 / Real.log 2 := by
        exact div_le_div_of_nonneg_left (by norm_num) hlog2 hlogmono
      rw [show 2 / (Real.sqrt n * Real.log n) =
          (2 / Real.log n) * (Real.sqrt n)⁻¹ by field_simp]
      exact mul_le_mul_of_nonneg_right hfreq (by positivity)
    _ = (2 / Real.log 2) *
        (∑ n ∈ Finset.Icc 2 N, (Real.sqrt n)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ (2 / Real.log 2) *
        (Real.sqrt N * Real.sqrt (harmonic N : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_inv_sqrt_Icc_two_le N) (by positivity)

/-- The natural Dirichlet-polynomial cutoff for the first Hardy approximation
on the dyadic interval `[T, 2T]`. -/
noncomputable def firstZetaApproximationCutoff (T : ℝ) : ℕ :=
  ⌊4 * T⌋₊

/-- At the Hardy cutoff, the integrated nonconstant Dirichlet polynomial is
controlled by a square-root times logarithmic square-root majorant. -/
theorem norm_integral_criticalLineDirichletTail_cutoff_le
    {T : ℝ} (hT : 1 ≤ T) :
    ‖∫ t in T..2 * T, ∑ n ∈ Finset.Icc 2 (firstZetaApproximationCutoff T),
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)‖ ≤
      (2 / Real.log 2) *
        (Real.sqrt (4 * T) * Real.sqrt (1 + Real.log (4 * T))) := by
  have h4T : 1 ≤ 4 * T := by linarith
  have hfloor : (firstZetaApproximationCutoff T : ℝ) ≤ 4 * T := by
    exact Nat.floor_le (by positivity)
  have hharmonic :
      (harmonic (firstZetaApproximationCutoff T) : ℝ) ≤
        1 + Real.log (4 * T) := by
    exact harmonic_floor_le_one_add_log (4 * T) h4T
  refine norm_integral_criticalLineDirichletTail_le.trans ?_
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (Real.sqrt_le_sqrt hfloor) (Real.sqrt_le_sqrt hharmonic)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity)

/-- The integrated nonconstant Dirichlet polynomial at the Hardy cutoff is
`o(T)` on dyadic intervals.  This is the cancellation input needed in the
lower-bound half of Hardy's contradiction argument. -/
theorem norm_integral_criticalLineDirichletTail_cutoff_isLittleO :
    (fun T : ℝ =>
      ‖∫ t in T..2 * T,
        ∑ n ∈ Finset.Icc 2 (firstZetaApproximationCutoff T),
          1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)‖) =o[atTop]
      (fun T : ℝ => T) := by
  have hlog : Real.log =o[atTop] (fun T : ℝ => T) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_atTop (r := (1 : ℝ)) one_pos)
  have hlogFour :
      (fun T : ℝ => Real.log (4 * T)) =o[atTop] (fun T : ℝ => T) := by
    have hadd := (isLittleO_const_id_atTop (Real.log 4)).add hlog
    refine hadd.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hT.ne']
  have honeAddLog :
      (fun T : ℝ => 1 + Real.log (4 * T)) =o[atTop]
        (fun T : ℝ => T) :=
    (isLittleO_const_id_atTop (1 : ℝ)).add hlogFour
  have hsqrtLog :
      (fun T : ℝ => Real.sqrt (1 + Real.log (4 * T))) =o[atTop]
        (fun T : ℝ => Real.sqrt T) :=
    honeAddLog.sqrt (eventually_ge_atTop (0 : ℝ))
  have hsqrtFour :
      (fun T : ℝ => Real.sqrt (4 * T)) =O[atTop]
        (fun T : ℝ => Real.sqrt T) := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_mul (by norm_num)]
    norm_num
  have hproduct :
      (fun T : ℝ => Real.sqrt (4 * T) *
        Real.sqrt (1 + Real.log (4 * T))) =o[atTop]
        (fun T : ℝ => T) := by
    refine (hsqrtFour.mul_isLittleO hsqrtLog).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact Real.mul_self_sqrt hT
  have hmajorant :
      (fun T : ℝ => (2 / Real.log 2) *
        (Real.sqrt (4 * T) * Real.sqrt (1 + Real.log (4 * T)))) =o[atTop]
        (fun T : ℝ => T) :=
    hproduct.const_mul_left (2 / Real.log 2)
  refine (IsBigO.of_bound' ?_).trans_isLittleO hmajorant
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (by positivity :
    0 ≤ (2 / Real.log 2) *
      (Real.sqrt (4 * T) * Real.sqrt (1 + Real.log (4 * T))))]
  exact norm_integral_criticalLineDirichletTail_cutoff_le hT

end HardyTheorem
