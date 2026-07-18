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

private lemma norm_periodizedBernoulli_two_le_tsum_norm_coeff (x : ℝ) :
    ‖((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ)‖ ≤
      ∑' k : ℤ, ‖bernoulliTwoFourierCoeff k‖ := by
  apply (hasSum_bernoulliTwoFourier x).norm_le_of_bounded
    summable_bernoulliTwoFourierCoeff.norm.hasSum
  intro k
  rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]

private lemma integrableOn_Ioi_periodizedBernoulli_two_cpow
    {a sigma t : ℝ} (ha : 0 < a) (hsigma : 1 < sigma + 2) :
    IntegrableOn
      (fun x : ℝ =>
        ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
          (x : ℂ) ^ (-(((sigma : ℂ) + I * t) + 2)))
      (Set.Ioi a) := by
  let A : ℝ := ∑' k : ℤ, ‖bernoulliTwoFourierCoeff k‖
  let P : ℝ → ℂ := fun x =>
    (x : ℂ) ^ (-(((sigma : ℂ) + I * t) + 2))
  let F : ℝ → ℂ := fun x =>
    ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) * P x
  have hP : IntegrableOn P (Set.Ioi a) := by
    change IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (-(((sigma : ℂ) + I * t) + 2)))
      (Set.Ioi a)
    apply integrableOn_Ioi_cpow_of_lt
    · norm_num [neg_re, add_re, mul_re]
      linarith
    · exact ha
  have hA : 0 ≤ A := tsum_nonneg fun k => norm_nonneg _
  have hmajorant : IntegrableOn (fun x => A * ‖P x‖) (Set.Ioi a) :=
    hP.norm.const_mul A
  have hF_meas : AEStronglyMeasurable F (volume.restrict (Set.Ioi a)) := by
    apply AEStronglyMeasurable.mul
    · exact (continuous_ofReal.comp
        ((periodizedBernoulli.continuous (by norm_num : 2 ≠ 1)).comp
          continuous_quotient_mk')).aestronglyMeasurable
    · exact hP.aestronglyMeasurable
  change Integrable F (volume.restrict (Set.Ioi a))
  change Integrable (fun x => A * ‖P x‖) (volume.restrict (Set.Ioi a)) at hmajorant
  apply hmajorant.mono hF_meas
  filter_upwards with x
  dsimp only [F]
  rw [norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hA (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right
    (by simpa only [A] using norm_periodizedBernoulli_two_le_tsum_norm_coeff x)
    (norm_nonneg _)

/-- The periodic-Bernoulli complex-power estimate remains uniform after the
upper endpoint tends to infinity. -/
theorem exists_norm_integral_Ioi_periodizedBernoulli_two_cpow_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a sigma t : ℝ},
      0 < a → 1 < sigma + 2 → |t| ≤ a →
        ‖∫ x in Set.Ioi a,
          ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
            (x : ℂ) ^ (-(((sigma : ℂ) + I * t) + 2))‖ ≤
          C * a ^ (-(sigma + 2)) := by
  obtain ⟨C, hC, hfinite⟩ :=
    exists_norm_intervalIntegral_periodizedBernoulli_two_cpow_le
  refine ⟨C, hC, ?_⟩
  intro a sigma t ha hsigma ht
  let F : ℝ → ℂ := fun x =>
    ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
      (x : ℂ) ^ (-(((sigma : ℂ) + I * t) + 2))
  have hF : IntegrableOn F (Set.Ioi a) :=
    integrableOn_Ioi_periodizedBernoulli_two_cpow ha hsigma
  have hlim : Tendsto (fun b : ℝ => ‖∫ x in a..b, F x‖) atTop
      (nhds ‖∫ x in Set.Ioi a, F x‖) :=
    (intervalIntegral_tendsto_integral_Ioi a hF tendsto_id).norm
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop a] with b hb
  exact hfinite hb ha (by linarith) ht

private lemma integrableOn_Ioi_centeredFloorError_cpow
    {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    IntegrableOn
      (fun x : ℝ =>
        (((((⌊x⌋₊ : ℝ) - x) + 1 / 2 : ℝ) : ℂ) *
          (x : ℂ) ^ (-(s + 1))))
      (Set.Ioi (N : ℝ)) := by
  let P : ℝ → ℂ := fun x => (x : ℂ) ^ (-(s + 1))
  let F : ℝ → ℂ := fun x =>
    (((((⌊x⌋₊ : ℝ) - x) + 1 / 2 : ℝ) : ℂ) * P x)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hP : IntegrableOn P (Set.Ioi (N : ℝ)) := by
    exact integrableOn_Ioi_cpow_of_lt (by simp; linarith) hNpos
  have hmajorant :
      IntegrableOn (fun x => (3 / 2 : ℝ) * ‖P x‖) (Set.Ioi (N : ℝ)) :=
    hP.norm.const_mul (3 / 2)
  have hF_meas :
      AEStronglyMeasurable F (volume.restrict (Set.Ioi (N : ℝ))) := by
    apply AEStronglyMeasurable.mul
    · have hfloor : Measurable fun x : ℝ => (⌊x⌋₊ : ℝ) := by fun_prop
      exact (Complex.measurable_ofReal.comp
        ((hfloor.sub measurable_id).add measurable_const)).aestronglyMeasurable
    · exact hP.aestronglyMeasurable
  change Integrable F (volume.restrict (Set.Ioi (N : ℝ)))
  change Integrable (fun x => (3 / 2 : ℝ) * ‖P x‖)
    (volume.restrict (Set.Ioi (N : ℝ))) at hmajorant
  apply hmajorant.mono hF_meas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := hNpos.le.trans hx.le
  have hfloor := Nat.abs_floor_sub_le hx0
  have hcenter : |((⌊x⌋₊ : ℝ) - x) + 1 / 2| ≤ 3 / 2 := by
    calc
      |((⌊x⌋₊ : ℝ) - x) + 1 / 2| ≤
          |(⌊x⌋₊ : ℝ) - x| + |(1 / 2 : ℝ)| := abs_add_le _ _
      _ ≤ 1 + 1 / 2 := by norm_num; linarith
      _ = 3 / 2 := by norm_num
  dsimp only [F]
  rw [norm_mul, norm_real, Real.norm_eq_abs]
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right hcenter (norm_nonneg _)

/-- The finite Bernoulli integration-by-parts identity remains exact after the
upper integer endpoint tends to infinity. -/
theorem integral_Ioi_centeredFloorError_cpow_eq_bernoulliTwo
    {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in Set.Ioi (N : ℝ),
      (((((⌊x⌋₊ : ℝ) - x) + 1 / 2 : ℝ) : ℂ) *
        (x : ℂ) ^ (-(s + 1)))) =
      (N : ℂ) ^ (-(s + 1)) / 12 -
        (s + 1) / 2 *
          ∫ x in Set.Ioi (N : ℝ),
            ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
              (x : ℂ) ^ (-(s + 2)) := by
  let f : ℝ → ℂ := fun x =>
    (((((⌊x⌋₊ : ℝ) - x) + 1 / 2 : ℝ) : ℂ) *
      (x : ℂ) ^ (-(s + 1)))
  let g : ℝ → ℂ := fun x =>
    ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
      (x : ℂ) ^ (-(s + 2))
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hf : IntegrableOn f (Set.Ioi (N : ℝ)) := by
    simpa only [f] using integrableOn_Ioi_centeredFloorError_cpow hs hN
  have hs_eq : ((s.re : ℂ) + I * s.im) = s := by
    apply Complex.ext <;> simp
  have hg : IntegrableOn g (Set.Ioi (N : ℝ)) := by
    simpa only [g, hs_eq] using
      (integrableOn_Ioi_periodizedBernoulli_two_cpow
        (a := (N : ℝ)) (sigma := s.re) (t := s.im) hNpos (by linarith))
  have hlim_f :
      Tendsto (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ), f x) atTop
        (nhds (∫ x in Set.Ioi (N : ℝ), f x)) :=
    intervalIntegral_tendsto_integral_Ioi (N : ℝ) hf
      tendsto_natCast_atTop_atTop
  have hlim_g :
      Tendsto (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ), g x) atTop
        (nhds (∫ x in Set.Ioi (N : ℝ), g x)) :=
    intervalIntegral_tendsto_integral_Ioi (N : ℝ) hg
      tendsto_natCast_atTop_atTop
  have hlim_boundary :
      Tendsto (fun M : ℕ => (M : ℂ) ^ (-(s + 1))) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hrpow := (tendsto_rpow_neg_atTop (show 0 < s.re + 1 by linarith)).comp
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun M : ℕ => (M : ℝ)) atTop atTop)
    apply hrpow.congr'
    filter_upwards [eventually_ge_atTop 1] with M hM
    have hMpos : 0 < (M : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hM)
    change (M : ℝ) ^ (-(s.re + 1)) =
      ‖((M : ℝ) : ℂ) ^ (-(s + 1))‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hMpos]
    simp only [neg_re, add_re, one_re]
  have hfinite : ∀ᶠ M : ℕ in atTop,
      (∫ x in (N : ℝ)..(M : ℝ), f x) =
        ((N : ℂ) ^ (-(s + 1)) - (M : ℂ) ^ (-(s + 1))) / 12 -
          (s + 1) / 2 * ∫ x in (N : ℝ)..(M : ℝ), g x := by
    filter_upwards [eventually_ge_atTop N] with M hNM
    simpa only [f, g] using
      intervalIntegral_centeredFloorError_cpow_eq_bernoulliTwo hs hN hNM
  have hlim_rhs : Tendsto
      (fun M : ℕ =>
        ((N : ℂ) ^ (-(s + 1)) - (M : ℂ) ^ (-(s + 1))) / 12 -
          (s + 1) / 2 * ∫ x in (N : ℝ)..(M : ℝ), g x)
      atTop
      (nhds ((N : ℂ) ^ (-(s + 1)) / 12 -
        (s + 1) / 2 * ∫ x in Set.Ioi (N : ℝ), g x)) := by
    convert ((tendsto_const_nhds.sub hlim_boundary).div_const 12).sub
      (tendsto_const_nhds.mul hlim_g) using 1
    all_goals ring_nf
  change (∫ x in Set.Ioi (N : ℝ), f x) =
    (N : ℂ) ^ (-(s + 1)) / 12 -
      (s + 1) / 2 * ∫ x in Set.Ioi (N : ℝ), g x
  have hfinite' :
      (fun M : ℕ =>
        ((N : ℂ) ^ (-(s + 1)) - (M : ℂ) ^ (-(s + 1))) / 12 -
          (s + 1) / 2 * ∫ x in (N : ℝ)..(M : ℝ), g x) =ᶠ[atTop]
        (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ), f x) :=
    hfinite.mono fun _M h => h.symm
  exact tendsto_nhds_unique hlim_f (hlim_rhs.congr' hfinite')

/-- Uniform Abel floor-error estimate in the strip used by Hardy's first zeta
approximation.  The oscillation in the floor error removes the apparent
factor `‖s‖` from the elementary absolute-value estimate. -/
theorem exists_norm_mul_integral_Ioi_floorError_cpow_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℂ} {N : ℕ},
      (1 / 4 : ℝ) ≤ s.re → s.re ≤ 2 → 1 ≤ N →
        |s.im| ≤ (N : ℝ) →
          ‖s * ∫ x in Set.Ioi (N : ℝ),
            ((((⌊x⌋₊ : ℝ) - x : ℝ) : ℂ) *
              (x : ℂ) ^ (-(s + 1)))‖ ≤
            C * (N : ℝ) ^ (-s.re) := by
  obtain ⟨B, hB, hBbound⟩ :=
    exists_norm_integral_Ioi_periodizedBernoulli_two_cpow_le
  refine ⟨3 / 4 + 6 * B, by positivity, ?_⟩
  intro s N hs_lower hs_upper hN him
  let E : ℝ → ℂ := fun x =>
    ((((⌊x⌋₊ : ℝ) - x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)))
  let C : ℝ → ℂ := fun x =>
    (((((⌊x⌋₊ : ℝ) - x) + 1 / 2 : ℝ) : ℂ) *
      (x : ℂ) ^ (-(s + 1)))
  let P : ℝ → ℂ := fun x => (x : ℂ) ^ (-(s + 1))
  let G : ℝ → ℂ := fun x =>
    ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
      (x : ℂ) ^ (-(s + 2))
  have hs : 0 < s.re := lt_of_lt_of_le (by norm_num) hs_lower
  have hs0 : s ≠ 0 := ne_zero_of_re_pos hs
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hNge : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hCint : IntegrableOn C (Set.Ioi (N : ℝ)) := by
    simpa only [C] using integrableOn_Ioi_centeredFloorError_cpow hs hN
  have hPintable : IntegrableOn P (Set.Ioi (N : ℝ)) := by
    exact integrableOn_Ioi_cpow_of_lt (by simp; linarith) hNpos
  have hEeq :
      (∫ x in Set.Ioi (N : ℝ), E x) =
        (∫ x in Set.Ioi (N : ℝ), C x) -
          (1 / 2 : ℂ) * ∫ x in Set.Ioi (N : ℝ), P x := by
    calc
      (∫ x in Set.Ioi (N : ℝ), E x) =
          ∫ x in Set.Ioi (N : ℝ), C x - (1 / 2 : ℂ) * P x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x _hx
        dsimp only [E, C, P]
        push_cast
        ring
      _ = (∫ x in Set.Ioi (N : ℝ), C x) -
          ∫ x in Set.Ioi (N : ℝ), (1 / 2 : ℂ) * P x := by
        rw [integral_sub hCint (hPintable.const_mul (1 / 2 : ℂ))]
      _ = (∫ x in Set.Ioi (N : ℝ), C x) -
          (1 / 2 : ℂ) * ∫ x in Set.Ioi (N : ℝ), P x := by
        congr 1
        exact integral_const_mul (μ := volume.restrict (Set.Ioi (N : ℝ)))
          (1 / 2 : ℂ) P
  have hPint :
      (∫ x in Set.Ioi (N : ℝ), P x) = (N : ℂ) ^ (-s) / s := by
    dsimp only [P]
    rw [integral_Ioi_cpow_of_lt (by simp; linarith) hNpos]
    have hexp : -(s + 1) + 1 = -s := by ring
    rw [hexp]
    field_simp [hs0]
    norm_num
  have hCeq :
      (∫ x in Set.Ioi (N : ℝ), C x) =
        (N : ℂ) ^ (-(s + 1)) / 12 -
          (s + 1) / 2 * ∫ x in Set.Ioi (N : ℝ), G x := by
    simpa only [C, G] using
      integral_Ioi_centeredFloorError_cpow_eq_bernoulliTwo hs hN
  have hformula :
      s * ∫ x in Set.Ioi (N : ℝ), E x =
        s * ((N : ℂ) ^ (-(s + 1)) / 12 -
          (s + 1) / 2 * ∫ x in Set.Ioi (N : ℝ), G x) -
            (N : ℂ) ^ (-s) / 2 := by
    rw [hEeq, hCeq, hPint]
    field_simp [hs0]
  have hs_eq : ((s.re : ℂ) + I * s.im) = s := by
    apply Complex.ext <;> simp
  have hBtail :
      ‖∫ x in Set.Ioi (N : ℝ), G x‖ ≤
        B * (N : ℝ) ^ (-(s.re + 2)) := by
    have hb := hBbound (a := (N : ℝ)) (sigma := s.re) (t := s.im)
      hNpos (by linarith) (him.trans (by linarith [hNpos]))
    rw [hs_eq] at hb
    simpa only [G] using hb
  have hs_norm : ‖s‖ ≤ 3 * (N : ℝ) := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = s.re + |s.im| := by rw [abs_of_nonneg hs.le]
      _ ≤ 2 + (N : ℝ) := add_le_add hs_upper him
      _ ≤ 3 * (N : ℝ) := by linarith
  have hs_one_norm : ‖s + 1‖ ≤ 4 * (N : ℝ) := by
    calc
      ‖s + 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 * (N : ℝ) + 1 := by norm_num; linarith
      _ ≤ 4 * (N : ℝ) := by linarith
  have hpow_step (u : ℝ) :
      (N : ℝ) * (N : ℝ) ^ (-(u + 1)) = (N : ℝ) ^ (-u) := by
    calc
      (N : ℝ) * (N : ℝ) ^ (-(u + 1)) =
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(u + 1)) := by
        rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((1 : ℝ) + (-(u + 1))) :=
        (Real.rpow_add hNpos _ _).symm
      _ = (N : ℝ) ^ (-u) := by congr 1; ring
  have hpow_one :
      (N : ℝ) * (N : ℝ) ^ (-(s.re + 1)) =
        (N : ℝ) ^ (-s.re) :=
    hpow_step s.re
  have hpow_two :
      (N : ℝ) * (N : ℝ) * (N : ℝ) ^ (-(s.re + 2)) =
        (N : ℝ) ^ (-s.re) := by
    rw [mul_assoc, show -(s.re + 2) = -((s.re + 1) + 1) by ring,
      hpow_step (s.re + 1), hpow_step s.re]
  have hNpow_one :
      ‖(N : ℂ) ^ (-(s + 1))‖ =
        (N : ℝ) ^ (-(s.re + 1)) := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    simp only [neg_re, add_re, one_re]
  have hNpow_zero :
      ‖(N : ℂ) ^ (-s)‖ = (N : ℝ) ^ (-s.re) := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    simp only [neg_re]
  have hcenter_norm :
      ‖(N : ℂ) ^ (-(s + 1)) / 12 -
          (s + 1) / 2 * ∫ x in Set.Ioi (N : ℝ), G x‖ ≤
        (N : ℝ) ^ (-(s.re + 1)) / 12 +
          (‖s + 1‖ / 2) * (B * (N : ℝ) ^ (-(s.re + 2))) := by
    calc
      ‖(N : ℂ) ^ (-(s + 1)) / 12 -
          (s + 1) / 2 * ∫ x in Set.Ioi (N : ℝ), G x‖ ≤
          ‖(N : ℂ) ^ (-(s + 1)) / 12‖ +
            ‖(s + 1) / 2 * ∫ x in Set.Ioi (N : ℝ), G x‖ :=
        norm_sub_le _ _
      _ = (N : ℝ) ^ (-(s.re + 1)) / 12 +
          (‖s + 1‖ / 2) * ‖∫ x in Set.Ioi (N : ℝ), G x‖ := by
        rw [norm_div, norm_mul, norm_div, hNpow_one]
        norm_num
      _ ≤ (N : ℝ) ^ (-(s.re + 1)) / 12 +
          (‖s + 1‖ / 2) * (B * (N : ℝ) ^ (-(s.re + 2))) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hBtail
          (show 0 ≤ ‖s + 1‖ / 2 by positivity))
  have hscaled_center :
      ‖s * ((N : ℂ) ^ (-(s + 1)) / 12 -
          (s + 1) / 2 * ∫ x in Set.Ioi (N : ℝ), G x)‖ ≤
        (1 / 4 + 6 * B) * (N : ℝ) ^ (-s.re) := by
    rw [norm_mul]
    have hcoeff : ‖s + 1‖ / 2 ≤ (4 * (N : ℝ)) / 2 :=
      div_le_div_of_nonneg_right hs_one_norm (by norm_num)
    have htail_nonneg :
        0 ≤ B * (N : ℝ) ^ (-(s.re + 2)) :=
      mul_nonneg hB (Real.rpow_nonneg hNpos.le _)
    have hcenter_bound := hcenter_norm.trans
      (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hcoeff htail_nonneg))
    calc
      ‖s‖ * ‖(N : ℂ) ^ (-(s + 1)) / 12 -
          (s + 1) / 2 * ∫ x in Set.Ioi (N : ℝ), G x‖ ≤
          (3 * (N : ℝ)) *
            ((N : ℝ) ^ (-(s.re + 1)) / 12 +
              ((4 * (N : ℝ)) / 2) *
                (B * (N : ℝ) ^ (-(s.re + 2)))) := by
        exact mul_le_mul hs_norm hcenter_bound (norm_nonneg _) (by positivity)
      _ = (1 / 4 + 6 * B) * (N : ℝ) ^ (-s.re) := by
        rw [show (3 * (N : ℝ)) *
            ((N : ℝ) ^ (-(s.re + 1)) / 12 +
              ((4 * (N : ℝ)) / 2) *
                (B * (N : ℝ) ^ (-(s.re + 2)))) =
              (1 / 4) * ((N : ℝ) * (N : ℝ) ^ (-(s.re + 1))) +
                6 * B * ((N : ℝ) * (N : ℝ) *
                  (N : ℝ) ^ (-(s.re + 2))) by ring]
        rw [hpow_one, hpow_two]
        ring
  change ‖s * ∫ x in Set.Ioi (N : ℝ), E x‖ ≤
    (3 / 4 + 6 * B) * (N : ℝ) ^ (-s.re)
  rw [hformula]
  calc
    ‖s * ((N : ℂ) ^ (-(s + 1)) / 12 -
          (s + 1) / 2 * ∫ x in Set.Ioi (N : ℝ), G x) -
        (N : ℂ) ^ (-s) / 2‖ ≤
        ‖s * ((N : ℂ) ^ (-(s + 1)) / 12 -
          (s + 1) / 2 * ∫ x in Set.Ioi (N : ℝ), G x)‖ +
          ‖(N : ℂ) ^ (-s) / 2‖ := norm_sub_le _ _
    _ ≤ (1 / 4 + 6 * B) * (N : ℝ) ^ (-s.re) +
        (1 / 2) * (N : ℝ) ^ (-s.re) := by
      apply add_le_add hscaled_center
      rw [norm_div, hNpow_zero]
      norm_num
      ring_nf
      exact le_rfl
    _ = (3 / 4 + 6 * B) * (N : ℝ) ^ (-s.re) := by ring

private lemma floor_rpow_neg_le_four_mul
    {x sigma : ℝ} (hx : 1 ≤ x) (hsigma0 : 0 ≤ sigma)
    (hsigma2 : sigma ≤ 2) :
    (Nat.floor x : ℝ) ^ (-sigma) ≤ 4 * x ^ (-sigma) := by
  let N := Nat.floor x
  have hN : 1 ≤ N := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using hx
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hxlt : x < (N : ℝ) + 1 := by
    simpa only [N] using Nat.lt_floor_add_one x
  have hx_two_N : x ≤ 2 * (N : ℝ) := by
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have htwo : (2 : ℝ) ^ sigma ≤ 4 := by
    calc
      (2 : ℝ) ^ sigma ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hsigma2
      _ = 4 := by norm_num [Real.rpow_two]
  have hxpow : x ^ sigma ≤ 4 * (N : ℝ) ^ sigma := by
    calc
      x ^ sigma ≤ (2 * (N : ℝ)) ^ sigma :=
        Real.rpow_le_rpow hxpos.le hx_two_N hsigma0
      _ = (2 : ℝ) ^ sigma * (N : ℝ) ^ sigma :=
        Real.mul_rpow (by norm_num) hNpos.le
      _ ≤ 4 * (N : ℝ) ^ sigma :=
        mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hNpos.le _)
  change (N : ℝ) ^ (-sigma) ≤ 4 * x ^ (-sigma)
  rw [Real.rpow_neg hNpos.le, Real.rpow_neg hxpos.le,
    inv_eq_one_div, inv_eq_one_div, mul_one_div]
  exact (div_le_div_iff₀ (Real.rpow_pos_of_pos hNpos _)
    (Real.rpow_pos_of_pos hxpos _)).2 (by simpa using hxpow)

private lemma norm_floor_poleTerm_sub_poleTerm_le_four
    {s : ℂ} {x : ℝ} (hs : 0 < s.re) (hs2 : s.re ≤ 2)
    (hs1 : s ≠ 1) (hx : 1 ≤ x) :
    ‖(Nat.floor x : ℂ) ^ (1 - s) / (s - 1) -
        (x : ℂ) ^ (1 - s) / (s - 1)‖ ≤
      4 * x ^ (-s.re) := by
  let N := Nat.floor x
  have hN : 1 ≤ N := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using hx
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hNx : (N : ℝ) ≤ x := by
    simpa only [N] using Nat.floor_le hxpos.le
  have hzero_not_mem : (0 : ℝ) ∉ Set.uIcc (N : ℝ) x := by
    rw [Set.uIcc_of_le hNx]
    intro h
    linarith [h.1]
  have hint :
      (∫ u in (N : ℝ)..x, (u : ℂ) ^ (-s)) =
        ((x : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) := by
    simpa [show -s + 1 = 1 - s by ring] using
      (integral_cpow (a := (N : ℝ)) (b := x) (r := -s)
        (Or.inr ⟨by
          intro h
          apply hs1
          have h' := congrArg Neg.neg h
          simpa using h', hzero_not_mem⟩))
  have hcorr :
      (N : ℂ) ^ (1 - s) / (s - 1) -
          (x : ℂ) ^ (1 - s) / (s - 1) =
        ∫ u in (N : ℝ)..x, (u : ℂ) ^ (-s) := by
    rw [hint]
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have honeSub : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
    field_simp [hsub, honeSub]
    ring
  have hconst := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (N : ℝ)) (b := x) (C := (N : ℝ) ^ (-s.re))
    (f := fun u : ℝ => (u : ℂ) ^ (-s)) (fun u hu => by
      rw [Set.uIoc_of_le hNx] at hu
      have hupos : 0 < u := hNpos.trans hu.1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hupos]
      simp only [neg_re]
      exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (neg_nonpos.mpr hs.le)
        hNpos hupos hu.1.le)
  have hgap : x - (N : ℝ) ≤ 1 := by
    have hxlt : x < (N : ℝ) + 1 := by
      simpa only [N] using Nat.lt_floor_add_one x
    linarith
  change ‖(N : ℂ) ^ (1 - s) / (s - 1) -
      (x : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 4 * x ^ (-s.re)
  rw [hcorr]
  calc
    ‖∫ u in (N : ℝ)..x, (u : ℂ) ^ (-s)‖ ≤
        (N : ℝ) ^ (-s.re) * |x - (N : ℝ)| := hconst
    _ = (N : ℝ) ^ (-s.re) * (x - (N : ℝ)) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hNx)]
    _ ≤ (N : ℝ) ^ (-s.re) * 1 :=
      mul_le_mul_of_nonneg_left hgap (Real.rpow_nonneg hNpos.le _)
    _ = (N : ℝ) ^ (-s.re) := by ring
    _ ≤ 4 * x ^ (-s.re) := by
      simpa only [N] using
        floor_rpow_neg_le_four_mul hx hs.le hs2

/-- Uniform first zeta approximation with a real cutoff.  The remainder
combines the oscillatory Abel floor-error tail with the short correction from
`Nat.floor x` to `x` in the pole term. -/
theorem exists_riemannZeta_first_approximation :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℂ) (x : ℝ),
      (1 / 4 : ℝ) ≤ s.re → s.re ≤ 2 → s ≠ 1 → 1 ≤ x →
        |s.im| ≤ x / 2 →
          ∃ R : ℂ,
            riemannZeta s =
              (∑ n ∈ Finset.Icc 1 (Nat.floor x), 1 / (n : ℂ) ^ s) +
                (x : ℂ) ^ (1 - s) / (s - 1) + R ∧
            ‖R‖ ≤ C * x ^ (-s.re) := by
  obtain ⟨A, hA, htail⟩ :=
    exists_norm_mul_integral_Ioi_floorError_cpow_le
  refine ⟨4 * A + 4, by positivity, ?_⟩
  intro s x hs_lower hs_upper hs1 hx him
  let N := Nat.floor x
  let E : ℂ := s * ∫ u in Set.Ioi (N : ℝ),
    ((((⌊u⌋₊ : ℝ) - u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1)))
  let D : ℂ := (N : ℂ) ^ (1 - s) / (s - 1) -
    (x : ℂ) ^ (1 - s) / (s - 1)
  have hs : 0 < s.re := lt_of_lt_of_le (by norm_num) hs_lower
  have hN : 1 ≤ N := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using hx
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hxlt : x < (N : ℝ) + 1 := by
    simpa only [N] using Nat.lt_floor_add_one x
  have hx_half_le_N : x / 2 ≤ (N : ℝ) := by
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have himN : |s.im| ≤ (N : ℝ) := him.trans hx_half_le_N
  have hE : ‖E‖ ≤ A * (N : ℝ) ^ (-s.re) := by
    simpa only [E] using htail hs_lower hs_upper hN himN
  have hfloorCompare :
      (N : ℝ) ^ (-s.re) ≤ 4 * x ^ (-s.re) := by
    simpa only [N] using floor_rpow_neg_le_four_mul hx hs.le hs_upper
  have hEx : ‖E‖ ≤ (4 * A) * x ^ (-s.re) := by
    calc
      ‖E‖ ≤ A * (N : ℝ) ^ (-s.re) := hE
      _ ≤ A * (4 * x ^ (-s.re)) :=
        mul_le_mul_of_nonneg_left hfloorCompare hA
      _ = (4 * A) * x ^ (-s.re) := by ring
  have hD : ‖D‖ ≤ 4 * x ^ (-s.re) := by
    simpa only [D, N] using
      norm_floor_poleTerm_sub_poleTerm_le_four hs hs_upper hs1 hx
  have hzeta :=
    ZeroFreeRegion.riemannZeta_eq_dirichletPolynomial_add_pole_add_floorErrorTail
      hs hs1 hN
  refine ⟨E + D, ?_, ?_⟩
  · dsimp only [E, D, N]
    rw [hzeta]
    ring
  · calc
      ‖E + D‖ ≤ ‖E‖ + ‖D‖ := norm_add_le _ _
      _ ≤ (4 * A) * x ^ (-s.re) + 4 * x ^ (-s.re) :=
        add_le_add hEx hD
      _ = (4 * A + 4) * x ^ (-s.re) := by ring

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

private lemma norm_criticalLine_poleTerm_le_two_div_sqrt
    {T t : ℝ} (hT : 1 ≤ T) (ht : t ∈ Set.Icc T (2 * T)) :
    ‖(4 * T : ℂ) ^ (1 - ((1 / 2 : ℂ) + I * t)) /
        (((1 / 2 : ℂ) + I * t) - 1)‖ ≤
      2 / Real.sqrt T := by
  let s : ℂ := (1 / 2 : ℂ) + I * t
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have h4Tpos : 0 < 4 * T := by positivity
  have htpos : 0 < t := hTpos.trans_le ht.1
  have hnum :
      ‖(4 * T : ℂ) ^ (1 - s)‖ = 2 * Real.sqrt T := by
    rw [show (4 * T : ℂ) = ((4 * T : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos h4Tpos]
    norm_num [s, sub_re, add_re, div_re, mul_re]
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hden : T ≤ ‖s - 1‖ := by
    calc
      T ≤ t := ht.1
      _ = |t| := (abs_of_pos htpos).symm
      _ = |(s - 1).im| := by simp [s]
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  have hdenpos : 0 < ‖s - 1‖ := hTpos.trans_le hden
  change ‖(4 * T : ℂ) ^ (1 - s) / (s - 1)‖ ≤
    2 / Real.sqrt T
  rw [norm_div, hnum]
  calc
    (2 * Real.sqrt T) / ‖s - 1‖ ≤
        (2 * Real.sqrt T) / T :=
      div_le_div_of_nonneg_left (by positivity) hTpos hden
    _ = 2 / Real.sqrt T := by
      have hsqrtpos : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
      field_simp [hsqrtpos.ne', hTpos.ne']
      nlinarith [Real.sq_sqrt hTpos.le]

/-- On a Hardy dyadic interval, the first zeta approximation has a remainder
of size `O(T⁻¹/²)` after the elementary pole term is absorbed. -/
theorem criticalLineZetaFirstApprox :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T t : ℝ,
      T0 ≤ T → t ∈ Set.Icc T (2 * T) →
        ∃ R : ℂ,
          riemannZeta ((1 / 2 : ℂ) + I * t) =
            (∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
              1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) + R ∧
          ‖R‖ ≤ C / Real.sqrt T := by
  obtain ⟨A, hA, hfirst⟩ := exists_riemannZeta_first_approximation
  refine ⟨A + 2, 1, by positivity, le_rfl, ?_⟩
  intro T t hT ht
  let s : ℂ := (1 / 2 : ℂ) + I * t
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have htpos : 0 < t := hTpos.trans_le ht.1
  have hs_re : s.re = 1 / 2 := by simp [s]
  have hs_im : s.im = t := by simp [s]
  have hs1 : s ≠ 1 := by
    intro h
    have him_eq := congrArg Complex.im h
    simp only [hs_im, one_im] at him_eq
    linarith
  have h4T : 1 ≤ 4 * T := by linarith
  have him_bound : |s.im| ≤ (4 * T) / 2 := by
    rw [hs_im, abs_of_pos htpos]
    linarith [ht.2]
  obtain ⟨R₀, hzeta, hR₀⟩ := hfirst s (4 * T)
    (by rw [hs_re]; norm_num) (by rw [hs_re]; norm_num) hs1 h4T him_bound
  let P : ℂ := (4 * T : ℂ) ^ (1 - s) / (s - 1)
  have hP : ‖P‖ ≤ 2 / Real.sqrt T := by
    simpa only [P, s] using norm_criticalLine_poleTerm_le_two_div_sqrt hT ht
  have hpow : (4 * T) ^ (-s.re) ≤ T ^ (-s.re) := by
    apply Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (by rw [hs_re]; norm_num)
    · exact hTpos
    · exact (show 0 < 4 * T by positivity)
    · linarith
  have hR₀' : ‖R₀‖ ≤ A / Real.sqrt T := by
    calc
      ‖R₀‖ ≤ A * (4 * T) ^ (-s.re) := hR₀
      _ ≤ A * T ^ (-s.re) := mul_le_mul_of_nonneg_left hpow hA
      _ = A / Real.sqrt T := by
        rw [hs_re, Real.rpow_neg hTpos.le, ← Real.sqrt_eq_rpow,
          div_eq_mul_inv]
  refine ⟨P + R₀, ?_, ?_⟩
  · change riemannZeta s =
      (∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
        1 / (n : ℂ) ^ s) + (P + R₀)
    rw [hzeta]
    dsimp only [P, firstZetaApproximationCutoff]
    push_cast
    ring
  · calc
      ‖P + R₀‖ ≤ ‖P‖ + ‖R₀‖ := norm_add_le _ _
      _ ≤ 2 / Real.sqrt T + A / Real.sqrt T := add_le_add hP hR₀'
      _ = (A + 2) / Real.sqrt T := by ring

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

/-- The first zeta approximation forces a linear lower bound for the dyadic
`L¹` norm of zeta on the critical line. -/
theorem exists_integral_norm_riemannZeta_critical_line_ge_mul :
    ∃ c T0 : ℝ, 0 < c ∧ 1 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T →
      c * T ≤ ∫ t in T..(2 * T),
        ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ := by
  obtain ⟨C, Tapprox, hC, hTapprox, happ⟩ := criticalLineZetaFirstApprox
  have htail_event :=
    norm_integral_criticalLineDirichletTail_cutoff_isLittleO.bound
      (show (0 : ℝ) < 1 / 4 by norm_num)
  obtain ⟨Ttail, htail_after⟩ := eventually_atTop.1 htail_event
  let T0 : ℝ := max Tapprox (max Ttail (16 * C ^ 2))
  refine ⟨1 / 2, T0, by norm_num, ?_, ?_⟩
  · exact hTapprox.trans (le_max_left _ _)
  intro T hT
  have hTa : Tapprox ≤ T := (le_max_left _ _).trans hT
  have hTrest : max Ttail (16 * C ^ 2) ≤ T :=
    (le_max_right Tapprox _).trans hT
  have hTtail : Ttail ≤ T := (le_max_left _ _).trans hTrest
  have hTerr : 16 * C ^ 2 ≤ T := (le_max_right _ _).trans hTrest
  have hT1 : 1 ≤ T := hTapprox.trans hTa
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have hTtwo : T ≤ 2 * T := by linarith
  let F : ℝ → ℂ := fun t => riemannZeta ((1 / 2 : ℂ) + I * t)
  let Q : ℝ → ℂ := fun t =>
    ∑ n ∈ Finset.Icc 2 (firstZetaApproximationCutoff T),
      1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)
  let H : ℝ → ℂ := fun t => F t - (1 + Q t)
  have hcutoff : 1 ≤ firstZetaApproximationCutoff T := by
    apply Nat.le_floor
    simpa only [Nat.cast_one, firstZetaApproximationCutoff] using
      (show (1 : ℝ) ≤ 4 * T by linarith)
  have hsum_split (t : ℝ) :
      (∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
          1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) = 1 + Q t := by
    have hset : Finset.Icc 1 (firstZetaApproximationCutoff T) =
        insert 1 (Finset.Icc 2 (firstZetaApproximationCutoff T)) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    simp only [Q, Nat.cast_one, one_cpow, one_div]
    norm_num
  have hHpoint : ∀ t ∈ Set.Icc T (2 * T),
      ‖H t‖ ≤ C / Real.sqrt T := by
    intro t ht
    obtain ⟨R, hzeta, hR⟩ := happ T t hTa ht
    have hHR : H t = R := by
      dsimp only [H, F]
      rw [hzeta, hsum_split]
      ring
    rw [hHR]
    exact hR
  have hQcont : Continuous Q := by
    dsimp only [Q]
    apply continuous_finset_sum
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : n ≠ 0 := by omega
    rw [show (fun t : ℝ =>
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) =
      (fun t : ℝ => ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
        Complex.exp ((-I * (Real.log n : ℂ)) * t)) by
          funext t
          exact inv_nat_cpow_criticalLine_eq_exp hn0 t]
    fun_prop
  have hQint : IntervalIntegrable Q volume T (2 * T) :=
    hQcont.intervalIntegrable _ _
  have hFcont : ContinuousOn F (Set.Icc T (2 * T)) := by
    intro t ht
    have htpos : 0 < t := hTpos.trans_le ht.1
    have hs1 : ((1 / 2 : ℂ) + I * t) ≠ 1 := by
      intro h
      have him := congrArg Complex.im h
      norm_num at him
      linarith
    have hpath : ContinuousAt (fun u : ℝ => (1 / 2 : ℂ) + I * u) t := by
      fun_prop
    have hzbase : ContinuousAt riemannZeta ((1 / 2 : ℂ) + I * t) :=
      (differentiableAt_riemannZeta hs1).continuousAt
    have hzcont : ContinuousAt
        (riemannZeta ∘ fun u : ℝ => (1 / 2 : ℂ) + I * u) t :=
      (show Tendsto riemannZeta
          (nhds ((1 / 2 : ℂ) + I * t))
          (nhds (riemannZeta ((1 / 2 : ℂ) + I * t))) from hzbase).comp
        (show Tendsto (fun u : ℝ => (1 / 2 : ℂ) + I * u)
          (nhds t) (nhds ((1 / 2 : ℂ) + I * t)) from hpath)
    simpa only [F, Function.comp_apply] using hzcont.continuousWithinAt
  have hFint : IntervalIntegrable F volume T (2 * T) :=
    ContinuousOn.intervalIntegrable (by
      simpa only [Set.uIcc_of_le hTtwo] using hFcont)
  have hUint : IntervalIntegrable (fun t => (1 : ℂ) + Q t) volume T (2 * T) :=
    continuous_const.intervalIntegrable _ _ |>.add hQint
  have hHint : IntervalIntegrable H volume T (2 * T) := by
    dsimp only [H]
    exact hFint.sub hUint
  have hHintegral :
      (∫ t in T..(2 * T), H t) =
        (∫ t in T..(2 * T), F t) -
          ((∫ _t in T..(2 * T), (1 : ℂ)) +
            ∫ t in T..(2 * T), Q t) := by
    dsimp only [H]
    rw [intervalIntegral.integral_sub hFint hUint,
      intervalIntegral.integral_add
        (continuous_const.intervalIntegrable _ _) hQint]
  have hone : (∫ _t in T..(2 * T), (1 : ℂ)) = (T : ℂ) := by
    simp
    change (((2 * T - T : ℝ) : ℂ) * 1) = (T : ℂ)
    push_cast
    ring
  have hOneEq :
      (T : ℂ) =
        (∫ t in T..(2 * T), F t) -
          (∫ t in T..(2 * T), Q t) -
            ∫ t in T..(2 * T), H t := by
    rw [hHintegral, hone]
    ring
  have htail_small :
      ‖∫ t in T..(2 * T), Q t‖ ≤ T / 4 := by
    have hsmall := htail_after T hTtail
    rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg hTpos.le] at hsmall
    dsimp only [Q]
    nlinarith [hsmall]
  have hfourC_le_sqrt : 4 * C ≤ Real.sqrt T := by
    calc
      4 * C = Real.sqrt (16 * C ^ 2) := by
        rw [show 16 * C ^ 2 = (4 * C) ^ 2 by ring,
          Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hC)]
      _ ≤ Real.sqrt T := Real.sqrt_le_sqrt hTerr
  have herror_small :
      ‖∫ t in T..(2 * T), H t‖ ≤ T / 4 := by
    have hmajor := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := T) (b := 2 * T) (C := C / Real.sqrt T) (f := H)
      (fun t ht => by
        rw [Set.uIoc_of_le hTtwo] at ht
        exact hHpoint t ⟨ht.1.le, ht.2⟩)
    have hsqrtpos : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
    calc
      ‖∫ t in T..(2 * T), H t‖ ≤
          (C / Real.sqrt T) * |2 * T - T| := hmajor
      _ = C * Real.sqrt T := by
        rw [abs_of_nonneg (by linarith : 0 ≤ 2 * T - T)]
        field_simp [hsqrtpos.ne']
        nlinarith [Real.sq_sqrt hTpos.le]
      _ ≤ T / 4 := by
        have hmul := mul_le_mul_of_nonneg_right hfourC_le_sqrt
          (Real.sqrt_nonneg T)
        nlinarith [Real.sq_sqrt hTpos.le]
  have htriangle :
      T ≤ ‖∫ t in T..(2 * T), F t‖ +
          ‖∫ t in T..(2 * T), Q t‖ +
            ‖∫ t in T..(2 * T), H t‖ := by
    calc
      T = ‖(T : ℂ)‖ := by
        rw [norm_real, Real.norm_eq_abs, abs_of_pos hTpos]
      _ = ‖(∫ t in T..(2 * T), F t) -
          (∫ t in T..(2 * T), Q t) -
            ∫ t in T..(2 * T), H t‖ := congrArg norm hOneEq
      _ ≤ ‖(∫ t in T..(2 * T), F t) -
          (∫ t in T..(2 * T), Q t)‖ +
            ‖∫ t in T..(2 * T), H t‖ := norm_sub_le _ _
      _ ≤ (‖∫ t in T..(2 * T), F t‖ +
          ‖∫ t in T..(2 * T), Q t‖) +
            ‖∫ t in T..(2 * T), H t‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
  have hlower : (1 / 2 : ℝ) * T ≤ ‖∫ t in T..(2 * T), F t‖ := by
    linarith
  have hnormIntegral := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := F) hTtwo
  change (1 / 2 : ℝ) * T ≤ ∫ t in T..(2 * T), ‖F t‖
  exact hlower.trans hnormIntegral

end HardyTheorem
