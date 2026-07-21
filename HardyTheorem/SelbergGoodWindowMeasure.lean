import HardyTheorem.HardyLittlewoodOddTheorem
import HardyTheorem.SelbergMollifier
import HardyTheorem.SelbergPacking

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace HardyTheorem

/-!
# Conditional Selberg good-window bridge

This file isolates the two analytic estimates needed by the Selberg
short-window argument.  The hypotheses are stated directly as measure bounds
for starts where the mollified absolute mass is too small or its signed mass
is too large.
-/

/-- The signed short integral of the Möbius-mollified Hardy function. -/
noncomputable def selbergMoebiusSignedShortIntegral
    (X : ℕ) (H t : ℝ) : ℝ :=
  ∫ u in t..t + H, selbergMoebiusMollifiedHardyZ X u

/-- The short integral of the absolute value of the Möbius-mollified Hardy
function. -/
noncomputable def selbergMoebiusAbsShortIntegral
    (X : ℕ) (H t : ℝ) : ℝ :=
  ∫ u in t..t + H, |selbergMoebiusMollifiedHardyZ X u|

/-- Starts whose mollified absolute mass does not exceed `eta`. -/
def selbergSmallAbsoluteMassStarts (X : ℕ) (H eta : ℝ) : Set ℝ :=
  {t | selbergMoebiusAbsShortIntegral X H t ≤ eta}

/-- Starts whose signed mollified mass has magnitude at least `eta`. -/
def selbergExcessiveSignedMassStarts (X : ℕ) (H eta : ℝ) : Set ℝ :=
  {t | eta ≤ |selbergMoebiusSignedShortIntegral X H t|}

/-- Starts avoiding both analytic exceptional sets. -/
def selbergGoodWindowStarts (X : ℕ) (H eta : ℝ) : Set ℝ :=
  (selbergSmallAbsoluteMassStarts X H eta ∪
    selbergExcessiveSignedMassStarts X H eta)ᶜ

private theorem analyticOnNhd_selbergMoebiusMollifier (X : ℕ) :
    AnalyticOnNhd ℂ (selbergMoebiusMollifier X) Set.univ := by
  unfold selbergMoebiusMollifier selbergMollifier
  apply Finset.analyticOnNhd_fun_sum
  intro n hn
  have hn0 : n ≠ 0 := by
    exact Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
  have hpow : AnalyticOnNhd ℂ (fun s : ℂ => (n : ℂ) ^ s) Set.univ :=
    analyticOnNhd_const.cpow analyticOnNhd_id fun _ _ =>
      Complex.natCast_mem_slitPlane.mpr hn0
  have hinv : AnalyticOnNhd ℂ (fun s : ℂ => ((n : ℂ) ^ s)⁻¹) Set.univ :=
    hpow.inv fun _ _ => Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn0))
  simpa only [one_div] using
    analyticOnNhd_const.mul hinv

private theorem tendsto_selbergMoebiusMollifier_real_atTop
    (X : ℕ) (hX : 1 ≤ X) :
    Tendsto (fun sigma : ℝ =>
      selbergMoebiusMollifier X (sigma : ℂ)) atTop (nhds 1) := by
  unfold selbergMoebiusMollifier selbergMollifier
  have hterm : ∀ n ∈ Finset.Icc 1 X,
      Tendsto (fun sigma : ℝ =>
        (selbergMoebiusCoeff X n : ℂ) *
          (1 / (n : ℂ) ^ (sigma : ℂ))) atTop
        (nhds (if n = 1 then 1 else 0)) := by
    intro n hn
    by_cases hn1 : n = 1
    · subst n
      simpa using (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (1 : ℂ)) atTop (nhds 1))
    · have hn2 : 2 ≤ n := by
        have hnlow := (Finset.mem_Icc.mp hn).1
        omega
      have hnreal : (1 : ℝ) < n := by exact_mod_cast hn2
      have hinvpos : 0 < ((n : ℝ)⁻¹) := inv_pos.mpr (by positivity)
      have hinvlt : ((n : ℝ)⁻¹) < 1 :=
        (inv_lt_one₀ (by positivity)).2 hnreal
      have hreal : Tendsto (fun sigma : ℝ => ((n : ℝ)⁻¹) ^ sigma)
          atTop (nhds 0) :=
        tendsto_rpow_atTop_of_base_lt_one _ (by linarith) hinvlt
      have hcomplex : Tendsto (fun sigma : ℝ =>
          ((((n : ℝ)⁻¹) ^ sigma : ℝ) : ℂ)) atTop (nhds 0) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
      have hmul : Tendsto (fun sigma : ℝ =>
          (selbergMoebiusCoeff X n : ℂ) *
            ((((n : ℝ)⁻¹) ^ sigma : ℝ) : ℂ)) atTop (nhds 0) := by
        simpa only [mul_zero] using
          hcomplex.const_mul (selbergMoebiusCoeff X n : ℂ)
      rw [if_neg hn1]
      convert hmul using 1
      funext sigma
      rw [one_div]
      have hcpow : (n : ℂ) ^ (sigma : ℂ) =
          (((n : ℝ) ^ sigma : ℝ) : ℂ) := by
        simpa only [Complex.ofReal_natCast] using
          (Complex.ofReal_cpow (Nat.cast_nonneg n) sigma).symm
      rw [hcpow, ← Complex.ofReal_inv,
        ← Real.inv_rpow (Nat.cast_nonneg n) sigma]
  have hsum := tendsto_finset_sum (Finset.Icc 1 X) hterm
  convert hsum using 1
  simp [hX]

private theorem exists_selbergMoebiusMollifier_ne_zero
    (X : ℕ) (hX : 1 ≤ X) :
    ∃ s : ℂ, selbergMoebiusMollifier X s ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hzero : Tendsto (fun sigma : ℝ =>
      selbergMoebiusMollifier X (sigma : ℂ)) atTop (nhds 0) := by
    simpa only [hnone] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (nhds 0))
  have honezero : (1 : ℂ) = 0 := tendsto_nhds_unique
    (tendsto_selbergMoebiusMollifier_real_atTop X hX) hzero
  norm_num at honezero

private theorem analyticOnNhd_selbergMoebiusMollifier_vertical (X : ℕ) :
    AnalyticOnNhd ℂ (fun z : ℂ =>
      selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * z)) Set.univ := by
  have haffine : AnalyticOnNhd ℂ (fun z : ℂ =>
      (1 / 2 : ℂ) + I * z) Set.univ :=
    analyticOnNhd_const.add (analyticOnNhd_const.mul analyticOnNhd_id)
  simpa only [Function.comp_apply] using
    (analyticOnNhd_selbergMoebiusMollifier X).comp haffine
      (Set.mapsTo_univ _ _)

private theorem exists_selbergMoebiusMollifier_criticalLine_ne_zero_Ioo
    (X : ℕ) (hX : 1 ≤ X) {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Set.Ioo a b,
      selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) ≠ 0 := by
  by_contra hnone
  push Not at hnone
  let c : ℝ := (a + b) / 2
  let d : ℝ := (b - a) / 4
  let u : ℕ → ℂ := fun n => (c + d / (n + 1 : ℝ) : ℝ)
  have hd : 0 < d := by
    dsimp only [d]
    linarith
  have hu_tendsto : Tendsto u atTop (nhds (c : ℂ)) := by
    have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ))
        atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hfrac : Tendsto (fun n : ℕ => d / (n + 1 : ℝ)) atTop (nhds 0) := by
      simpa only [div_eq_mul_inv, one_mul, mul_zero] using hone.const_mul d
    have hadd : Tendsto (fun n : ℕ => c + d / (n + 1 : ℝ))
        atTop (nhds c) := by
      simpa only [add_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (nhds c)).add hfrac
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      hadd
  have hu_mem : ∀ n : ℕ, u n ∈
      {z : ℂ | selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * z) = 0} \
        {(c : ℂ)} := by
    intro n
    have hden : (0 : ℝ) < n + 1 := by positivity
    have hfracpos : 0 < d / (n + 1 : ℝ) := div_pos hd hden
    have hfracle : d / (n + 1 : ℝ) ≤ d := by
      apply (div_le_iff₀ hden).2
      have hdenone : (1 : ℝ) ≤ n + 1 := by
        exact_mod_cast Nat.succ_pos n
      nlinarith
    have huIoo : (c + d / (n + 1 : ℝ)) ∈ Set.Ioo a b := by
      have hac : a < c := by
        dsimp only [c]
        linarith
      have hcdb : c + d < b := by
        dsimp only [c, d]
        linarith
      constructor <;> linarith
    constructor
    · simpa only [u, Complex.ofReal_add, Complex.ofReal_div,
        Complex.ofReal_natCast, Complex.ofReal_one] using hnone _ huIoo
    · intro heq
      have hre := congr_arg Complex.re heq
      simp only [u, Complex.ofReal_re] at hre
      linarith
  have hclosure : (c : ℂ) ∈ closure
      ({z : ℂ | selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * z) = 0} \
        {(c : ℂ)}) :=
    mem_closure_of_tendsto hu_tendsto (Filter.Eventually.of_forall hu_mem)
  have hident :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure
      (analyticOnNhd_selbergMoebiusMollifier_vertical X)
        isPreconnected_univ (Set.mem_univ (c : ℂ)) hclosure
  obtain ⟨s, hs⟩ := exists_selbergMoebiusMollifier_ne_zero X hX
  let z : ℂ := -I * (s - (1 / 2 : ℂ))
  have harg : (1 / 2 : ℂ) + I * z = s := by
    dsimp only [z]
    ring_nf
    simp
  exact hs (by simpa only [harg] using hident (Set.mem_univ z))

private theorem exists_selbergMoebiusMollifiedHardyZ_ne_zero_Ioo
    (X : ℕ) (hX : 1 ≤ X) {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Set.Ioo a b, selbergMoebiusMollifiedHardyZ X t ≠ 0 := by
  obtain ⟨v, hv, hvHardy⟩ := exists_hardyZ_ne_zero_Ioo hab
  have hnear : ∀ᶠ t : ℝ in nhds v, hardyZ t ≠ 0 :=
    hardyZ_continuous.continuousAt.eventually_ne hvHardy
  rw [Metric.eventually_nhds_iff] at hnear
  obtain ⟨epsilon, hepsilon, hbound⟩ := hnear
  let r : ℝ := min (epsilon / 2) (min ((v - a) / 2) ((b - v) / 2))
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min (half_pos hepsilon)
      (lt_min (half_pos (sub_pos.mpr hv.1)) (half_pos (sub_pos.mpr hv.2)))
  obtain ⟨t, ht, htM⟩ :=
    exists_selbergMoebiusMollifier_criticalLine_ne_zero_Ioo
      X hX (show v - r < v + r by linarith)
  have htIoo : t ∈ Set.Ioo a b := by
    have htLow : v - r < t := by simpa only [r] using ht.1
    have htHigh : t < v + r := by simpa only [r] using ht.2
    constructor
    · have hrva : r ≤ (v - a) / 2 :=
        min_le_right _ _ |>.trans (min_le_left _ _)
      linarith
    · have hrvb : r ≤ (b - v) / 2 :=
        min_le_right _ _ |>.trans (min_le_right _ _)
      linarith
  have htHardy : hardyZ t ≠ 0 := by
    apply hbound
    rw [Real.dist_eq, abs_lt]
    have hre : r ≤ epsilon / 2 := min_le_left _ _
    have htLow : v - r < t := by simpa only [r] using ht.1
    have htHigh : t < v + r := by simpa only [r] using ht.2
    constructor <;> linarith
  refine ⟨t, htIoo, ?_⟩
  rw [selbergMoebiusMollifiedHardyZ, selbergMollifiedHardyZ]
  exact mul_ne_zero htHardy (mt Complex.normSq_eq_zero.mp htM)

/-- A good start gives strict cancellation and hence a genuine local sign
change of the actual Möbius-mollified Hardy function. -/
theorem exists_selbergMoebiusMollifiedHardyZ_localSignChange_of_goodStart
    {X : ℕ} (hX : 1 ≤ X) {H eta t : ℝ} (hH : 0 ≤ H)
    (ht : t ∈ selbergGoodWindowStarts X H eta) :
    ∃ u ∈ Set.Ioo t (t + H),
      HasLocalSignChangeAt (selbergMoebiusMollifiedHardyZ X) u := by
  have hnot := ht
  rw [selbergGoodWindowStarts, Set.mem_compl_iff, Set.mem_union] at hnot
  have hparts := not_or.mp hnot
  have hnotSmall : ¬ selbergMoebiusAbsShortIntegral X H t ≤ eta := by
    simpa only [selbergSmallAbsoluteMassStarts, Set.mem_setOf_eq] using hparts.1
  have hnotExcessive : ¬ eta ≤ |selbergMoebiusSignedShortIntegral X H t| := by
    simpa only [selbergExcessiveSignedMassStarts, Set.mem_setOf_eq] using hparts.2
  have hstrict : |selbergMoebiusSignedShortIntegral X H t| <
      selbergMoebiusAbsShortIntegral X H t :=
    (lt_of_not_ge hnotExcessive).trans (lt_of_not_ge hnotSmall)
  have hchange :=
    MathlibAux.exists_local_sign_change_of_abs_intervalIntegral_lt_intervalIntegral_abs
      (continuous_selbergMoebiusMollifiedHardyZ X)
      (show t ≤ t + H by linarith)
      (by simpa only [selbergMoebiusSignedShortIntegral,
          selbergMoebiusAbsShortIntegral] using hstrict)
      (fun a b hab =>
        exists_selbergMoebiusMollifiedHardyZ_ne_zero_Ioo X hX hab)
  simpa only [HasLocalSignChangeAt, HasNegToPosLocalSignChangeAt,
    HasPosToNegLocalSignChangeAt] using hchange

/-- A good mollified window contains a genuine local sign change of Hardy's
unmollified `Z` function. -/
theorem exists_hardyZ_localSignChange_of_selbergGoodStart
    {X : ℕ} (hX : 1 ≤ X) {H eta t : ℝ} (hH : 0 ≤ H)
    (ht : t ∈ selbergGoodWindowStarts X H eta) :
    ∃ u ∈ Set.Ioo t (t + H), HasLocalSignChangeAt hardyZ u := by
  obtain ⟨u, hu, hchange⟩ :=
    exists_selbergMoebiusMollifiedHardyZ_localSignChange_of_goodStart
      hX hH ht
  exact ⟨u, hu, hasLocalSignChangeAt_hardyZ_of_mollified hchange⟩

/-- The two concrete Selberg bad-set estimates at logarithmic window length
imply the odd-multiplicity Selberg zero-proportion target. -/
theorem selberg_odd_zero_proportion_target_of_mollified_good_window_bounds
    (A T0 : ℝ) (X : ℝ → ℕ) (eta : ℝ → ℝ) (hA : 0 < A)
    (hX : ∀ T ≥ T0, 1 ≤ X T)
    (hsmall : ∀ T ≥ T0,
      volume.real
          (Set.Icc T (2 * T - A / Real.log T) ∩
            selbergSmallAbsoluteMassStarts
              (X T) (A / Real.log T) (eta T)) ≤ T / 24)
    (hexcessive : ∀ T ≥ T0,
      volume.real
          (Set.Icc T (2 * T - A / Real.log T) ∩
            selbergExcessiveSignedMassStarts
              (X T) (A / Real.log T) (eta T)) ≤ T / 24) :
    selberg_odd_zero_proportion_target := by
  let T1 : ℝ := max T0 (Real.exp 1)
  let good : ℝ → Set ℝ := fun T =>
    selbergGoodWindowStarts (X T) (A / Real.log T) (eta T)
  apply selberg_odd_zero_proportion_target_of_log_good_window_measure
    A T1 good hA
  · intro T hT
    have hT0 : T0 ≤ T := (le_max_left _ _).trans hT
    let I : Set ℝ := Set.Icc T (2 * T - A / Real.log T)
    let small : Set ℝ :=
      selbergSmallAbsoluteMassStarts (X T) (A / Real.log T) (eta T)
    let excessive : Set ℝ :=
      selbergExcessiveSignedMassStarts (X T) (A / Real.log T) (eta T)
    have hsubset : I \ good T ⊆ (I ∩ small) ∪ (I ∩ excessive) := by
      intro t ht
      rcases ht with ⟨htI, htbad⟩
      change t ∉ (small ∪ excessive)ᶜ at htbad
      simp only [Set.mem_compl_iff, Set.mem_union, not_not] at htbad
      rcases htbad with htSmall | htExcessive
      · exact Or.inl ⟨htI, htSmall⟩
      · exact Or.inr ⟨htI, htExcessive⟩
    have hunion_ne_top : volume ((I ∩ small) ∪ (I ∩ excessive)) ≠ ⊤ := by
      apply measure_ne_top_of_subset
        (union_subset inter_subset_left inter_subset_left)
      simpa only [I] using (measure_Icc_lt_top :
        volume (Set.Icc T (2 * T - A / Real.log T)) < ⊤).ne
    have hmono : volume.real (I \ good T) ≤
        volume.real ((I ∩ small) ∪ (I ∩ excessive)) :=
      measureReal_mono hsubset hunion_ne_top
    calc
      volume.real
          (Set.Icc T (2 * T - A / Real.log T) \ good T) =
          volume.real (I \ good T) := by rfl
      _ ≤ volume.real ((I ∩ small) ∪ (I ∩ excessive)) := hmono
      _ ≤ volume.real (I ∩ small) + volume.real (I ∩ excessive) :=
        measureReal_union_le _ _
      _ ≤ T / 12 := by
        have hs := hsmall T hT0
        have he := hexcessive T hT0
        change volume.real (I ∩ small) ≤ T / 24 at hs
        change volume.real (I ∩ excessive) ≤ T / 24 at he
        nlinarith
  · intro T hT t ht
    have hT0 : T0 ≤ T := (le_max_left _ _).trans hT
    have hTexp : Real.exp 1 ≤ T := (le_max_right _ _).trans hT
    have hTpos : 0 < T := (Real.exp_pos 1).trans_le hTexp
    have hlogone : 1 ≤ Real.log T := by
      rw [Real.le_log_iff_exp_le hTpos]
      exact hTexp
    have hH : 0 ≤ A / Real.log T :=
      div_nonneg hA.le (zero_le_one.trans hlogone)
    exact exists_hardyZ_localSignChange_of_selbergGoodStart
      (hX T hT0) hH ht.1

end HardyTheorem
