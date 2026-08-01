import HardyTheorem.HardyLittlewoodOddTheorem
import HardyTheorem.SelbergMollifier

open Complex Filter Set

namespace HardyTheorem

/-!
# Nonvanishing intervals for finite Selberg mollifiers

The good-window argument only needs the finite mollifier to have constant
coefficient one.  The specific Möbius coefficients are irrelevant for the
analytic nonvanishing step.  This file exposes that fact for reuse by the
square-root-zeta mollifier.
-/

/-- A finite Selberg mollifier is entire for arbitrary coefficients. -/
theorem analyticOnNhd_selbergMollifier
    (X : ℕ) (coeff : ℕ → ℂ) :
    AnalyticOnNhd ℂ (selbergMollifier X coeff) Set.univ := by
  unfold selbergMollifier
  apply Finset.analyticOnNhd_fun_sum
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
  have hpow : AnalyticOnNhd ℂ (fun s : ℂ => (n : ℂ) ^ s) Set.univ :=
    analyticOnNhd_const.cpow analyticOnNhd_id fun _ _ =>
      Complex.natCast_mem_slitPlane.mpr hn0
  have hinv : AnalyticOnNhd ℂ (fun s : ℂ => ((n : ℂ) ^ s)⁻¹) Set.univ :=
    hpow.inv fun _ _ =>
      Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Nat.cast_ne_zero.mpr hn0))
  simpa only [one_div] using analyticOnNhd_const.mul hinv

/-- If the constant coefficient is one, a finite Selberg mollifier tends to
one on the positive real axis. -/
theorem tendsto_selbergMollifier_real_atTop
    (X : ℕ) (coeff : ℕ → ℂ) (hX : 1 ≤ X) (hcoeff : coeff 1 = 1) :
    Tendsto (fun sigma : ℝ => selbergMollifier X coeff (sigma : ℂ))
      atTop (nhds 1) := by
  unfold selbergMollifier
  have hterm : ∀ n ∈ Finset.Icc 1 X,
      Tendsto (fun sigma : ℝ =>
        coeff n * (1 / (n : ℂ) ^ (sigma : ℂ))) atTop
        (nhds (if n = 1 then 1 else 0)) := by
    intro n hn
    by_cases hn1 : n = 1
    · subst n
      simpa [hcoeff] using
        (tendsto_const_nhds :
          Tendsto (fun _ : ℝ => (1 : ℂ)) atTop (nhds 1))
    · have hn2 : 2 ≤ n := by
        have hnlow := (Finset.mem_Icc.mp hn).1
        omega
      have hnreal : (1 : ℝ) < n := by exact_mod_cast hn2
      have hinvpos : 0 < ((n : ℝ)⁻¹) := inv_pos.mpr (by positivity)
      have hinvlt : ((n : ℝ)⁻¹) < 1 :=
        (inv_lt_one₀ (by positivity)).2 hnreal
      have hreal :
          Tendsto (fun sigma : ℝ => ((n : ℝ)⁻¹) ^ sigma)
            atTop (nhds 0) :=
        tendsto_rpow_atTop_of_base_lt_one _ (by linarith) hinvlt
      have hcomplex :
          Tendsto (fun sigma : ℝ =>
            ((((n : ℝ)⁻¹) ^ sigma : ℝ) : ℂ)) atTop (nhds 0) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
      have hmul :
          Tendsto (fun sigma : ℝ =>
            coeff n * ((((n : ℝ)⁻¹) ^ sigma : ℝ) : ℂ))
            atTop (nhds 0) := by
        simpa only [mul_zero] using hcomplex.const_mul (coeff n)
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

/-- A finite Selberg mollifier with constant coefficient one is not
identically zero. -/
theorem exists_selbergMollifier_ne_zero
    (X : ℕ) (coeff : ℕ → ℂ) (hX : 1 ≤ X) (hcoeff : coeff 1 = 1) :
    ∃ s : ℂ, selbergMollifier X coeff s ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hzero :
      Tendsto (fun sigma : ℝ => selbergMollifier X coeff (sigma : ℂ))
        atTop (nhds 0) := by
    simpa only [hnone] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (nhds 0))
  have honezero : (1 : ℂ) = 0 :=
    tendsto_nhds_unique
      (tendsto_selbergMollifier_real_atTop X coeff hX hcoeff) hzero
  norm_num at honezero

/-- The restriction of a finite mollifier to the complexified critical
line is entire. -/
theorem analyticOnNhd_selbergMollifier_vertical
    (X : ℕ) (coeff : ℕ → ℂ) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => selbergMollifier X coeff ((1 / 2 : ℂ) + I * z))
      Set.univ := by
  have haffine :
      AnalyticOnNhd ℂ (fun z : ℂ => (1 / 2 : ℂ) + I * z) Set.univ :=
    analyticOnNhd_const.add (analyticOnNhd_const.mul analyticOnNhd_id)
  simpa only [Function.comp_apply] using
    (analyticOnNhd_selbergMollifier X coeff).comp haffine
      (Set.mapsTo_univ _ _)

/-- On every nonempty interval of the critical-line parameter, a finite
mollifier with constant coefficient one is nonzero somewhere. -/
theorem exists_selbergMollifier_criticalLine_ne_zero_Ioo
    (X : ℕ) (coeff : ℕ → ℂ) (hX : 1 ≤ X) (hcoeff : coeff 1 = 1)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Set.Ioo a b,
      selbergMollifier X coeff ((1 / 2 : ℂ) + I * t) ≠ 0 := by
  by_contra hnone
  push Not at hnone
  let c : ℝ := (a + b) / 2
  let d : ℝ := (b - a) / 4
  let u : ℕ → ℂ := fun n => (c + d / (n + 1 : ℝ) : ℝ)
  have hd : 0 < d := by
    dsimp only [d]
    linarith
  have hu_tendsto : Tendsto u atTop (nhds (c : ℂ)) := by
    have hone :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ))
          atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hfrac :
        Tendsto (fun n : ℕ => d / (n + 1 : ℝ)) atTop (nhds 0) := by
      simpa only [div_eq_mul_inv, one_mul, mul_zero] using
        hone.const_mul d
    have hadd :
        Tendsto (fun n : ℕ => c + d / (n + 1 : ℝ))
          atTop (nhds c) := by
      simpa only [add_zero] using
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => c) atTop (nhds c)).add hfrac
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hadd
  have hu_mem : ∀ n : ℕ, u n ∈
      {z : ℂ | selbergMollifier X coeff ((1 / 2 : ℂ) + I * z) = 0} \
        {(c : ℂ)} := by
    intro n
    have hden : (0 : ℝ) < n + 1 := by positivity
    have hfracpos : 0 < d / (n + 1 : ℝ) := div_pos hd hden
    have hfracle : d / (n + 1 : ℝ) ≤ d := by
      apply (div_le_iff₀ hden).2
      have hdenone : (1 : ℝ) ≤ n + 1 := by
        exact_mod_cast Nat.succ_pos n
      nlinarith
    have huIoo : c + d / (n + 1 : ℝ) ∈ Set.Ioo a b := by
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
      ({z : ℂ |
          selbergMollifier X coeff ((1 / 2 : ℂ) + I * z) = 0} \
        {(c : ℂ)}) :=
    mem_closure_of_tendsto hu_tendsto
      (Filter.Eventually.of_forall hu_mem)
  have hident :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure
      (analyticOnNhd_selbergMollifier_vertical X coeff)
      isPreconnected_univ (Set.mem_univ (c : ℂ)) hclosure
  obtain ⟨s, hs⟩ :=
    exists_selbergMollifier_ne_zero X coeff hX hcoeff
  let z : ℂ := -I * (s - (1 / 2 : ℂ))
  have harg : (1 / 2 : ℂ) + I * z = s := by
    dsimp only [z]
    ring_nf
    simp
  exact hs (by simpa only [harg] using hident (Set.mem_univ z))

/-- The corresponding mollified Hardy function is nonzero somewhere in
every nonempty interval. -/
theorem exists_selbergMollifiedHardyZ_ne_zero_Ioo
    (X : ℕ) (coeff : ℕ → ℂ) (hX : 1 ≤ X) (hcoeff : coeff 1 = 1)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Set.Ioo a b, selbergMollifiedHardyZ X coeff t ≠ 0 := by
  obtain ⟨v, hv, hvHardy⟩ := exists_hardyZ_ne_zero_Ioo hab
  have hnear : ∀ᶠ t : ℝ in nhds v, hardyZ t ≠ 0 :=
    hardyZ_continuous.continuousAt.eventually_ne hvHardy
  rw [Metric.eventually_nhds_iff] at hnear
  obtain ⟨epsilon, hepsilon, hbound⟩ := hnear
  let r : ℝ :=
    min (epsilon / 2) (min ((v - a) / 2) ((b - v) / 2))
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min (half_pos hepsilon)
      (lt_min (half_pos (sub_pos.mpr hv.1))
        (half_pos (sub_pos.mpr hv.2)))
  obtain ⟨t, ht, htM⟩ :=
    exists_selbergMollifier_criticalLine_ne_zero_Ioo
      X coeff hX hcoeff (show v - r < v + r by linarith)
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
  rw [selbergMollifiedHardyZ]
  exact mul_ne_zero htHardy (mt Complex.normSq_eq_zero.mp htM)

end HardyTheorem
