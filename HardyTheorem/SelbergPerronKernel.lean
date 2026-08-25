import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

open Complex MeasureTheory Set Filter Asymptotics
open scoped Topology

namespace HardyTheorem

/-!
# The logarithmic Perron kernel from Mellin inversion

The continuous cutoff `log⁺(x⁻¹)` has Mellin transform `1 / s²` on `re s > 0`.
Mellin inversion therefore evaluates the full vertical Perron kernel exactly.  This formulation
also handles the boundary value `x = 1` without a half-weight ambiguity, since the logarithmic
weight vanishes there.
-/

noncomputable def perronLogCutoff (x : ℝ) : ℂ :=
  (Real.posLog x⁻¹ : ℂ)

theorem perronLogCutoff_eq_negLogIndicator_on_pos :
    EqOn perronLogCutoff
      (fun x : ℝ => -(Real.log x) •
        (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) x)
      (Ioi 0) := by
  intro x hx
  have hxpos : 0 < x := hx
  by_cases hx1 : x ≤ 1
  · have hxmem : x ∈ Ioc (0 : ℝ) 1 := ⟨hxpos, hx1⟩
    have hinvge : 1 ≤ |x⁻¹| := by
      rw [abs_of_pos (inv_pos.mpr hxpos)]
      exact (one_le_inv₀ hxpos).mpr hx1
    simp [perronLogCutoff, Real.posLog_eq_log hinvge,
      Real.log_inv, hxmem]
  · have hxgt : 1 < x := lt_of_not_ge hx1
    have hxnot : x ∉ Ioc (0 : ℝ) 1 := by
      intro h
      exact hx1 h.2
    have hinvle : |x⁻¹| ≤ 1 := by
      rw [abs_of_pos (inv_pos.mpr hxpos)]
      exact (inv_le_one₀ hxpos).mpr hxgt.le
    simp [perronLogCutoff, (Real.posLog_eq_zero_iff x⁻¹).mpr hinvle,
      hxnot]

theorem hasMellin_perronLogCutoff {s : ℂ} (hs : 0 < s.re) :
    HasMellin perronLogCutoff s (1 / s ^ 2) := by
  let g : ℝ → ℂ :=
    (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ))
  have hlocal : LocallyIntegrableOn g (Ioi (0 : ℝ)) :=
    ((locallyIntegrable_const (1 : ℂ)).indicator measurableSet_Ioc).locallyIntegrableOn _
  have hzero : g =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hxnot : x ∉ Ioc (0 : ℝ) 1 := by
      intro h
      exact (not_le_of_gt hx) h.2
    simp [g, hxnot]
  have htop :
      g =O[atTop] (fun x : ℝ => x ^ (-(s.re + 1))) := by
    exact (isBigO_zero _ _).congr' hzero.symm EventuallyEq.rfl
  have hbot :
      g =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    rw [isBigO_iff_isBigOWith]
    refine ⟨1, IsBigOWith.of_bound ?_⟩
    filter_upwards with x
    simp only [neg_zero, Real.rpow_zero, norm_one, one_mul]
    by_cases hxmem : x ∈ Ioc (0 : ℝ) 1
    · simp [g, hxmem]
    · simp [g, hxmem]
  have hd := mellin_hasDerivAt_of_isBigO_rpow
    (a := s.re + 1) (b := 0) hlocal htop (by linarith) hbot hs
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have heq : mellin g =ᶠ[𝓝 s] fun z : ℂ => z⁻¹ := by
    filter_upwards [hopen.eventually_mem hs] with z hz
    simpa [one_div] using (hasMellin_one_Ioc hz).2
  have hexplicit : HasDerivAt (mellin g) (-(s ^ 2)⁻¹) s :=
    (hasDerivAt_inv hs0).congr_of_eventuallyEq heq
  have hmellinLog :
      mellin (fun x : ℝ => Real.log x • g x) s = -(s ^ 2)⁻¹ :=
    hd.2.unique hexplicit
  have hnegconv :
      MellinConvergent (fun x : ℝ => -(Real.log x • g x)) s :=
    by
      simpa only [neg_smul, one_smul] using hd.1.const_smul (-1 : ℂ)
  have hfun : EqOn perronLogCutoff
      (fun x : ℝ => -(Real.log x • g x)) (Ioi 0) := by
    simpa only [g, neg_smul] using perronLogCutoff_eq_negLogIndicator_on_pos
  have hconv : MellinConvergent perronLogCutoff s := by
    rw [MellinConvergent] at hnegconv ⊢
    exact hnegconv.congr_fun
      (fun x hx => by rw [hfun hx]) measurableSet_Ioi
  refine ⟨hconv, ?_⟩
  have hmellinEq :
      mellin perronLogCutoff s =
        mellin (fun x : ℝ => -(Real.log x • g x)) s := by
    unfold mellin
    exact setIntegral_congr_fun measurableSet_Ioi fun x hx => by
      rw [hfun hx]
  rw [hmellinEq]
  have hneg :
      mellin (fun x : ℝ => -(Real.log x • g x)) s =
        -mellin (fun x : ℝ => Real.log x • g x) s := by
    simp only [mellin, smul_neg, integral_neg]
  rw [hneg, hmellinLog]
  simp [one_div]

theorem verticalIntegrable_inv_sq {sigma : ℝ} (hsigma : 0 < sigma) :
    VerticalIntegrable (fun s : ℂ => 1 / s ^ 2) sigma := by
  have hsigma0 : sigma ≠ 0 := hsigma.ne'
  have hbase : Integrable
      (fun t : ℝ => sigma⁻¹ ^ 2 * (1 + (sigma⁻¹ * t) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hsigma0)).const_mul
      (sigma⁻¹ ^ 2)
  let F : ℝ → ℂ := fun t => 1 / (((sigma : ℂ) + t * I) ^ 2)
  have hFcont : Continuous F := by
    apply continuous_iff_continuousAt.2
    intro t
    apply continuousAt_const.div₀
    · fun_prop
    · apply pow_ne_zero
      intro hz
      have hzre := congrArg Complex.re hz
      norm_num at hzre
      linarith
  have hnormInt : Integrable (fun t => ‖F t‖) := by
    apply hbase.congr
    filter_upwards with t
    have hnorm :
        ‖F t‖ = (sigma ^ 2 + t ^ 2)⁻¹ := by
      simp only [F]
      rw [one_div, norm_inv, norm_pow, Complex.sq_norm,
        Complex.normSq_apply]
      norm_num
      ring_nf
    have hscale :
        sigma⁻¹ ^ 2 * (1 + (sigma⁻¹ * t) ^ 2)⁻¹ =
          (sigma ^ 2 + t ^ 2)⁻¹ := by
      field_simp
    exact hscale.trans hnorm.symm
  unfold VerticalIntegrable
  exact (integrable_norm_iff hFcont.aestronglyMeasurable).mp hnormInt

theorem continuousAt_perronLogCutoff_of_pos {x : ℝ} (hx : 0 < x) :
    ContinuousAt perronLogCutoff x := by
  unfold perronLogCutoff
  exact Complex.continuous_ofReal.continuousAt.comp
    (Real.continuous_posLog.continuousAt.comp
      (continuousAt_id.inv₀ hx.ne'))

theorem mellinInv_inv_sq_eq_perronLogCutoff
    {sigma x : ℝ} (hsigma : 0 < sigma) (hx : 0 < x) :
    mellinInv sigma (fun s : ℂ => 1 / s ^ 2) x =
      perronLogCutoff x := by
  have hmellin : MellinConvergent perronLogCutoff (sigma : ℂ) :=
    (hasMellin_perronLogCutoff (s := (sigma : ℂ)) (by simpa using hsigma)).1
  have hverticalMellin : VerticalIntegrable (mellin perronLogCutoff) sigma := by
    unfold VerticalIntegrable
    apply (verticalIntegrable_inv_sq hsigma).congr
    filter_upwards with t
    have hre : 0 < (((sigma : ℂ) + t * I).re) := by simpa using hsigma
    exact (hasMellin_perronLogCutoff hre).2.symm
  have hinversion := mellinInv_mellin_eq sigma perronLogCutoff hx
    hmellin hverticalMellin (continuousAt_perronLogCutoff_of_pos hx)
  calc
    mellinInv sigma (fun s : ℂ => 1 / s ^ 2) x =
        mellinInv sigma (mellin perronLogCutoff) x := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      have hre : 0 < (((sigma : ℂ) + t * I).re) := by simpa using hsigma
      rw [(hasMellin_perronLogCutoff hre).2]
    _ = perronLogCutoff x := hinversion

theorem perronKernel_integral_eq
    {sigma x : ℝ} (hsigma : 0 < sigma) (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ, (x : ℂ) ^ (-((sigma : ℂ) + t * I)) *
          (1 / (((sigma : ℂ) + t * I) ^ 2)) =
      perronLogCutoff x := by
  simpa [mellinInv, smul_eq_mul] using
    (mellinInv_inv_sq_eq_perronLogCutoff hsigma hx)

/-- Ratio form of the logarithmic Perron kernel.  This is the exact shape obtained from
the term `Y^s / n^s` in a Dirichlet series. -/
theorem perronKernel_ratio_integral_eq
    {sigma Y n : ℝ} (hsigma : 0 < sigma) (hY : 0 < Y) (hn : 0 < n) :
    (1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ,
          ((Y : ℂ) ^ ((sigma : ℂ) + t * I) /
              (n : ℂ) ^ ((sigma : ℂ) + t * I)) *
            (1 / (((sigma : ℂ) + t * I) ^ 2)) =
      perronLogCutoff (n / Y) := by
  have hratio (t : ℝ) :
      ((n / Y : ℝ) : ℂ) ^ (-((sigma : ℂ) + t * I)) =
        (Y : ℂ) ^ ((sigma : ℂ) + t * I) /
          (n : ℂ) ^ ((sigma : ℂ) + t * I) := by
    rw [ofReal_div, Complex.div_cpow_ofReal_nonneg hn.le hY.le,
      Complex.cpow_neg, Complex.cpow_neg]
    field_simp [Complex.cpow_ne_zero_iff, hn.ne', hY.ne']
  rw [MeasureTheory.integral_congr_ae]
  · exact perronKernel_integral_eq hsigma (div_pos hn hY)
  · filter_upwards with t
    rw [hratio]

theorem perronLogCutoff_nat_div_eq_log {n Y : ℕ}
    (hn : 0 < n) (hY : 0 < Y) (hnY : n ≤ Y) :
    perronLogCutoff ((n : ℝ) / (Y : ℝ)) =
      (Real.log ((Y : ℝ) / (n : ℝ)) : ℂ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hratio : ((n : ℝ) / (Y : ℝ))⁻¹ = (Y : ℝ) / (n : ℝ) := by
    field_simp
  have hge : 1 ≤ |(Y : ℝ) / (n : ℝ)| := by
    rw [abs_of_pos (div_pos hYR hnR)]
    exact (one_le_div hnR).2 (by exact_mod_cast hnY)
  unfold perronLogCutoff
  rw [hratio, Real.posLog_eq_log hge]

theorem perronLogCutoff_nat_div_eq_zero {n Y : ℕ}
    (hn : 0 < n) (hY : 0 < Y) (hYn : Y ≤ n) :
    perronLogCutoff ((n : ℝ) / (Y : ℝ)) = 0 := by
  unfold perronLogCutoff
  norm_cast
  rw [Real.posLog_eq_zero_iff]
  have hxpos : 0 < (n : ℝ) / (Y : ℝ) := by positivity
  rw [abs_of_pos (inv_pos.mpr hxpos)]
  apply (inv_le_one₀ hxpos).2
  exact (one_le_div (by positivity)).2 (by exact_mod_cast hYn)

end HardyTheorem
