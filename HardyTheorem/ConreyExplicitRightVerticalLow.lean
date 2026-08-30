import HardyTheorem.ConreyExplicitRightVertical

/-!
# The low part and global integral on Conrey's explicit right vertical

The high part retains and integrates the height-dependent main term.  On the
short low part, a coarse digamma bound keeps `V1` close to `49/100`; combining
this with the finite mollifier gives direct two-sided norm bounds.  The final
theorem joins both ranges into the complete quantitative right-vertical input
for Conrey's equation (37).
-/

open Complex

namespace HardyTheorem

theorem log_le_div_hundred_of_ge_forty_thousand {L : ℝ} (hL : 40000 ≤ L) :
    Real.log L ≤ L / 100 := by
  have hLpos : 0 < L := by linarith
  have hraw := Real.log_le_rpow_div hLpos.le
    (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [← Real.sqrt_eq_rpow] at hraw
  have hsqrt0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hsqrtSq : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hLpos.le
  have hsqrtLe : Real.sqrt L ≤ L / 200 := by
    nlinarith [sq_nonneg (Real.sqrt L - 200)]
  norm_num at hraw
  linarith

theorem norm_logDeriv_conreyH_movingRight_low_le
    {L t : ℝ} (hL : 40000 ≤ L) (ht : 1 ≤ t)
    (htop : t ≤ 2 * Real.log L) :
    ‖deriv conreyH (((2 * Real.log L : ℝ) : ℂ) + I * t) /
        conreyH (((2 * Real.log L : ℝ) : ℂ) + I * t)‖ ≤
      6 + Real.log L := by
  have hLpos : 0 < L := by linarith
  have hlogSmall := log_le_div_hundred_of_ge_forty_thousand hL
  have he2lt : Real.exp 2 < 9 := by
    have he := Real.exp_one_lt_three
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [he2]
    nlinarith [Real.exp_pos 1]
  have hLexp2 : Real.exp 2 ≤ L := he2lt.le.trans (by linarith)
  have hlogL : 2 ≤ Real.log L := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (Real.exp_pos 2)) (Set.mem_Ioi.mpr hLpos) hLexp2
    simpa only [Real.log_exp] using hmono
  let s : ℂ := ((2 * Real.log L : ℝ) : ℂ) + I * t
  have hsre : 1 < s.re := by simp [s]; linarith
  have hsNormUpper : ‖s‖ ≤ 4 * Real.log L := by
    calc
      ‖s‖ ≤ ‖((2 * Real.log L : ℝ) : ℂ)‖ + ‖I * (t : ℂ)‖ := by
        simpa only [s] using
          norm_add_le (((2 * Real.log L : ℝ) : ℂ)) (I * (t : ℂ))
      _ = 2 * Real.log L + t := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : 0 ≤ 2 * Real.log L), norm_mul,
          norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : 0 ≤ t)]
      _ ≤ 4 * Real.log L := by linarith
  have hzre : 1 ≤ (s / 2).re := by simp [s]; linarith
  have hzNorm : ‖s / 2‖ ≤ 2 * Real.log L := by
    rw [norm_div]
    norm_num only [norm_ofNat]
    linarith
  have hzArg : ‖s / 2‖ + 1 ≤ L := by linarith
  have hlogArg : Real.log (‖s / 2‖ + 1) ≤ Real.log L := by
    exact Real.log_le_log (by positivity) hzArg
  have hEuler : ‖(Real.eulerMascheroniConstant : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.one_half_lt_eulerMascheroniConstant.trans' (by norm_num))]
    exact Real.eulerMascheroniConstant_lt_two_thirds.le.trans (by norm_num)
  have hDigRaw := PrimeNumberTheorem.norm_digamma_le_log (z := s / 2) hzre
  have hDig : ‖Complex.digamma (s / 2)‖ ≤ 4 + Real.log L := by
    linarith
  have hsNormLower : 1 ≤ ‖s‖ := by
    calc
      1 ≤ s.re := by linarith
      _ ≤ |s.re| := le_abs_self _
      _ ≤ ‖s‖ := Complex.abs_re_le_norm _
  have hsOneNormLower : 1 ≤ ‖s - 1‖ := by
    calc
      1 ≤ (s - 1).re := by simp [s]; linarith
      _ ≤ |(s - 1).re| := le_abs_self _
      _ ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
  have hInv : ‖1 / s‖ ≤ 1 := by
    rw [norm_div, norm_one]
    simpa only [div_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hsNormLower
  have hInvOne : ‖1 / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    simpa only [div_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hsOneNormLower
  have hlogPi : ‖Complex.log (Real.pi : ℂ) / 2‖ ≤ 1 := by
    have hpiExp : Real.pi ≤ Real.exp 2 := by
      have hpi := Real.pi_lt_d2
      have he := Real.exp_one_gt_d9
      have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      rw [he2]
      nlinarith
    have hlogPiLe : Real.log Real.pi ≤ 2 := by
      calc
        Real.log Real.pi ≤ Real.log (Real.exp 2) :=
          Real.log_le_log Real.pi_pos hpiExp
        _ = 2 := Real.log_exp 2
    have hlogPiEq : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
      (Complex.ofReal_log Real.pi_pos.le).symm
    rw [hlogPiEq, norm_div]
    norm_num only [norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    linarith
  have hDigHalf : ‖Complex.digamma (s / 2) / 2‖ ≤
      (4 + Real.log L) / 2 := by
    rw [norm_div]
    norm_num only [norm_ofNat]
    exact div_le_div_of_nonneg_right hDig (by norm_num)
  rw [logDeriv_conreyH_eq hsre]
  calc
    ‖1 / s + 1 / (s - 1) - Complex.log ↑Real.pi / 2 +
        Complex.digamma (s / 2) / 2‖ ≤
        ‖1 / s‖ + ‖1 / (s - 1)‖ + ‖Complex.log ↑Real.pi / 2‖ +
          ‖Complex.digamma (s / 2) / 2‖ := by
      calc
        _ ≤ ‖1 / s + 1 / (s - 1) - Complex.log ↑Real.pi / 2‖ +
            ‖Complex.digamma (s / 2) / 2‖ := norm_add_le _ _
        _ ≤ (‖1 / s + 1 / (s - 1)‖ + ‖Complex.log ↑Real.pi / 2‖) +
            ‖Complex.digamma (s / 2) / 2‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ ((‖1 / s‖ + ‖1 / (s - 1)‖) + ‖Complex.log ↑Real.pi / 2‖) +
            ‖Complex.digamma (s / 2) / 2‖ :=
          add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
        _ = _ := by ring
    _ ≤ 6 + Real.log L := by linarith

theorem norm_conreyExplicitV1_sub_const_low_le
    {L t : ℝ} (hL : 40000 ≤ L) (ht : 1 ≤ t)
    (htop : t ≤ 2 * Real.log L) :
    ‖conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L
        (((2 * Real.log L : ℝ) : ℂ) + I * t) - (49 / 100 : ℂ)‖ ≤
      1 / 50 := by
  have hLpos : 0 < L := by linarith
  have hlogSmall := log_le_div_hundred_of_ge_forty_thousand hL
  have he2lt : Real.exp 2 < 9 := by
    have he := Real.exp_one_lt_three
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [he2]
    nlinarith [Real.exp_pos 1]
  have hLexp2 : Real.exp 2 ≤ L := he2lt.le.trans (by linarith)
  have hlogL : 2 ≤ Real.log L := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (Real.exp_pos 2)) (Set.mem_Ioi.mpr hLpos) hLexp2
    simpa only [Real.log_exp] using hmono
  have hLexp1 : Real.exp 1 ≤ L :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hLexp2
  let s : ℂ := ((2 * Real.log L : ℝ) : ℂ) + I * t
  have hre : s.re = 2 * Real.log L := by simp [s]
  have hs2 : 2 ≤ s.re := by rw [hre]; linarith
  have hzetaTail : ‖riemannZeta s - 1‖ ≤ 3 / L :=
    norm_riemannZeta_movingRight_sub_one_le hLexp1 hre
  have hzetaNorm : ‖riemannZeta s‖ ≤ (5 / 3 : ℝ) :=
    (ZeroFreeRegion.norm_riemannZeta_le_re_zeta_two_of_two_le_re s hs2).trans
      ZeroFreeRegion.riemannZeta_two_re_le_five_thirds
  have hzetaDeriv : ‖deriv riemannZeta s‖ ≤ (5 / 3 : ℝ) := by
    have hraw :=
      ZeroFreeRegion.norm_deriv_riemannZeta_sigma_it_le_re_zeta_two_div_radius_of_two_add_radius_le
        (σ := 2 * Real.log L) (t := t) (R := 1) (by norm_num) (by linarith)
    rw [show s = ((2 * Real.log L : ℝ) : ℂ) + I * t by rfl]
    exact hraw.trans (by
      simpa using ZeroFreeRegion.riemannZeta_two_re_le_five_thirds)
  have hH : ‖deriv conreyH s / conreyH s‖ ≤ 6 + Real.log L := by
    simpa only [s] using
      norm_logDeriv_conreyH_movingRight_low_le hL ht htop
  have hcoeff : ‖(51 / 50 : ℂ) / (L : ℂ)‖ = 51 / (50 * L) := by
    rw [norm_div]
    norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLpos]
    ring
  rw [show (((2 * Real.log L : ℝ) : ℂ) + I * t) = s by rfl]
  unfold conreyDegreeOneV1
  simp only [Complex.ofReal_zero, mul_zero, add_zero]
  push_cast
  change ‖((49 / 100 : ℂ) * riemannZeta s +
      ((51 / 50 : ℂ) / (L : ℂ)) *
        (deriv riemannZeta s + (deriv conreyH s / conreyH s) * riemannZeta s)) -
      (49 / 100 : ℂ)‖ ≤ 1 / 50
  rw [show (49 / 100 : ℂ) * riemannZeta s +
        ((51 / 50 : ℂ) / (L : ℂ)) *
          (deriv riemannZeta s + (deriv conreyH s / conreyH s) * riemannZeta s) -
        (49 / 100 : ℂ) =
      (49 / 100 : ℂ) * (riemannZeta s - 1) +
        ((51 / 50 : ℂ) / (L : ℂ)) *
          (deriv riemannZeta s + (deriv conreyH s / conreyH s) * riemannZeta s) by ring]
  calc
    ‖(49 / 100 : ℂ) * (riemannZeta s - 1) +
        ((51 / 50 : ℂ) / (L : ℂ)) *
          (deriv riemannZeta s + (deriv conreyH s / conreyH s) * riemannZeta s)‖ ≤
      (49 / 100 : ℝ) * ‖riemannZeta s - 1‖ +
        (51 / (50 * L)) *
          (‖deriv riemannZeta s‖ +
            ‖deriv conreyH s / conreyH s‖ * ‖riemannZeta s‖) := by
      calc
        _ ≤ ‖(49 / 100 : ℂ) * (riemannZeta s - 1)‖ +
            ‖((51 / 50 : ℂ) / (L : ℂ)) *
              (deriv riemannZeta s +
                (deriv conreyH s / conreyH s) * riemannZeta s)‖ := norm_add_le _ _
        _ = (49 / 100 : ℝ) * ‖riemannZeta s - 1‖ +
            (51 / (50 * L)) *
              ‖deriv riemannZeta s +
                (deriv conreyH s / conreyH s) * riemannZeta s‖ := by
          rw [norm_mul, norm_mul, hcoeff]
          norm_num
        _ ≤ _ := by
          gcongr
          simpa only [norm_mul] using
            norm_add_le (deriv riemannZeta s)
              ((deriv conreyH s / conreyH s) * riemannZeta s)
    _ ≤ (49 / 100 : ℝ) * (3 / L) +
        (51 / (50 * L)) * ((5 / 3 : ℝ) + (6 + Real.log L) * (5 / 3)) := by
      gcongr
    _ ≤ 1 / 50 := by
      field_simp [hLpos.ne'] at hlogSmall ⊢
      nlinarith

theorem conreyExplicitRightVerticalProduct_low_norm_bounds
    {Y : ℕ} {sigma0 L t : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2)
    (hL : 40000 ≤ L) (ht : 1 ≤ t) (htop : t ≤ 2 * Real.log L) :
    (2 / 5 : ℝ) ≤ ‖conreyExplicitRightVerticalProduct Y sigma0 L t‖ ∧
      ‖conreyExplicitRightVerticalProduct Y sigma0 L t‖ ≤ 3 / 5 := by
  have hLpos : 0 < L := by linarith
  have he2lt : Real.exp 2 < 9 := by
    have he := Real.exp_one_lt_three
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [he2]
    nlinarith [Real.exp_pos 1]
  have hLexp2 : Real.exp 2 ≤ L := he2lt.le.trans (by linarith)
  have hLexp1 : Real.exp 1 ≤ L :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hLexp2
  let s : ℂ := ((2 * Real.log L : ℝ) : ℂ) + I * t
  let V : ℂ := conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L s
  let M : ℂ := conreyMollifier Y sigma0 conreyExplicitP s
  have hVerr : ‖V - (49 / 100 : ℂ)‖ ≤ 1 / 50 := by
    simpa only [V, s] using norm_conreyExplicitV1_sub_const_low_le hL ht htop
  have hVdiff := abs_norm_sub_norm_le V (49 / 100 : ℂ)
  have hVconst : ‖(49 / 100 : ℂ)‖ = (49 / 100 : ℝ) := by norm_num
  have hVlower : (47 / 100 : ℝ) ≤ ‖V‖ := by
    rw [hVconst] at hVdiff
    have hleft : (49 / 100 : ℝ) - ‖V‖ ≤ 1 / 50 :=
      (le_abs_self ((49 / 100 : ℝ) - ‖V‖)).trans
        (by simpa only [abs_sub_comm] using hVdiff.trans hVerr)
    linarith
  have hVupper : ‖V‖ ≤ (51 / 100 : ℝ) := by
    rw [hVconst] at hVdiff
    have hright : ‖V‖ - (49 / 100 : ℝ) ≤ 1 / 50 :=
      (le_abs_self (‖V‖ - (49 / 100 : ℝ))).trans (hVdiff.trans hVerr)
    linarith
  have hMerr : ‖M - 1‖ ≤ 3 / L := by
    dsimp [M, s]
    convert norm_conreyExplicitMollifier_movingRight_sub_one_le
      hY hsigma0 hLexp1 t using 1
    push_cast
    rfl
  have hMsmall : (3 / L : ℝ) ≤ 1 / 100 := by
    apply (div_le_iff₀ hLpos).mpr
    linarith
  have hMdiff := abs_norm_sub_norm_le M (1 : ℂ)
  have hMlower : (99 / 100 : ℝ) ≤ ‖M‖ := by
    have hleft : (1 : ℝ) - ‖M‖ ≤ 1 / 100 := by
      have : (1 : ℝ) - ‖M‖ ≤ 3 / L :=
        (le_abs_self ((1 : ℝ) - ‖M‖)).trans
          (by simpa only [norm_one, abs_sub_comm] using hMdiff.trans hMerr)
      exact this.trans hMsmall
    linarith
  have hMupper : ‖M‖ ≤ (101 / 100 : ℝ) := by
    have hright : ‖M‖ - (1 : ℝ) ≤ 1 / 100 := by
      have : ‖M‖ - (1 : ℝ) ≤ 3 / L :=
        (le_abs_self (‖M‖ - (1 : ℝ))).trans
          (by simpa only [norm_one] using hMdiff.trans hMerr)
      exact this.trans hMsmall
    linarith
  change (2 / 5 : ℝ) ≤ ‖V * M‖ ∧ ‖V * M‖ ≤ 3 / 5
  rw [norm_mul]
  constructor
  · have hmul := mul_le_mul hVlower hMlower
      (by norm_num : (0 : ℝ) ≤ 99 / 100) (norm_nonneg V)
    nlinarith
  · have hmul := mul_le_mul hVupper hMupper (norm_nonneg M)
      (by norm_num : (0 : ℝ) ≤ 51 / 100)
    nlinarith

theorem abs_log_norm_conreyExplicitRightVerticalProduct_low_le_two
    {Y : ℕ} {sigma0 L t : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2)
    (hL : 40000 ≤ L) (ht : 1 ≤ t) (htop : t ≤ 2 * Real.log L) :
    |Real.log ‖conreyExplicitRightVerticalProduct Y sigma0 L t‖| ≤ 2 := by
  obtain ⟨hlower, hupper⟩ :=
    conreyExplicitRightVerticalProduct_low_norm_bounds
      hY hsigma0 hL ht htop
  have hthird : (1 / 3 : ℝ) ≤
      ‖conreyExplicitRightVerticalProduct Y sigma0 L t‖ := by linarith
  have hone : ‖conreyExplicitRightVerticalProduct Y sigma0 L t‖ ≤ (1 : ℝ) := by
    linarith
  have hlog := abs_log_le_three_mul_one_sub hthird hone
  nlinarith

theorem integral_abs_log_norm_conreyExplicitRightVerticalProduct_low_le
    {Y : ℕ} {sigma0 L : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2) (hL : 40000 ≤ L) :
    (∫ t in 1..2 * Real.log L,
      |Real.log ‖conreyExplicitRightVerticalProduct Y sigma0 L t‖|) ≤
        4 * Real.log L := by
  have hLpos : 0 < L := by linarith
  have he2lt : Real.exp 2 < 9 := by
    have he := Real.exp_one_lt_three
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [he2]
    nlinarith [Real.exp_pos 1]
  have hLexp2 : Real.exp 2 ≤ L := he2lt.le.trans (by linarith)
  have hlogL : 2 ≤ Real.log L := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (Real.exp_pos 2)) (Set.mem_Ioi.mpr hLpos) hLexp2
    simpa only [Real.log_exp] using hmono
  have hab : (1 : ℝ) ≤ 2 * Real.log L := by linarith
  let P : ℝ → ℂ := fun t => conreyExplicitRightVerticalProduct Y sigma0 L t
  let f : ℝ → ℝ := fun t => |Real.log ‖P t‖|
  have hPcont : Continuous P := by
    simpa only [P] using
      continuous_conreyExplicitRightVerticalProduct
        (Y := Y) (sigma0 := sigma0) hLexp2
  have hfcont : ContinuousOn f (Set.Icc 1 (2 * Real.log L)) := by
    intro t htmem
    have hbounds := conreyExplicitRightVerticalProduct_low_norm_bounds
      hY hsigma0 hL htmem.1 htmem.2
    have hPne : P t ≠ 0 := by
      intro hzero
      have hzero' : conreyExplicitRightVerticalProduct Y sigma0 L t = 0 := by
        simpa only [P] using hzero
      rw [hzero', norm_zero] at hbounds
      norm_num at hbounds
    have hnorm : ContinuousAt (fun u => ‖P u‖) t :=
      (continuous_norm.comp hPcont).continuousAt
    have hlog : ContinuousAt (fun u => Real.log ‖P u‖) t :=
      (Real.continuousAt_log (by simpa using hPne)).comp' hnorm
    exact (continuous_abs.continuousAt.comp' hlog).continuousWithinAt
  have hfint : IntervalIntegrable f MeasureTheory.volume 1 (2 * Real.log L) := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hab] using hfcont
  have hpoint : ∀ t ∈ Set.Icc 1 (2 * Real.log L), f t ≤ (2 : ℝ) := by
    intro t htmem
    simpa only [f, P] using
      abs_log_norm_conreyExplicitRightVerticalProduct_low_le_two
        hY hsigma0 hL htmem.1 htmem.2
  have hmono : (∫ t in 1..2 * Real.log L, f t) ≤
      ∫ _t in 1..2 * Real.log L, (2 : ℝ) :=
    intervalIntegral.integral_mono_on hab hfint intervalIntegrable_const hpoint
  calc
    (∫ t in 1..2 * Real.log L,
      |Real.log ‖conreyExplicitRightVerticalProduct Y sigma0 L t‖|) =
        ∫ t in 1..2 * Real.log L, f t := by rfl
    _ ≤ ∫ _t in 1..2 * Real.log L, (2 : ℝ) := hmono
    _ = (2 * Real.log L - 1) * 2 := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
    _ ≤ 4 * Real.log L := by linarith

theorem four_mul_log_le_exp_div_of_ge_forty_thousand
    {L : ℝ} (hL : 40000 ≤ L) :
    4 * Real.log L ≤ Real.exp L / L := by
  have hLpos : 0 < L := by linarith
  have hlogSmall := log_le_div_hundred_of_ge_forty_thousand hL
  have hehalf := Real.add_one_le_exp (L / 2)
  have hexpQuad : L ^ 2 / 25 ≤ Real.exp L := by
    rw [show L = L / 2 + L / 2 by ring, Real.exp_add]
    nlinarith [sq_nonneg (L / 2 - 1)]
  apply (le_div_iff₀ hLpos).mpr
  have hmul := mul_le_mul_of_nonneg_right hlogSmall hLpos.le
  nlinarith

theorem intervalIntegrable_abs_log_norm_conreyExplicitRightVerticalProduct_global
    {Y : ℕ} {sigma0 L : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2) (hL : 40000 ≤ L) :
    IntervalIntegrable
      (fun t : ℝ => |Real.log ‖conreyExplicitRightVerticalProduct Y sigma0 L t‖|)
      MeasureTheory.volume 1 (Real.exp L) := by
  have hLpos : 0 < L := by linarith
  have he2lt : Real.exp 2 < 9 := by
    have he := Real.exp_one_lt_three
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [he2]
    nlinarith [Real.exp_pos 1]
  have hLexp2 : Real.exp 2 ≤ L := he2lt.le.trans (by linarith)
  have hlogL : 2 ≤ Real.log L := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (Real.exp_pos 2)) (Set.mem_Ioi.mpr hLpos) hLexp2
    simpa only [Real.log_exp] using hmono
  have hab : 2 * Real.log L ≤ Real.exp L := by
    have hlogLleL : Real.log L ≤ L := by
      have := Real.add_one_le_exp (Real.log L)
      rw [Real.exp_log hLpos] at this
      linarith
    have hehalf := Real.add_one_le_exp (L / 2)
    have hexpLarge : 2 * L ≤ Real.exp L := by
      rw [show L = L / 2 + L / 2 by ring, Real.exp_add]
      nlinarith [sq_nonneg (L / 2 - 1)]
    linarith
  have honeexp : (1 : ℝ) ≤ Real.exp L := by
    have hexp := Real.exp_le_exp.mpr (show (0 : ℝ) ≤ L by linarith)
    simpa only [Real.exp_zero] using hexp
  let P : ℝ → ℂ := fun t => conreyExplicitRightVerticalProduct Y sigma0 L t
  have hPcont : Continuous P := by
    simpa only [P] using
      continuous_conreyExplicitRightVerticalProduct
        (Y := Y) (sigma0 := sigma0) hLexp2
  have hfcont : ContinuousOn (fun t : ℝ => |Real.log ‖P t‖|)
      (Set.Icc 1 (Real.exp L)) := by
    intro t htmem
    have hPne : P t ≠ 0 := by
      by_cases htlow : t ≤ 2 * Real.log L
      · have hbounds := conreyExplicitRightVerticalProduct_low_norm_bounds
          hY hsigma0 hL htmem.1 htlow
        intro hzero
        have hzero' : conreyExplicitRightVerticalProduct Y sigma0 L t = 0 := by
          simpa only [P] using hzero
        rw [hzero', norm_zero] at hbounds
        norm_num at hbounds
      · simpa only [P] using conreyExplicitRightVerticalProduct_ne_zero
          hY hsigma0 (by linarith : 600 ≤ L) (by linarith) htmem.2
    have hnorm : ContinuousAt (fun u => ‖P u‖) t :=
      (continuous_norm.comp hPcont).continuousAt
    have hlog : ContinuousAt (fun u => Real.log ‖P u‖) t :=
      (Real.continuousAt_log (by simpa using hPne)).comp' hnorm
    exact (continuous_abs.continuousAt.comp' hlog).continuousWithinAt
  apply ContinuousOn.intervalIntegrable
  simpa only [Set.uIcc_of_le honeexp] using hfcont

theorem integral_abs_log_norm_conreyExplicitRightVerticalProduct_global_le
    {Y : ℕ} {sigma0 L : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2) (hL : 40000 ≤ L) :
    (∫ t in 1..Real.exp L,
      |Real.log ‖conreyExplicitRightVerticalProduct Y sigma0 L t‖|) ≤
        507 * Real.exp L / L := by
  have hhigh := integral_abs_log_norm_conreyExplicitRightVerticalProduct_high_le
    hY hsigma0 (by linarith : 600 ≤ L)
  have hlow :=
    integral_abs_log_norm_conreyExplicitRightVerticalProduct_low_le
      hY hsigma0 hL
  have habsorb := four_mul_log_le_exp_div_of_ge_forty_thousand hL
  have hglobalInt :=
    intervalIntegrable_abs_log_norm_conreyExplicitRightVerticalProduct_global
      hY hsigma0 hL
  have hLpos : 0 < L := by linarith
  have he2lt : Real.exp 2 < 9 := by
    have he := Real.exp_one_lt_three
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [he2]
    nlinarith [Real.exp_pos 1]
  have hLexp2 : Real.exp 2 ≤ L := he2lt.le.trans (by linarith)
  have hlogL : 2 ≤ Real.log L := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (Real.exp_pos 2)) (Set.mem_Ioi.mpr hLpos) hLexp2
    simpa only [Real.log_exp] using hmono
  have ha1 : (1 : ℝ) ≤ 2 * Real.log L := by linarith
  have hab : 2 * Real.log L ≤ Real.exp L := by
    have hlogLleL : Real.log L ≤ L := by
      have := Real.add_one_le_exp (Real.log L)
      rw [Real.exp_log hLpos] at this
      linarith
    have hehalf := Real.add_one_le_exp (L / 2)
    have hexpLarge : 2 * L ≤ Real.exp L := by
      calc
        2 * L ≤ (L / 2 + 1) ^ 2 := by
          nlinarith [sq_nonneg (L / 2 - 1)]
        _ ≤ (Real.exp (L / 2)) ^ 2 := by
          nlinarith [Real.exp_pos (L / 2)]
        _ = Real.exp L := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
    linarith
  have honeexp : (1 : ℝ) ≤ Real.exp L := ha1.trans hab
  have hlowInt : IntervalIntegrable
      (fun t : ℝ => |Real.log ‖conreyExplicitRightVerticalProduct Y sigma0 L t‖|)
      MeasureTheory.volume 1 (2 * Real.log L) :=
    hglobalInt.mono_set (by
      rw [Set.uIcc_of_le ha1, Set.uIcc_of_le honeexp]
      exact Set.Icc_subset_Icc le_rfl hab)
  have hhighInt : IntervalIntegrable
      (fun t : ℝ => |Real.log ‖conreyExplicitRightVerticalProduct Y sigma0 L t‖|)
      MeasureTheory.volume (2 * Real.log L) (Real.exp L) :=
    hglobalInt.mono_set (by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le honeexp]
      exact Set.Icc_subset_Icc ha1 le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hlowInt hhighInt]
  calc
    (∫ t in 1..2 * Real.log L,
        |Real.log ‖conreyExplicitRightVerticalProduct Y sigma0 L t‖|) +
      ∫ t in 2 * Real.log L..Real.exp L,
        |Real.log ‖conreyExplicitRightVerticalProduct Y sigma0 L t‖| ≤
      Real.exp L / L + 506 * Real.exp L / L :=
        add_le_add (hlow.trans habsorb) hhigh
    _ = 507 * Real.exp L / L := by ring

end HardyTheorem
