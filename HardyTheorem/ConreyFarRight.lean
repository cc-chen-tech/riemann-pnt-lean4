import HardyTheorem.ConreyMollifierRectangleCount
import PrimeNumberTheorem.DigammaBounds

/-!
# Uniform far-right zero exclusion for Conrey's equation (35)

The real part of the digamma function tends to positive infinity uniformly
in the imaginary part as the real part tends to infinity.  This supplies a
uniform right edge on which `V1`, the normalized mollifier `B`, and their
product are nonzero.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace HardyTheorem

private theorem tendsto_harmonic_real_atTop :
    Tendsto (fun n : ℕ => (harmonic n : ℝ)) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsum := Real.tendsto_harmonic_sub_log.add_atTop hlog
  exact hsum.congr' (Eventually.of_forall (by intro n; ring))

private theorem digammaGaussTerm_re_nonneg {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    0 ≤ (PrimeNumberTheorem.digammaGaussTerm z n).re := by
  let k : ℝ := n + 1
  let u : ℝ := z.re + k
  let D : ℝ := u ^ 2 + z.im ^ 2
  have hformula : (PrimeNumberTheorem.digammaGaussTerm z n).re =
      1 / k - u / D := by
    simp [PrimeNumberTheorem.digammaGaussTerm, k, u, D, inv_re, normSq_apply]
    ring
  rw [hformula]
  have hk : 0 < k := by dsimp [k]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hku : k * u ≤ D := by
    have hkle : k ≤ u := by dsimp [u]; linarith
    have hsq : k * u ≤ u ^ 2 := by nlinarith
    dsimp [D]
    nlinarith [sq_nonneg z.im]
  have hquot : u / D ≤ 1 / k := by
    rw [div_le_div_iff₀ hD hk]
    simpa [mul_comm] using hku
  linarith

private theorem one_div_two_sum_range_eq_half_harmonic (N : ℕ) :
    (∑ n ∈ Finset.range N, (1 : ℝ) / (2 * (n + 1 : ℝ))) =
      (harmonic N : ℝ) / 2 := by
  have hsum : (∑ n ∈ Finset.range N, (1 : ℝ) / (n + 1 : ℝ)) =
      (harmonic N : ℝ) := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih, harmonic_succ]
        norm_num
  calc
    (∑ n ∈ Finset.range N, (1 : ℝ) / (2 * (n + 1 : ℝ))) =
        ∑ n ∈ Finset.range N, (1 / (n + 1 : ℝ)) * (1 / 2 : ℝ) := by
          apply Finset.sum_congr rfl
          intro n _hn
          field_simp
    _ = (∑ n ∈ Finset.range N, (1 / (n + 1 : ℝ))) * (1 / 2 : ℝ) := by
          rw [Finset.sum_mul]
    _ = (harmonic N : ℝ) / 2 := by rw [hsum]; ring

private theorem digammaGaussTerm_re_ge_half {z : ℂ} {n : ℕ}
    (h : (n + 1 : ℝ) ≤ z.re) :
    (1 : ℝ) / (2 * (n + 1 : ℝ)) ≤
      (PrimeNumberTheorem.digammaGaussTerm z n).re := by
  let k : ℝ := n + 1
  let u : ℝ := z.re + k
  let D : ℝ := u ^ 2 + z.im ^ 2
  have hformula : (PrimeNumberTheorem.digammaGaussTerm z n).re =
      1 / k - u / D := by
    simp [PrimeNumberTheorem.digammaGaussTerm, k, u, D, inv_re, normSq_apply]
    ring
  rw [hformula]
  have hk : 0 < k := by dsimp [k]; positivity
  have hz : 0 < z.re := hk.trans_le (by simpa [k] using h)
  have hu : 0 < u := by dsimp [u]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have h2ku : 2 * k * u ≤ D := by
    have h2k : 2 * k ≤ u := by dsimp [u, k]; linarith
    have hsq : 2 * k * u ≤ u ^ 2 := by nlinarith
    dsimp [D]
    nlinarith [sq_nonneg z.im]
  have hquot : u / D ≤ 1 / (2 * k) := by
    rw [div_le_div_iff₀ hD (mul_pos (by norm_num) hk)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using h2ku
  have hsplit : 1 / k = 2 * (1 / (2 * k)) := by field_simp
  change 1 / (2 * k) ≤ 1 / k - u / D
  linarith

/-- The real part of `digamma` tends to positive infinity uniformly in the
imaginary part when the real part tends to infinity. -/
theorem exists_digamma_re_ge_of_re_ge (M : ℝ) :
    ∃ A : ℝ, ∀ z : ℂ, A ≤ z.re → M ≤ (Complex.digamma z).re := by
  have hev : ∀ᶠ N : ℕ in atTop,
      2 * (M + Real.eulerMascheroniConstant + 1) < (harmonic N : ℝ) :=
    tendsto_harmonic_real_atTop.eventually (eventually_gt_atTop _)
  obtain ⟨N, hN⟩ := hev.exists
  refine ⟨(N : ℝ) + 1, ?_⟩
  intro z hz
  have hNz : (N : ℝ) ≤ z.re := by linarith
  have hz1 : 1 ≤ z.re := by
    have hNnonneg : (0 : ℝ) ≤ N := by positivity
    linarith
  have hzpos : 0 < z.re := zero_lt_one.trans_le hz1
  have hsummable := PrimeNumberTheorem.summable_digammaGaussTerm hzpos
  have hsummableRe := Complex.reCLM.summable hsummable
  have hpartial :
      (harmonic N : ℝ) / 2 ≤
        ∑ n ∈ Finset.range N,
          (PrimeNumberTheorem.digammaGaussTerm z n).re := by
    rw [← one_div_two_sum_range_eq_half_harmonic]
    apply Finset.sum_le_sum
    intro n hn
    apply digammaGaussTerm_re_ge_half
    have hnN : n + 1 ≤ N := Nat.succ_le_iff.mpr (Finset.mem_range.mp hn)
    calc
      (n + 1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
      _ ≤ z.re := hNz
  have hseries :
      (harmonic N : ℝ) / 2 ≤
        ∑' n : ℕ, (PrimeNumberTheorem.digammaGaussTerm z n).re :=
    hpartial.trans (hsummableRe.sum_le_tsum (Finset.range N)
      (fun n _hn => digammaGaussTerm_re_nonneg hzpos n))
  have hinv : (z⁻¹).re ≤ 1 := by
    calc
      (z⁻¹).re ≤ ‖z⁻¹‖ := re_le_norm _
      _ = ‖z‖⁻¹ := norm_inv z
      _ ≤ 1 := inv_le_one_of_one_le₀
        (hz1.trans (le_abs_self z.re |>.trans (abs_re_le_norm z)))
  calc
    M ≤ -Real.eulerMascheroniConstant - 1 + (harmonic N : ℝ) / 2 := by linarith
    _ ≤ -Real.eulerMascheroniConstant - (z⁻¹).re +
        ∑' n : ℕ, (PrimeNumberTheorem.digammaGaussTerm z n).re := by linarith
    _ = (Complex.digamma z).re := by
      rw [PrimeNumberTheorem.digamma_eq_gauss_series hzpos,
        Complex.add_re, Complex.sub_re, Complex.neg_re,
        Complex.ofReal_re, Complex.re_tsum hsummable]

private theorem logDeriv_GammaReal {s : ℂ}
    (hsGamma : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) :
    logDeriv Complex.Gammaℝ s =
      -Complex.log Real.pi / 2 + Complex.digamma (s / 2) / 2 := by
  let A : ℂ → ℂ := fun z => (Real.pi : ℂ) ^ (-z / 2)
  let G : ℂ → ℂ := fun z => Complex.Gamma (z / 2)
  have hbase : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hA : A s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)
  have hG : G s ≠ 0 := Complex.Gamma_ne_zero hsGamma
  have hAdiff : DifferentiableAt ℂ A s := by
    dsimp [A]
    exact (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl hbase)
  have hGdiff : DifferentiableAt ℂ G s := by
    exact (Complex.differentiableAt_Gamma (s / 2) hsGamma).comp s (by fun_prop)
  have hAlog : logDeriv A s = -Complex.log Real.pi / 2 := by
    simp only [A, logDeriv_apply]
    rw [Complex.deriv_const_cpow (by fun_prop :
      DifferentiableAt ℂ (fun z : ℂ => -z / 2) s)]
    rw [show deriv (fun z : ℂ => -z / 2) s = -(1 : ℂ) / 2 by
      exact ((hasDerivAt_neg s).div_const 2).deriv]
    field_simp
  have hGlog : logDeriv G s = Complex.digamma (s / 2) / 2 := by
    have hcomp := logDeriv_comp
      (f := Complex.Gamma) (g := fun z : ℂ => z / 2) (x := s)
      (Complex.differentiableAt_Gamma (s / 2) hsGamma) (by fun_prop)
    calc
      logDeriv G s = logDeriv Complex.Gamma (s / 2) *
          deriv (fun z : ℂ => z / 2) s := by
        dsimp only [G]
        convert hcomp using 1 <;> all_goals (first | rfl | funext z <;> rfl)
      _ = Complex.digamma (s / 2) * ((1 : ℂ) / 2) := by
        rw [← Complex.digamma_def]
        congr 1
        exact (hasDerivAt_id s).div_const 2 |>.deriv
      _ = Complex.digamma (s / 2) / 2 := by ring
  change logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) *
    Complex.Gamma (z / 2)) s = _
  change logDeriv (fun z : ℂ => A z * G z) s = _
  rw [logDeriv_mul s hA hG hAdiff hGdiff, hAlog, hGlog]

private theorem differentiableAt_GammaReal {s : ℂ}
    (hsGamma : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  change DifferentiableAt ℂ
    (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) s
  exact ((differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul
      ((Complex.differentiableAt_Gamma (s / 2) hsGamma).comp s (by fun_prop))

/-- Exact logarithmic derivative of Conrey's completed archimedean factor on
its full positive-real-part regular domain. -/
theorem logDeriv_conreyH_eq_of_re_pos_of_ne_one
    {s : ℂ} (hspos : 0 < s.re) (hsone : s ≠ 1) :
    deriv conreyH s / conreyH s =
      1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
        Complex.digamma (s / 2) / 2 := by
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hs1 : s - 1 ≠ 0 := by
    exact sub_ne_zero.mpr hsone
  have hsGamma : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hGamma : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos hspos
  have hlinear : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
    simp [logDeriv_apply]
  have hpoly :
      logDeriv (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1)) s =
        1 / s + 1 / (s - 1) := by
    rw [logDeriv_mul s (mul_ne_zero (by norm_num) hs0) hs1
        (by fun_prop) (by fun_prop),
      logDeriv_const_mul s (1 / 2 : ℂ) (by norm_num),
      logDeriv_id', hlinear]
  have houter :
      logDeriv (fun z : ℂ =>
        ((1 / 2 : ℂ) * z * (z - 1)) * Complex.Gammaℝ z) s =
        logDeriv (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1)) s +
          logDeriv Complex.Gammaℝ s :=
    logDeriv_mul s
      (mul_ne_zero (mul_ne_zero (by norm_num) hs0) hs1)
      hGamma (by fun_prop) (differentiableAt_GammaReal hsGamma)
  rw [← logDeriv_apply]
  change logDeriv (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1) *
    Complex.Gammaℝ z) s = _
  rw [houter, hpoly, logDeriv_GammaReal hsGamma]
  ring

/-- Backwards-compatible right-half-plane wrapper for the exact logarithmic
derivative formula. -/
theorem logDeriv_conreyH_eq {s : ℂ} (hs : 1 < s.re) :
    deriv conreyH s / conreyH s =
      1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
        Complex.digamma (s / 2) / 2 := by
  apply logDeriv_conreyH_eq_of_re_pos_of_ne_one (by linarith)
  intro hsone
  have hre := congrArg Complex.re hsone
  simp at hre
  linarith

/-- The logarithmic derivative `H'/H` tends to positive infinity uniformly
in the imaginary part on right half-planes. -/
theorem exists_logDeriv_conreyH_re_ge_of_re_ge (M : ℝ) :
    ∃ A : ℝ, ∀ s : ℂ, A ≤ s.re →
      M ≤ (deriv conreyH s / conreyH s).re := by
  obtain ⟨A, hA⟩ := exists_digamma_re_ge_of_re_ge
    (2 * M + Real.log Real.pi)
  refine ⟨max 2 (2 * A), ?_⟩
  intro s hs
  have hs2 : 2 ≤ s.re := le_trans (le_max_left _ _) hs
  have hhalf : A ≤ (s / 2).re := by
    norm_num
    have := le_trans (le_max_right 2 (2 * A)) hs
    linarith
  have hdig := hA (s / 2) hhalf
  have hfirst : 0 ≤ (1 / s).re := by
    rw [one_div, inv_re]
    exact div_nonneg (by linarith) (normSq_nonneg s)
  have hsecond : 0 ≤ (1 / (s - 1)).re := by
    rw [one_div, inv_re]
    simp only [sub_re, one_re]
    exact div_nonneg (by linarith) (normSq_nonneg (s - 1))
  have hlogTwo :
      (Complex.log (Real.pi : ℂ) / 2).re = Real.log Real.pi / 2 := by
    simp [div_re, normSq_apply, Complex.log_ofReal_re]
  have hdigTwo :
      (Complex.digamma (s / 2) / 2).re =
        (Complex.digamma (s / 2)).re / 2 := by
    simp [div_re, normSq_apply]
  rw [logDeriv_conreyH_eq (by linarith)]
  simp only [add_re, sub_re, hlogTwo, hdigTwo]
  linarith

/-- Conrey's degree-one factor has no zeros sufficiently far to the right,
with a boundary uniform in the imaginary part. -/
theorem exists_conreyDegreeOneV1_ne_zero_of_re_ge
    {g g0 g1 L : ℝ} (hg : g ≠ 0) :
    ∃ A : ℝ, ∀ s : ℂ, A ≤ s.re →
      conreyDegreeOneV1 g g0 g1 L s ≠ 0 := by
  let c : ℝ := g1 / L
  by_cases hc : c = 0
  · refine ⟨3, ?_⟩
    intro s hs
    have hzeta : riemannZeta s ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by linarith)
    have hlead : (g : ℂ) + I * (g0 : ℂ) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      exact hg hre
    unfold conreyDegreeOneV1
    rw [show g1 / L = 0 from hc]
    simpa using mul_ne_zero hlead hzeta
  · let C : ℝ := 2 * (riemannZeta 2).re
    obtain ⟨AH, hAH⟩ := exists_logDeriv_conreyH_re_ge_of_re_ge
      (C + |g / c| + 1)
    refine ⟨max 3 AH, ?_⟩
    intro s hs
    have hs3 : 3 ≤ s.re := le_trans (le_max_left _ _) hs
    have hsH : AH ≤ s.re := le_trans (le_max_right 3 AH) hs
    have hzeta : riemannZeta s ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by linarith)
    have hzetaNorm : ‖logDeriv riemannZeta s‖ ≤ C := by
      exact ZeroFreeRegion.norm_logDeriv_riemannZeta_le_two_mul_re_zeta_two_of_three_le_re
        s hs3
    have hzetaRe : -C ≤ (logDeriv riemannZeta s).re := by
      have hneg : -‖logDeriv riemannZeta s‖ ≤
          (logDeriv riemannZeta s).re := by
        calc
          -‖logDeriv riemannZeta s‖ ≤
              -|(logDeriv riemannZeta s).re| :=
            neg_le_neg (abs_re_le_norm _)
          _ ≤ (logDeriv riemannZeta s).re := neg_abs_le _
      linarith
    have hH := hAH s hsH
    let Q : ℂ :=
      ((g / c : ℝ) : ℂ) + I * ((g0 / c : ℝ) : ℂ) +
        logDeriv riemannZeta s + deriv conreyH s / conreyH s
    have hQre : 1 ≤ Q.re := by
      have hgdiv : -|g / c| ≤ g / c := neg_abs_le (g / c)
      dsimp [Q]
      simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
        zero_mul, one_mul, zero_add]
      linarith
    have hQ : Q ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    have hfactor :
        conreyDegreeOneV1 g g0 g1 L s =
          riemannZeta s * (c : ℂ) * Q := by
      unfold conreyDegreeOneV1
      change ((g : ℂ) + I * (g0 : ℂ)) * riemannZeta s +
          (c : ℂ) * (deriv riemannZeta s +
            (deriv conreyH s / conreyH s) * riemannZeta s) =
        riemannZeta s * (c : ℂ) * Q
      dsimp [Q]
      rw [logDeriv_apply]
      push_cast
      field_simp [hzeta, ofReal_ne_zero.mpr hc]
      ring
    rw [hfactor]
    exact mul_ne_zero (mul_ne_zero hzeta (ofReal_ne_zero.mpr hc)) hQ

/-- A normalized finite Conrey mollifier is uniformly nonzero on a sufficiently
far-right half-plane, not merely along the positive real axis. -/
theorem exists_conreyMollifier_ne_zero_of_re_ge
    {Y : ℕ} {P : ℝ → ℝ} (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (sigma0 : ℝ) :
    ∃ A : ℝ, ∀ s : ℂ, A ≤ s.re →
      conreyMollifier Y sigma0 P s ≠ 0 := by
  let coeff : ℕ → ℂ := conreyMollifierCoefficient Y sigma0 P
  let S : Finset ℕ := (Finset.Icc 1 Y).erase 1
  let R : ℝ → ℝ := fun sigma =>
    ∑ n ∈ S, ‖coeff n‖ * ((n : ℝ)⁻¹) ^ sigma
  have hterm : ∀ n ∈ S,
      Tendsto (fun sigma : ℝ =>
        ‖coeff n‖ * ((n : ℝ)⁻¹) ^ sigma) atTop (nhds 0) := by
    intro n hn
    have hnmem : n ∈ Finset.Icc 1 Y := Finset.mem_of_mem_erase hn
    have hn1 : n ≠ 1 := Finset.ne_of_mem_erase hn
    have hn2 : 2 ≤ n := by
      have := (Finset.mem_Icc.mp hnmem).1
      omega
    have hnreal : (1 : ℝ) < n := by exact_mod_cast hn2
    have hbasePos : 0 < ((n : ℝ)⁻¹) := inv_pos.mpr (by positivity)
    have hbaseLt : ((n : ℝ)⁻¹) < 1 :=
      (inv_lt_one₀ (by positivity)).2 hnreal
    have hpow : Tendsto (fun sigma : ℝ => ((n : ℝ)⁻¹) ^ sigma)
        atTop (nhds 0) :=
      tendsto_rpow_atTop_of_base_lt_one _ (by linarith) hbaseLt
    simpa only [mul_zero] using hpow.const_mul ‖coeff n‖
  have hR : Tendsto R atTop (nhds 0) := by
    dsimp only [R]
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum S hterm
  have hev : ∀ᶠ sigma : ℝ in atTop, R sigma < 1 :=
    hR.eventually (Iio_mem_nhds zero_lt_one)
  obtain ⟨A, hA⟩ := eventually_atTop.1 hev
  refine ⟨A, ?_⟩
  intro s hs
  have hOneMem : 1 ∈ Finset.Icc 1 Y :=
    Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hcoeff : coeff 1 = 1 := by
    exact conreyMollifierCoefficient_one hY hP1 sigma0
  have hsplit :
      conreyMollifier Y sigma0 P s - 1 =
        ∑ n ∈ S, coeff n * (1 / (n : ℂ) ^ s) := by
    unfold conreyMollifier selbergMollifier
    dsimp only [S]
    rw [← Finset.sum_erase_add _ _ hOneMem]
    dsimp only [coeff] at hcoeff ⊢
    rw [hcoeff]
    simp
  have hnorm : ‖conreyMollifier Y sigma0 P s - 1‖ ≤ R s.re := by
    rw [hsplit]
    calc
      ‖∑ n ∈ S, coeff n * (1 / (n : ℂ) ^ s)‖ ≤
          ∑ n ∈ S, ‖coeff n * (1 / (n : ℂ) ^ s)‖ :=
        norm_sum_le _ _
      _ = R s.re := by
        dsimp only [R]
        apply Finset.sum_congr rfl
        intro n hn
        have hnpos : 0 < n := by
          have hnmem : n ∈ Finset.Icc 1 Y :=
            Finset.mem_of_mem_erase hn
          exact (Finset.mem_Icc.mp hnmem).1
        rw [norm_mul, norm_div, norm_one,
          Complex.norm_natCast_cpow_of_pos hnpos]
        rw [one_div, Real.inv_rpow (Nat.cast_nonneg n) s.re]
  have hlt : ‖conreyMollifier Y sigma0 P s - 1‖ < 1 :=
    hnorm.trans_lt (hA s.re hs)
  intro hzero
  have hone : ‖conreyMollifier Y sigma0 P s - 1‖ = 1 := by
    rw [hzero]
    norm_num
  linarith

/-- The actual equation-(35) product is uniformly nonzero on a sufficiently
far-right half-plane. -/
theorem exists_conreyMollifiedDegreeOneV1_ne_zero_of_re_ge
    {g g0 g1 L sigma0 : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) :
    ∃ A : ℝ, ∀ s : ℂ, A ≤ s.re →
      conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P s ≠ 0 := by
  obtain ⟨AV, hV⟩ := exists_conreyDegreeOneV1_ne_zero_of_re_ge hg
  obtain ⟨AB, hB⟩ :=
    exists_conreyMollifier_ne_zero_of_re_ge hY hP1 sigma0
  refine ⟨max AV AB, ?_⟩
  intro s hs
  rw [conreyMollifiedDegreeOneV1_eq]
  exact mul_ne_zero
    (hV s (le_trans (le_max_left _ _) hs))
    (hB s (le_trans (le_max_right _ _) hs))

end HardyTheorem
