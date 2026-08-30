import HardyTheorem.ConreyFarRight

/-!
# Digamma height estimate on Conrey's moving right edge

Gauss' convergent series is split at `ceil ‖z‖`.  The finite reciprocal
block, reciprocal-square tail, harmonic/log comparison, and elementary
archimedean terms are bounded separately.  This supplies the quantitative
height main term for `H'/H`; it does not assert the global right-vertical
integral or Conrey's two-fifths theorem.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem

private theorem abs_harmonic_ceil_sub_log_le_two
    {x t : ℝ} (ht : 2 ≤ t) (hxlow : t / 2 ≤ x) (hxhigh : x ≤ t) :
    |(harmonic ⌈x⌉₊ : ℝ) - Real.log t| ≤ 2 := by
  let N : ℕ := ⌈x⌉₊
  have ht0 : 0 < t := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le (by linarith : 0 < t / 2) hxlow
  have hNpos : 0 < N := Nat.ceil_pos.mpr hx0
  have hxN : x ≤ (N : ℝ) := by exact Nat.le_ceil x
  have hNlt : (N : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
  have hNtwoT : (N : ℝ) ≤ 2 * t := by linarith
  have hlogTwo : Real.log 2 ≤ 1 :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  have hlogNtwoT : Real.log (N : ℝ) ≤ Real.log (2 * t) := by
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) hNtwoT
  have hlogMul : Real.log (2 * t) = Real.log 2 + Real.log t := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht0.ne']
  have hupper : (harmonic N : ℝ) - Real.log t ≤ 2 := by
    have hharm := harmonic_le_one_add_log N
    rw [hlogMul] at hlogNtwoT
    linarith
  have htHalfN1 : t / 2 ≤ (N + 1 : ℕ) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hlogLow : Real.log (t / 2) ≤ Real.log (N + 1 : ℕ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact htHalfN1
  have hlogDiv : Real.log (t / 2) = Real.log t - Real.log 2 := by
    rw [Real.log_div ht0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  have hlower : -2 ≤ (harmonic N : ℝ) - Real.log t := by
    have hharm := log_add_one_le_harmonic N
    rw [hlogDiv] at hlogLow
    linarith
  exact abs_le.mpr ⟨hlower, hupper⟩

private theorem norm_digammaGauss_tail_le_one
    {z : ℂ} (hz : 0 < z.re) {N : ℕ} (hN : 0 < N)
    (hzN : ‖z‖ ≤ (N : ℝ)) :
    ‖∑' n : ℕ, PrimeNumberTheorem.digammaGaussTerm z (n + N)‖ ≤ 1 := by
  have hsNorm := PrimeNumberTheorem.summable_norm_digammaGaussTerm hz
  have hsTail : Summable
      (fun n : ℕ => ‖PrimeNumberTheorem.digammaGaussTerm z (n + N)‖) :=
    (summable_nat_add_iff N).mpr hsNorm
  have hp : Summable (fun n : ℕ => 1 / (N + n + 1 : ℝ) ^ 2) := by
    have h := summable_pow_div_add (1 : ℝ) 2 (N + 1) one_lt_two
    apply h.congr
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    congr 2
    push_cast
    ring
  have hpMul : Summable
      (fun n : ℕ => ‖z‖ * (1 / (N + n + 1 : ℝ) ^ 2)) := hp.mul_left ‖z‖
  have hratio : ‖z‖ / (N : ℝ) ≤ 1 :=
    (div_le_one (Nat.cast_pos.mpr hN)).mpr hzN
  calc
    ‖∑' n : ℕ, PrimeNumberTheorem.digammaGaussTerm z (n + N)‖ ≤
        ∑' n : ℕ, ‖PrimeNumberTheorem.digammaGaussTerm z (n + N)‖ :=
      norm_tsum_le_tsum_norm hsTail
    _ ≤ ∑' n : ℕ, ‖z‖ * (1 / (N + n + 1 : ℝ) ^ 2) := by
      apply Summable.tsum_le_tsum _ hsTail hpMul
      intro n
      have h := PrimeNumberTheorem.norm_digammaGaussTerm_le_norm_div_sq hz (n + N)
      simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc,
        div_eq_mul_inv] using h
    _ = ‖z‖ * (∑' n : ℕ, 1 / (N + n + 1 : ℝ) ^ 2) := tsum_mul_left
    _ ≤ ‖z‖ * (1 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (PrimeNumberTheorem.tsum_one_div_nat_add_sq_le hN) (norm_nonneg z)
    _ = ‖z‖ / (N : ℝ) := by ring
    _ ≤ 1 := hratio

private theorem norm_sum_inv_shift_le_three
    {z : ℂ} {t : ℝ} (ht : 2 ≤ t) (hzim : z.im = t / 2)
    {N : ℕ} (hNlt : (N : ℝ) < ‖z‖ + 1) (hzupper : ‖z‖ ≤ t) :
    ‖∑ n ∈ Finset.range N, (z + (n + 1 : ℕ))⁻¹‖ ≤ 3 := by
  have ht0 : 0 < t := by linarith
  have hterm : ∀ n : ℕ, ‖(z + (n + 1 : ℕ))⁻¹‖ ≤ 2 / t := by
    intro n
    have him : t / 2 ≤ ‖z + (n + 1 : ℕ)‖ := by
      calc
        t / 2 = |(z + (n + 1 : ℕ)).im| := by
          simp [hzim]
          rw [abs_of_nonneg (by linarith : 0 ≤ t / 2)]
        _ ≤ ‖z + (n + 1 : ℕ)‖ := Complex.abs_im_le_norm _
    have hden : 0 < ‖z + (n + 1 : ℕ)‖ := by
      linarith
    rw [norm_inv]
    calc
      ‖z + (n + 1 : ℕ)‖⁻¹ ≤ (t / 2)⁻¹ :=
        inv_anti₀ (by positivity) him
      _ = 2 / t := by field_simp [ht0.ne']
  calc
    ‖∑ n ∈ Finset.range N, (z + (n + 1 : ℕ))⁻¹‖ ≤
        ∑ n ∈ Finset.range N, ‖(z + (n + 1 : ℕ))⁻¹‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range N, (2 / t) :=
      Finset.sum_le_sum fun n _hn => hterm n
    _ = (N : ℝ) * (2 / t) := by simp
    _ ≤ 3 := by
      rw [show (N : ℝ) * (2 / t) = ((N : ℝ) * 2) / t by ring,
        div_le_iff₀ ht0]
      nlinarith

/-- On `2 ≤ t` and `1 < sigma ≤ t`, the digamma function at
`(sigma + i*t)/2` differs from its height main term by an absolute constant. -/
theorem norm_digamma_halfLine_sub_log_le_nine
    {sigma t : ℝ} (ht : 2 ≤ t) (hsigma : 1 < sigma)
    (hst : sigma ≤ t) :
    ‖Complex.digamma (((sigma : ℂ) + I * t) / 2) - Real.log t‖ ≤ 9 := by
  let z : ℂ := ((sigma : ℂ) + I * t) / 2
  let N : ℕ := ⌈‖z‖⌉₊
  have ht0 : 0 < t := by linarith
  have hsigma0 : 0 < sigma := by linarith
  have hzre : 0 < z.re := by
    dsimp [z]
    norm_num
    linarith
  have hzim : z.im = t / 2 := by
    dsimp [z]
    simp
  have hznormLow : t / 2 ≤ ‖z‖ := by
    calc
      t / 2 = |z.im| := by rw [hzim, abs_of_nonneg (by linarith : 0 ≤ t / 2)]
      _ ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hznormUpper : ‖z‖ ≤ t := by
    apply (sq_le_sq₀ (norm_nonneg z) ht0.le).mp
    rw [Complex.sq_norm]
    have hsquares : sigma ^ 2 ≤ t ^ 2 :=
      (sq_le_sq₀ hsigma0.le ht0.le).mpr hst
    dsimp [z]
    simp [Complex.normSq_apply]
    nlinarith
  have hznormOne : 1 ≤ ‖z‖ := by linarith
  have hNpos : 0 < N := Nat.ceil_pos.mpr (zero_lt_one.trans_le hznormOne)
  have hzN : ‖z‖ ≤ (N : ℝ) := by exact Nat.le_ceil ‖z‖
  have hNlt : (N : ℝ) < ‖z‖ + 1 := Nat.ceil_lt_add_one (norm_nonneg z)
  have hharmAbs : |(harmonic N : ℝ) - Real.log t| ≤ 2 :=
    abs_harmonic_ceil_sub_log_le_two ht hznormLow hznormUpper
  have hharmNorm :
      ‖((harmonic N : ℝ) : ℂ) - (Real.log t : ℂ)‖ ≤ 2 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hharmAbs
  have hinv : ‖z⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hznormOne
  have hfiniteInv :
      ‖∑ n ∈ Finset.range N, (z + (n + 1 : ℕ))⁻¹‖ ≤ 3 :=
    norm_sum_inv_shift_le_three ht hzim hNlt hznormUpper
  have htail :
      ‖∑' n : ℕ, PrimeNumberTheorem.digammaGaussTerm z (n + N)‖ ≤ 1 :=
    norm_digammaGauss_tail_le_one hzre hNpos hzN
  have hgamma : ‖(Real.eulerMascheroniConstant : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.one_half_lt_eulerMascheroniConstant.trans' (by norm_num))]
    exact Real.eulerMascheroniConstant_lt_two_thirds.le.trans (by norm_num)
  have hsum :=
    (PrimeNumberTheorem.summable_digammaGaussTerm hzre).sum_add_tsum_nat_add N
  have hfiniteGauss :
      (∑ n ∈ Finset.range N, PrimeNumberTheorem.digammaGaussTerm z n) =
        ((harmonic N : ℝ) : ℂ) -
          ∑ n ∈ Finset.range N, (z + (n + 1 : ℕ))⁻¹ := by
    simp only [PrimeNumberTheorem.digammaGaussTerm, Finset.sum_sub_distrib]
    congr 1
    simp [harmonic]
  have hdecomp :
      Complex.digamma z - Real.log t =
        -(Real.eulerMascheroniConstant : ℂ) - z⁻¹ +
          (((harmonic N : ℝ) : ℂ) - Real.log t) -
          (∑ n ∈ Finset.range N, (z + (n + 1 : ℕ))⁻¹) +
          ∑' n : ℕ, PrimeNumberTheorem.digammaGaussTerm z (n + N) := by
    rw [PrimeNumberTheorem.digamma_eq_gauss_series hzre]
    rw [← hsum, hfiniteGauss]
    ring
  change ‖Complex.digamma z - Real.log t‖ ≤ 9
  rw [hdecomp]
  calc
    ‖-(Real.eulerMascheroniConstant : ℂ) - z⁻¹ +
          (((harmonic N : ℝ) : ℂ) - Real.log t) -
          (∑ n ∈ Finset.range N, (z + (n + 1 : ℕ))⁻¹) +
          ∑' n : ℕ, PrimeNumberTheorem.digammaGaussTerm z (n + N)‖ ≤
        ‖-(Real.eulerMascheroniConstant : ℂ) - z⁻¹ +
          (((harmonic N : ℝ) : ℂ) - Real.log t) -
          (∑ n ∈ Finset.range N, (z + (n + 1 : ℕ))⁻¹)‖ +
          ‖∑' n : ℕ, PrimeNumberTheorem.digammaGaussTerm z (n + N)‖ :=
      norm_add_le _ _
    _ ≤ (‖-(Real.eulerMascheroniConstant : ℂ) - z⁻¹ +
          (((harmonic N : ℝ) : ℂ) - Real.log t)‖ +
          ‖∑ n ∈ Finset.range N, (z + (n + 1 : ℕ))⁻¹‖) + 1 :=
      add_le_add (norm_sub_le _ _) htail
    _ ≤ ((‖-(Real.eulerMascheroniConstant : ℂ) - z⁻¹‖ +
          ‖((harmonic N : ℝ) : ℂ) - Real.log t‖) + 3) + 1 :=
      add_le_add (add_le_add (norm_add_le _ _) hfiniteInv) le_rfl
    _ ≤ (((‖(Real.eulerMascheroniConstant : ℂ)‖ + ‖z⁻¹‖) + 2) + 3) + 1 := by
      apply add_le_add _ le_rfl
      apply add_le_add _ le_rfl
      exact add_le_add
        (by simpa using norm_sub_le (-(Real.eulerMascheroniConstant : ℂ)) z⁻¹)
        hharmNorm
    _ ≤ 9 := by
      linarith [hgamma, hinv]

/-- The exact completed archimedean logarithmic derivative differs from
`(1/2) log(t/(2*pi))` by at most eight on the target height range. -/
theorem norm_logDeriv_conreyH_sub_half_log_t_div_two_pi_le
    {sigma t : ℝ} (ht : 2 ≤ t) (hsigma : 1 < sigma)
    (hst : sigma ≤ t) :
    ‖deriv conreyH ((sigma : ℂ) + I * t) /
          conreyH ((sigma : ℂ) + I * t) -
        ((Real.log (t / (2 * Real.pi)) / 2 : ℝ) : ℂ)‖ ≤ 8 := by
  let s : ℂ := (sigma : ℂ) + I * t
  have ht0 : 0 < t := by linarith
  have hsre : 1 < s.re := by dsimp [s]; simp; exact hsigma
  have hsim : s.im = t := by dsimp [s]; simp
  have hlogPi : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
    (Complex.ofReal_log Real.pi_pos.le).symm
  have hlogTwoPi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  have hlogDiv :
      Real.log (t / (2 * Real.pi)) = Real.log t - Real.log (2 * Real.pi) := by
    rw [Real.log_div ht0.ne' (mul_ne_zero (by norm_num) Real.pi_ne_zero)]
  have hdecomp :
      deriv conreyH s / conreyH s -
          ((Real.log (t / (2 * Real.pi)) / 2 : ℝ) : ℂ) =
        1 / s + 1 / (s - 1) +
          (Complex.digamma (s / 2) - Real.log t) / 2 +
          ((Real.log 2 / 2 : ℝ) : ℂ) := by
    rw [logDeriv_conreyH_eq hsre, hlogPi, hlogDiv, hlogTwoPi]
    push_cast
    ring
  have hsNorm : t ≤ ‖s‖ := by
    calc
      t = |s.im| := by rw [hsim, abs_of_pos ht0]
      _ ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hsOneNorm : t ≤ ‖s - 1‖ := by
    calc
      t = |(s - 1).im| := by simp [hsim, abs_of_pos ht0]
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
  have hInv : ‖1 / s‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one]
    exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (ht.trans hsNorm))
  have hInvOne : ‖1 / (s - 1)‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one]
    exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (ht.trans hsOneNorm))
  have hDig := norm_digamma_halfLine_sub_log_le_nine ht hsigma hst
  have hDigHalf : ‖(Complex.digamma (s / 2) - Real.log t) / 2‖ ≤ 9 / 2 := by
    have hsHalf : s / 2 = ((sigma : ℂ) + I * t) / 2 := by rfl
    rw [norm_div]
    norm_num only [norm_ofNat]
    rw [hsHalf]
    exact div_le_div_of_nonneg_right hDig (by norm_num)
  have hlogTwo : ‖((Real.log 2 / 2 : ℝ) : ℂ)‖ ≤ 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.log_pos (by norm_num)).le (by norm_num))]
    have hlogTwoLe : Real.log 2 ≤ 1 :=
      Real.log_two_lt_d9.le.trans (by norm_num)
    linarith
  change ‖deriv conreyH s / conreyH s -
      ((Real.log (t / (2 * Real.pi)) / 2 : ℝ) : ℂ)‖ ≤ 8
  rw [hdecomp]
  calc
    ‖1 / s + 1 / (s - 1) +
        (Complex.digamma (s / 2) - Real.log t) / 2 +
        ((Real.log 2 / 2 : ℝ) : ℂ)‖ ≤
      ‖1 / s‖ + ‖1 / (s - 1)‖ +
        ‖(Complex.digamma (s / 2) - Real.log t) / 2‖ +
        ‖((Real.log 2 / 2 : ℝ) : ℂ)‖ := by
      calc
        _ ≤ ‖1 / s + 1 / (s - 1) +
              (Complex.digamma (s / 2) - Real.log t) / 2‖ +
              ‖((Real.log 2 / 2 : ℝ) : ℂ)‖ := norm_add_le _ _
        _ ≤ (‖1 / s + 1 / (s - 1)‖ +
              ‖(Complex.digamma (s / 2) - Real.log t) / 2‖) +
              ‖((Real.log 2 / 2 : ℝ) : ℂ)‖ :=
          add_le_add (norm_add_le _ _) le_rfl
        _ ≤ ((‖1 / s‖ + ‖1 / (s - 1)‖) +
              ‖(Complex.digamma (s / 2) - Real.log t) / 2‖) +
              ‖((Real.log 2 / 2 : ℝ) : ℂ)‖ :=
          add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
        _ = _ := by ring
    _ ≤ 8 := by linarith

end HardyTheorem
