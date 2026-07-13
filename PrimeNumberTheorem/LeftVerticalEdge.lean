import PrimeNumberTheorem.LeftHorizontalEdge
import PrimeNumberTheorem.ExplicitFormulaRectangle

open Complex Filter Topology

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- On a vertical line through a negative odd integer, the cotangent factor
arising from digamma reflection is uniformly bounded, including at height
zero. -/
theorem norm_cot_odd_vertical_le_one (N : ℕ) (t : ℝ) :
    ‖Complex.cot (Real.pi *
      ((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) / 2 +
        Real.pi * (t : ℂ) * I / 2)‖ ≤ 1 := by
  let x : ℝ := -((N : ℝ) * Real.pi + Real.pi / 2)
  let y : ℝ := Real.pi * t / 2
  have harg :
      Real.pi * (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ)) / 2 +
          Real.pi * (t : ℂ) * I / 2 =
        (x : ℂ) + (y : ℂ) * I := by
    dsimp [x, y]
    push_cast
    ring
  have hsin : Real.sin x ^ 2 = 1 := by
    have hzero : Real.sin ((N : ℝ) * Real.pi) = 0 := by
      exact Real.sin_nat_mul_pi N
    have hunit := Real.sin_sq_add_cos_sq ((N : ℝ) * Real.pi)
    dsimp [x]
    rw [Real.sin_neg, Real.sin_add]
    simp only [Real.sin_pi_div_two, Real.cos_pi_div_two, mul_zero, mul_one, neg_sq]
    nlinarith
  have hcos : Real.cos x ^ 2 = 0 := by
    dsimp [x]
    rw [Real.cos_neg]
    simp [Real.cos_add, Real.sin_nat_mul_pi]
  have hsinSq :
      Complex.normSq (Complex.sin ((x : ℂ) + (y : ℂ) * I)) =
        Real.sin x ^ 2 + Real.sinh y ^ 2 := by
    rw [Complex.sin_add_mul_I]
    simp [Complex.normSq_apply, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sinh_ofReal_re,
      Complex.sinh_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im, sq]
    nlinarith [Real.sin_sq_add_cos_sq x, Real.cosh_sq_sub_sinh_sq y]
  have hcosSq :
      Complex.normSq (Complex.cos ((x : ℂ) + (y : ℂ) * I)) =
        Real.cos x ^ 2 + Real.sinh y ^ 2 := by
    rw [Complex.cos_add_mul_I]
    simp [Complex.normSq_apply, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sinh_ofReal_re,
      Complex.sinh_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im, sq]
    nlinarith [Real.sin_sq_add_cos_sq x, Real.cosh_sq_sub_sinh_sq y]
  rw [harg, Complex.cot_eq_cos_div_sin, norm_div]
  apply (sq_le_sq₀ (div_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one).1
  rw [div_pow, Complex.sq_norm, Complex.sq_norm, hsinSq, hcosSq, hsin, hcos]
  have hy : 0 ≤ Real.sinh y ^ 2 := sq_nonneg _
  have hden : 0 < 1 + Real.sinh y ^ 2 := by linarith
  rw [div_le_iff₀ hden]
  nlinarith

/-- The logarithmic derivative of Deligne's real Gamma factor at every point
where its ordinary Gamma factor is regular. -/
theorem logDeriv_Gammaℝ {s : ℂ} (hsGamma : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) :
    logDeriv Complex.Gammaℝ s =
      -Complex.log Real.pi / 2 + Complex.digamma (s / 2) / 2 := by
  let A : ℂ → ℂ := fun z => (Real.pi : ℂ) ^ (-z / 2)
  let G : ℂ → ℂ := fun z => Complex.Gamma (z / 2)
  have hbase : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hA : A s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)
  have hG : G s ≠ 0 := Complex.Gamma_ne_zero hsGamma
  have hAdiff : DifferentiableAt ℂ A s := by
    dsimp [A]
    exact (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow (Or.inl hbase)
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
          deriv (fun z : ℂ => z / 2) s := by simpa [G] using hcomp
      _ = Complex.digamma (s / 2) * ((1 : ℂ) / 2) := by
        rw [← Complex.digamma_def]
        congr 1
        exact (hasDerivAt_id s).div_const 2 |>.deriv
      _ = Complex.digamma (s / 2) / 2 := by ring
  change logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) *
    Complex.Gamma (z / 2)) s = _
  change logDeriv (fun z : ℂ => A z * G z) s = _
  rw [logDeriv_mul s hA hG hAdiff hGdiff, hAlog, hGlog]

/-- Away from the poles of its ordinary Gamma factor, `Gammaℝ` is
differentiable. -/
theorem differentiableAt_Gammaℝ_of_regular {s : ℂ}
    (hsGamma : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  change DifferentiableAt ℂ
    (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) s
  exact ((differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul
      ((Complex.differentiableAt_Gamma (s / 2) hsGamma).comp s (by fun_prop))

/-- At regular nonzero points, the zeta logarithmic derivative is the
completed-zeta logarithmic derivative minus the real Gamma-factor logarithmic
derivative. -/
theorem logDeriv_riemannZeta_eq_completed_sub_Gammaℝ {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hGamma : Complex.Gammaℝ s ≠ 0)
    (hGdiff : DifferentiableAt ℂ Complex.Gammaℝ s)
    (hzs : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s =
      logDeriv completedRiemannZeta s - logDeriv Complex.Gammaℝ s := by
  have heq : riemannZeta =ᶠ[nhds s]
      fun z : ℂ => completedRiemannZeta z * (Complex.Gammaℝ z)⁻¹ := by
    filter_upwards [eventually_ne_nhds hs0] with z hz
    rw [riemannZeta_def_of_ne_zero hz, div_eq_mul_inv]
  have hLambda : completedRiemannZeta s ≠ 0 := by
    intro hzero
    apply hzs
    rw [riemannZeta_def_of_ne_zero hs0, hzero, zero_div]
  have hGinv : (Complex.Gammaℝ s)⁻¹ ≠ 0 := inv_ne_zero hGamma
  have hInvLog :
      logDeriv (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) s =
        -logDeriv Complex.Gammaℝ s := by
    change logDeriv ((fun z : ℂ => z⁻¹) ∘ Complex.Gammaℝ) s = _
    rw [logDeriv_comp (differentiableAt_inv hGamma) hGdiff, logDeriv_inv]
    rw [logDeriv_apply]
    ring
  have hlogeq :
      logDeriv riemannZeta s =
        logDeriv (fun z : ℂ =>
          completedRiemannZeta z * (Complex.Gammaℝ z)⁻¹) s := by
    simp only [logDeriv_apply]
    rw [heq.deriv_eq]
    congr 1
    exact heq.self_of_nhds
  rw [hlogeq, logDeriv_mul s hLambda hGinv
    (differentiableAt_completedZeta hs0 hs1)
    Complex.differentiable_Gammaℝ_inv.differentiableAt, hInvLog]
  ring

/-- Logarithmic-derivative form of the completed zeta functional equation.
Unlike the traditional `Gamma * cos` split, this identity remains regular at
negative odd real points. -/
theorem logDeriv_riemannZeta_eq_completed_reflection {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hGamma : Complex.Gammaℝ s ≠ 0)
    (hGamma1 : Complex.Gammaℝ (1 - s) ≠ 0)
    (hGdiff : DifferentiableAt ℂ Complex.Gammaℝ s)
    (hGdiff1 : DifferentiableAt ℂ Complex.Gammaℝ (1 - s))
    (hzs : riemannZeta s ≠ 0) (hz1s : riemannZeta (1 - s) ≠ 0) :
    logDeriv riemannZeta s =
      -logDeriv riemannZeta (1 - s) -
        logDeriv Complex.Gammaℝ (1 - s) - logDeriv Complex.Gammaℝ s := by
  have h1s0 : 1 - s ≠ 0 := by
    intro h
    apply hs1
    linear_combination -h
  have h1s1 : 1 - s ≠ 1 := by
    intro h
    apply hs0
    linear_combination -h
  have hFEfun : (fun z : ℂ => completedRiemannZeta (1 - z)) =
      completedRiemannZeta := by
    funext z
    exact completedRiemannZeta_one_sub z
  have hLambdaLog :
      logDeriv completedRiemannZeta s =
        -logDeriv completedRiemannZeta (1 - s) := by
    have hcomp := logDeriv_comp
      (f := completedRiemannZeta) (g := fun z : ℂ => 1 - z) (x := s)
      (differentiableAt_completedZeta h1s0 h1s1) (by fun_prop)
    calc
      logDeriv completedRiemannZeta s =
          logDeriv (fun z : ℂ => completedRiemannZeta (1 - z)) s := by
            rw [hFEfun]
      _ = logDeriv completedRiemannZeta (1 - s) *
          deriv (fun z : ℂ => 1 - z) s := by simpa using hcomp
      _ = -logDeriv completedRiemannZeta (1 - s) := by
        have hderiv : deriv (fun z : ℂ => 1 - z) s = -1 := by
          convert ((hasDerivAt_const s 1).sub (hasDerivAt_id s)).deriv using 1
          all_goals simp
        rw [hderiv]
        ring
  have hslog := logDeriv_riemannZeta_eq_completed_sub_Gammaℝ
    hs0 hs1 hGamma hGdiff hzs
  have h1slog := logDeriv_riemannZeta_eq_completed_sub_Gammaℝ
    h1s0 h1s1 hGamma1 hGdiff1 hz1s
  rw [hslog, h1slog, hLambdaLog]
  ring

/-- The completed functional equation expanded into digamma terms.  This is
the regular replacement for the traditional Gamma/cosine decomposition on a
left vertical line. -/
theorem neg_logDeriv_riemannZeta_eq_right_shift_add_digamma {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hsGamma : ∀ n : ℕ, s / 2 ≠ -(n : ℂ))
    (h1sGamma : ∀ n : ℕ, (1 - s) / 2 ≠ -(n : ℂ))
    (hzs : riemannZeta s ≠ 0) (hz1s : riemannZeta (1 - s) ≠ 0) :
    -logDeriv riemannZeta s =
      logDeriv riemannZeta (1 - s) - Complex.log Real.pi +
        Complex.digamma ((1 - s) / 2) / 2 + Complex.digamma (s / 2) / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hGamma : Complex.Gammaℝ s ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hpi))
      (Complex.Gamma_ne_zero hsGamma)
  have hGamma1 : Complex.Gammaℝ (1 - s) ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hpi))
      (Complex.Gamma_ne_zero h1sGamma)
  have hreflect := logDeriv_riemannZeta_eq_completed_reflection
    hs0 hs1 hGamma hGamma1
      (differentiableAt_Gammaℝ_of_regular hsGamma)
      (differentiableAt_Gammaℝ_of_regular h1sGamma) hzs hz1s
  rw [hreflect, logDeriv_Gammaℝ hsGamma, logDeriv_Gammaℝ h1sGamma]
  ring

/-- On every vertical line halfway between consecutive trivial zeros, the
zeta logarithmic derivative is an Euler-product term plus two right-half-plane
digamma terms and a uniformly bounded cotangent correction.  The identity is
valid at height zero. -/
theorem neg_logDeriv_riemannZeta_odd_vertical_eq (N : ℕ) (t : ℝ) :
    let s : ℂ := ((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I
    (-logDeriv riemannZeta s) =
      logDeriv riemannZeta (1 - s) - Complex.log Real.pi +
        Complex.digamma ((1 - s) / 2) / 2 +
        Complex.digamma (1 - s / 2) / 2 -
        ((Real.pi : ℂ) * Complex.cot (Real.pi * s / 2)) / 2 := by
  let s : ℂ := ((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I
  change (-logDeriv riemannZeta s) =
    logDeriv riemannZeta (1 - s) - Complex.log Real.pi +
      Complex.digamma ((1 - s) / 2) / 2 +
      Complex.digamma (1 - s / 2) / 2 -
      ((Real.pi : ℂ) * Complex.cot (Real.pi * s / 2)) / 2
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hsGamma : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
    intro n hn
    have hre := congrArg Complex.re hn
    simp [s] at hre
    have heqR : (2 * (n : ℝ)) = 2 * (N : ℝ) + 1 := by linarith
    have hparity : 2 * n = 2 * N + 1 := by exact_mod_cast heqR
    omega
  have h1sGamma : ∀ n : ℕ, (1 - s) / 2 ≠ -(n : ℂ) := by
    intro n hn
    have hre := congrArg Complex.re hn
    simp [s] at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have htrivial : ∀ n : ℕ, s ≠ -2 * ((n : ℂ) + 1) := by
    intro n hn
    have hre := congrArg Complex.re hn
    simp [s] at hre
    have heqR : 2 * (N : ℝ) + 1 = 2 * ((n : ℝ) + 1) := by linarith
    have hparity : 2 * N + 1 = 2 * (n + 1) := by exact_mod_cast heqR
    omega
  have hzs : riemannZeta s ≠ 0 :=
    PrimeNumberTheorem.riemannZeta_ne_zero_of_re_le_zero
      (by simp [s]; have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N; linarith) htrivial
  have hz1s : riemannZeta (1 - s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re
      (by simp [s]; have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N; linarith)
  have hbase := neg_logDeriv_riemannZeta_eq_right_shift_add_digamma
    hs0 hs1 hsGamma h1sGamma hzs hz1s
  have hhalf1Gamma : ∀ n : ℕ, 1 - s / 2 ≠ -(n : ℂ) := by
    intro n hn
    have hre := congrArg Complex.re hn
    simp [s] at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hsin : Complex.sin (Real.pi * (s / 2)) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    have hre := congrArg Complex.re hk
    simp [s] at hre
    have heq : (-(2 * (N : ℝ) + 1) / 2 : ℝ) = (k : ℝ) := by
      nlinarith [Real.pi_pos]
    have hparity : (2 * k : ℤ) = -(2 * (N : ℤ) + 1) := by
      exact_mod_cast (by linarith : 2 * (k : ℝ) = -(2 * (N : ℝ) + 1))
    omega
  have hreflect := digamma_eq_one_sub_sub_pi_mul_cot_of_regular
    hsGamma hhalf1Gamma hsin
  rw [hbase, hreflect]
  ring

/-- Quantitative logarithmic bound for the zeta logarithmic derivative on a
vertical line halfway between consecutive trivial zeros. -/
theorem norm_neg_logDeriv_riemannZeta_odd_vertical_le (N : ℕ) (t : ℝ) :
    let s : ℂ := ((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I
    ‖-logDeriv riemannZeta s‖ ≤
      vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
        (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
          Real.log (‖(1 - s) / 2‖ + 1)) +
        (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
          Real.log (‖1 - s / 2‖ + 1)) + Real.pi := by
  let s : ℂ := ((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I
  change ‖-logDeriv riemannZeta s‖ ≤
    vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
      (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
        Real.log (‖(1 - s) / 2‖ + 1)) +
      (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
        Real.log (‖1 - s / 2‖ + 1)) + Real.pi
  have heq := neg_logDeriv_riemannZeta_odd_vertical_eq N t
  change (-logDeriv riemannZeta s) = _ at heq
  have hEuler0 := norm_neg_logDeriv_riemannZeta_le_vonMangoldtLSeriesNorm
    (show (0 : ℝ) < 1 by norm_num)
    (show 1 + (1 : ℝ) ≤ 2 * (N : ℝ) + 2 by
      have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith) (t := -t)
  have hshift :
      (((2 * (N : ℝ) + 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) = 1 - s := by
    apply Complex.ext <;> simp [s]
    ring
  rw [hshift, norm_neg] at hEuler0
  have hD1 := PrimeNumberTheorem.norm_digamma_le_log
    (z := (1 - s) / 2) (by
      simp [s]
      have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith)
  have hD2 := PrimeNumberTheorem.norm_digamma_le_log
    (z := 1 - s / 2) (by
      simp [s]
      have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith)
  have hD1div :
      ‖Complex.digamma ((1 - s) / 2) / 2‖ ≤
        ‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
          Real.log (‖(1 - s) / 2‖ + 1) := by
    calc
      _ ≤ ‖Complex.digamma ((1 - s) / 2)‖ := by
        rw [norm_div]
        norm_num
      _ ≤ _ := hD1
  have hD2div :
      ‖Complex.digamma (1 - s / 2) / 2‖ ≤
        ‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
          Real.log (‖1 - s / 2‖ + 1) := by
    calc
      _ ≤ ‖Complex.digamma (1 - s / 2)‖ := by
        rw [norm_div]
        norm_num
      _ ≤ _ := hD2
  have hcot0 := norm_cot_odd_vertical_le_one N t
  have hcot : ‖Complex.cot (Real.pi * s / 2)‖ ≤ 1 := by
    convert hcot0 using 1
    dsimp [s]
    ring
  have hcotTerm :
      ‖((Real.pi : ℂ) * Complex.cot (Real.pi * s / 2)) / 2‖ ≤ Real.pi := by
    rw [norm_div, norm_mul]
    norm_num [abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos, hcot, norm_nonneg (Complex.cot (Real.pi * s / 2))]
  have htri (a b c d e : ℂ) :
      ‖a - b + c + d - e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
    calc
      _ ≤ ‖a - b + c + d‖ + ‖e‖ := norm_sub_le _ _
      _ ≤ (‖a - b + c‖ + ‖d‖) + ‖e‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((‖a - b‖ + ‖c‖) + ‖d‖) + ‖e‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ (((‖a‖ + ‖b‖) + ‖c‖) + ‖d‖) + ‖e‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = _ := by ring
  rw [heq]
  exact (htri _ _ _ _ _).trans (by gcongr)

/-- Uniform logarithmic-derivative bound on a finite segment of a negative-odd
vertical line. -/
theorem norm_neg_logDeriv_riemannZeta_odd_vertical_le_of_abs_le
    {N : ℕ} {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) :
    let s : ℂ := ((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I
    ‖-logDeriv riemannZeta s‖ ≤
      vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
        2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
          Real.log (2 * (N : ℝ) + T + 4)) + Real.pi := by
  let s : ℂ := ((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I
  let z₁ : ℂ := (1 - s) / 2
  let z₂ : ℂ := 1 - s / 2
  change ‖-logDeriv riemannZeta s‖ ≤
    vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
      2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
        Real.log (2 * (N : ℝ) + T + 4)) + Real.pi
  have hbase := norm_neg_logDeriv_riemannZeta_odd_vertical_le N t
  change ‖-logDeriv riemannZeta s‖ ≤
    vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
      (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 + Real.log (‖z₁‖ + 1)) +
      (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 + Real.log (‖z₂‖ + 1)) +
      Real.pi at hbase
  have hz₁re : z₁.re = (N : ℝ) + 1 := by simp [z₁, s]; ring
  have hz₁im : z₁.im = -t / 2 := by simp [z₁, s]
  have hz₂re : z₂.re = (N : ℝ) + 3 / 2 := by simp [z₂, s]; ring
  have hz₂im : z₂.im = -t / 2 := by simp [z₂, s]; ring
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hz₁norm : ‖z₁‖ + 1 ≤ 2 * (N : ℝ) + T + 4 := by
    calc
      ‖z₁‖ + 1 ≤ (|z₁.re| + |z₁.im|) + 1 :=
        add_le_add (Complex.norm_le_abs_re_add_abs_im z₁) le_rfl
      _ = ((N : ℝ) + 1) + |t| / 2 + 1 := by
        rw [hz₁re, hz₁im, abs_of_nonneg (by linarith), abs_div, abs_neg]
        norm_num
      _ ≤ 2 * (N : ℝ) + T + 4 := by nlinarith [abs_nonneg t]
  have hz₂norm : ‖z₂‖ + 1 ≤ 2 * (N : ℝ) + T + 4 := by
    calc
      ‖z₂‖ + 1 ≤ (|z₂.re| + |z₂.im|) + 1 :=
        add_le_add (Complex.norm_le_abs_re_add_abs_im z₂) le_rfl
      _ = ((N : ℝ) + 3 / 2) + |t| / 2 + 1 := by
        rw [hz₂re, hz₂im, abs_of_nonneg (by linarith), abs_div, abs_neg]
        norm_num
      _ ≤ 2 * (N : ℝ) + T + 4 := by nlinarith [abs_nonneg t]
  have hMpos : 0 < 2 * (N : ℝ) + T + 4 := by linarith
  have hlog₁ : Real.log (‖z₁‖ + 1) ≤ Real.log (2 * (N : ℝ) + T + 4) :=
    Real.log_le_log (by positivity) hz₁norm
  have hlog₂ : Real.log (‖z₂‖ + 1) ≤ Real.log (2 * (N : ℝ) + T + 4) :=
    Real.log_le_log (by positivity) hz₂norm
  exact hbase.trans (by linarith)

/-- Uniform pointwise bound for the first-order explicit-formula integrand on
a finite negative-odd vertical segment. -/
theorem norm_explicitFormulaIntegrand_odd_vertical_le
    {x T t : ℝ} {N : ℕ} (hx : 1 < x) (hT : 0 ≤ T) (ht : |t| ≤ T) :
    ‖explicitFormulaIntegrand x
      (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      (vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
        2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
          Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
        x ^ (-(2 * (N : ℝ) + 1)) := by
  let s : ℂ := ((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I
  let Q : ℝ := vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
    2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
      Real.log (2 * (N : ℝ) + T + 4)) + Real.pi
  change ‖explicitFormulaIntegrand x s‖ ≤ Q * x ^ (-(2 * (N : ℝ) + 1))
  have hlog := norm_neg_logDeriv_riemannZeta_odd_vertical_le_of_abs_le
    (N := N) hT ht
  change ‖-logDeriv riemannZeta s‖ ≤ Q at hlog
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hpow : ‖(x : ℂ) ^ s‖ = x ^ (-(2 * (N : ℝ) + 1)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    simp [s]
  have hline : 1 ≤ ‖s‖ := by
    have hre : 2 * (N : ℝ) + 1 ≤ |s.re| := by
      simp [s]
      have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      rw [abs_of_nonpos (by linarith)]
      linarith
    have habs := Complex.abs_re_le_norm s
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hQ : 0 ≤ Q := by
    have hseries : 0 ≤ vonMangoldtLSeriesNorm 1 :=
      tsum_nonneg fun n => norm_nonneg _
    have hM : 1 ≤ 2 * (N : ℝ) + T + 4 := by
      have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    have hlogM : 0 ≤ Real.log (2 * (N : ℝ) + T + 4) := Real.log_nonneg hM
    dsimp [Q]
    positivity
  simp only [explicitFormulaIntegrand]
  rw [norm_div, norm_mul, hpow]
  have hnum : 0 ≤ Q * x ^ (-(2 * (N : ℝ) + 1)) :=
    mul_nonneg hQ (Real.rpow_nonneg hxpos.le _)
  calc
    ‖-logDeriv riemannZeta s‖ * x ^ (-(2 * (N : ℝ) + 1)) / ‖s‖ ≤
        (Q * x ^ (-(2 * (N : ℝ) + 1))) / ‖s‖ := by
      gcongr
    _ ≤ Q * x ^ (-(2 * (N : ℝ) + 1)) :=
      div_le_self hnum hline

/-- The explicit-formula integrand is genuinely integrable on every finite
segment of a negative odd vertical line. -/
theorem intervalIntegrable_explicitFormulaIntegrand_odd_vertical
    {x T : ℝ} {N : ℕ} (hx : 1 < x) :
    IntervalIntegrable
      (fun t : ℝ => explicitFormulaIntegrand x
        (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I))
      MeasureTheory.volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  intro t _ht
  let s : ℂ := ((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have htrivial : ∀ n : ℕ, s ≠ -2 * ((n : ℂ) + 1) := by
    intro n hn
    have hre := congrArg Complex.re hn
    simp [s] at hre
    have heqR : 2 * (N : ℝ) + 1 = 2 * ((n : ℝ) + 1) := by linarith
    have hparity : 2 * N + 1 = 2 * (n + 1) := by exact_mod_cast heqR
    omega
  have hzeta : riemannZeta s ≠ 0 :=
    PrimeNumberTheorem.riemannZeta_ne_zero_of_re_le_zero
      (by simp [s]; have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N; linarith)
      htrivial
  have han : ContinuousAt (explicitFormulaIntegrand x) s :=
    (analyticAt_explicitFormulaIntegrand_of_ne_zero_of_ne_one_of_zeta_ne_zero
      (zero_lt_one.trans hx) hs0 hs1 hzeta).continuousAt
  have hmap : ContinuousAt
      (fun r : ℝ => ((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (r : ℂ) * I) t := by
    fun_prop
  change ContinuousWithinAt
    (explicitFormulaIntegrand x ∘ fun r : ℝ =>
      (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (r : ℂ) * I)) _ t
  exact (ContinuousAt.comp
    (f := fun r : ℝ => (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (r : ℂ) * I))
    (x := t) (g := explicitFormulaIntegrand x) han hmap).continuousWithinAt

/-- Explicit finite-height bound for the complete moving left vertical edge. -/
theorem norm_integral_explicitFormulaIntegrand_odd_vertical_le
    {x T : ℝ} {N : ℕ} (hx : 1 < x) (hT : 0 ≤ T) :
    IntervalIntegrable
        (fun t : ℝ => explicitFormulaIntegrand x
          (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I))
        MeasureTheory.volume (-T) T ∧
      ‖∫ t : ℝ in (-T)..T,
          explicitFormulaIntegrand x
            (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        ((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
          2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
            Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
          x ^ (-(2 * (N : ℝ) + 1))) * (2 * T) := by
  refine ⟨intervalIntegrable_explicitFormulaIntegrand_odd_vertical hx, ?_⟩
  let C : ℝ := (vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
    2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
      Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
      x ^ (-(2 * (N : ℝ) + 1))
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ => explicitFormulaIntegrand x
      (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I))
    (a := -T) (b := T) (C := C) (fun t ht => by
      rw [Set.uIoc_of_le (by linarith)] at ht
      have habs : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      exact norm_explicitFormulaIntegrand_odd_vertical_le hx hT habs)
  change _ ≤ C * (2 * T)
  convert hbound using 1
  rw [abs_of_nonneg (by linarith : 0 ≤ T - -T)]
  ring

/-- If the vertical height grows at most linearly with the number of enclosed
trivial zeros, the complete moving left vertical edge tends to zero. -/
theorem tendsto_integral_explicitFormulaIntegrand_odd_vertical_atTop
    {x : ℝ} (hx : 1 < x) {K : ℕ} {T : ℕ → ℝ}
    (hT0 : ∀ n, 0 ≤ T n)
    (hTupper : ∀ n, T n ≤ (n : ℝ) + K + 1) :
    Tendsto
      (fun n : ℕ => ∫ t : ℝ in (-(T n))..(T n),
        explicitFormulaIntegrand x
          (((-(2 * (n : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I))
      atTop (nhds 0) := by
  let A : ℝ := vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
    2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3) + Real.pi
  let D : ℝ := A + 2 * (K : ℝ) + 16
  let q : ℝ := x ^ (-2 : ℝ)
  let C : ℝ := 2 * ((K : ℝ) + 1) * D * x ^ (-1 : ℝ)
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hA : 0 ≤ A := by
    have hseries : 0 ≤ vonMangoldtLSeriesNorm 1 :=
      tsum_nonneg fun n => norm_nonneg _
    dsimp [A]
    positivity
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg hx (by norm_num)
  have hxsplit (n : ℕ) :
      x ^ (-(2 * (n : ℝ) + 1)) = x ^ (-1 : ℝ) * q ^ n := by
    rw [show -(2 * (n : ℝ) + 1) = (-1 : ℝ) + (-2 : ℝ) * (n : ℝ) by ring,
      Real.rpow_add hxpos, Real.rpow_mul_natCast hxpos.le]
  have hpoly : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * q ^ n)
      atTop (nhds 0) := by
    have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 hq0 hq1
    have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 hq0 hq1
    have h0 := tendsto_pow_const_mul_const_pow_of_lt_one 0 hq0 hq1
    have hsum := (h2.add (h1.const_mul 2)).add h0
    convert hsum using 1
    · funext n
      norm_num
      ring
    · ring
  have hupper : Tendsto
      (fun n : ℕ => C * (((n : ℝ) + 1) ^ 2 * q ^ n))
      atTop (nhds 0) := by simpa using hpoly.const_mul C
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simp only [sub_zero]
  apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) _ hupper
  filter_upwards with n
  let M : ℝ := 2 * (n : ℝ) + T n + 4
  let Q : ℝ := vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
    2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 + Real.log M) + Real.pi
  have hmain := (norm_integral_explicitFormulaIntegrand_odd_vertical_le
    (N := n) hx (hT0 n)).2
  change _ ≤ (Q * x ^ (-(2 * (n : ℝ) + 1))) * (2 * T n) at hmain
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hK : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  have hMpos : 0 < M := by dsimp [M]; linarith [hT0 n]
  have hMupper : M ≤ 3 * (n : ℝ) + (K : ℝ) + 5 := by
    dsimp [M]
    linarith [hTupper n]
  have hlogM : Real.log M ≤ M := Real.log_le_self hMpos.le
  have hQupper : Q ≤ D * ((n : ℝ) + 1) := by
    dsimp [Q, D, A]
    nlinarith
  have hQ : 0 ≤ Q := by
    have hseries : 0 ≤ vonMangoldtLSeriesNorm 1 :=
      tsum_nonneg fun m => norm_nonneg _
    have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg (by
      dsimp [M]
      linarith [hT0 n])
    dsimp [Q]
    positivity
  have hTfactor : 2 * T n ≤ 2 * ((K : ℝ) + 1) * ((n : ℝ) + 1) := by
    nlinarith [hTupper n]
  have hpow0 : 0 ≤ x ^ (-(2 * (n : ℝ) + 1)) :=
    Real.rpow_nonneg hxpos.le _
  have hTtwo : 0 ≤ 2 * T n := mul_nonneg (by norm_num) (hT0 n)
  calc
    _ ≤ (Q * x ^ (-(2 * (n : ℝ) + 1))) * (2 * T n) := hmain
    _ ≤ (D * ((n : ℝ) + 1) * x ^ (-(2 * (n : ℝ) + 1))) *
        (2 * ((K : ℝ) + 1) * ((n : ℝ) + 1)) := by
      gcongr
    _ = C * (((n : ℝ) + 1) ^ 2 * q ^ n) := by
      rw [hxsplit]
      dsimp [C]
      ring

/-- Good contour heights can be chosen with linear growth.  The upper bound is
needed because exponential decay in the moving left edge must dominate the
length of the vertical segment. -/
theorem exists_linearlyControlled_goodHeight_gt_one :
    ∃ (K : ℕ) (T : ℕ → ℝ), StrictMono T ∧ Tendsto T atTop atTop ∧
      ∀ n, ((n + K : ℕ) : ℝ) < T n ∧
        T n < ((n + K : ℕ) : ℝ) + 1 ∧
        1 < T n ∧ ExplicitFormulaAux.goodHeight (T n) := by
  classical
  let T : ℕ → ℝ := fun n => Classical.choose
    (ExplicitFormulaAux.exists_goodHeight_Ioo ((n + 2 : ℕ) : ℝ))
  have hT (n : ℕ) :
      ((n + 2 : ℕ) : ℝ) < T n ∧
        T n < ((n + 2 : ℕ) : ℝ) + 1 ∧
        ExplicitFormulaAux.goodHeight (T n) := by
    exact Classical.choose_spec
      (ExplicitFormulaAux.exists_goodHeight_Ioo ((n + 2 : ℕ) : ℝ))
  have hmono : StrictMono T := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hn := (hT n).2.1
    have hnext := (hT (n + 1)).1
    norm_num [Nat.cast_add, Nat.cast_one] at hn hnext
    linarith
  have htend : Tendsto T atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (Nat.ceil b)] with n hn
    have hbceil : b ≤ (Nat.ceil b : ℝ) := Nat.le_ceil b
    have hceiln : (Nat.ceil b : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnshift : (n : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show n ≤ n + 2 by omega)
    exact le_trans hbceil (le_trans hceiln (hnshift.trans (hT n).1.le))
  refine ⟨2, T, hmono, htend, ?_⟩
  intro n
  have htwo : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ n + 2 by omega)
  exact ⟨(hT n).1, (hT n).2.1,
    lt_trans (lt_of_lt_of_le one_lt_two htwo) (hT n).1, (hT n).2.2⟩

end ExplicitFormulaResidues
end PrimeNumberTheorem
