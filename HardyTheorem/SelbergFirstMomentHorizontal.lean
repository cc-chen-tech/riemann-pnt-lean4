import HardyTheorem.SelbergFirstMomentRightEdge
import HardyTheorem.FirstZetaApproximation

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators Interval

namespace HardyTheorem

/-!
# Horizontal sides of Selberg's first-moment rectangle

The horizontal estimate does not require the convexity bound for zeta.  The
uniform first Abel approximation at cutoff `4*T` gives `O(sqrt T)` throughout
`1/2 <= re(s) <= 2`.  The finite square-root-zeta mollifier contributes
`O(sqrt X)` per copy, leaving `O(X * sqrt T)` on either horizontal side.
-/

/-- The first Abel approximation gives a square-root bound uniformly on the
strip `1/2 <= sigma <= 2` and a dyadic height range. -/
theorem exists_norm_riemannZeta_half_two_strip_le_sqrt :
    ∃ C T0 : ℝ, 0 < C ∧ 1 ≤ T0 ∧
      ∀ T t sigma : ℝ,
        T0 ≤ T → T ≤ |t| → |t| ≤ 2 * T →
        sigma ∈ Set.Icc (1 / 2 : ℝ) 2 →
        ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤ C * Real.sqrt T := by
  obtain ⟨A, hA, happ⟩ := exists_riemannZeta_first_approximation
  refine ⟨A + 6, 1, by linarith, le_rfl, ?_⟩
  intro T t sigma hT htl htu hsigma
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  let s : ℂ := (sigma : ℂ) + I * t
  let x : ℝ := 4 * T
  have hsre : s.re = sigma := by simp [s]
  have hsim : |s.im| = |t| := by simp [s]
  have hs1 : s ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    simp [s] at him
    have htpos : 0 < |t| := zero_lt_one.trans_le (hT.trans htl)
    rw [him, abs_zero] at htpos
    exact lt_irrefl 0 htpos
  have hx : 1 ≤ x := by dsimp [x]; nlinarith
  have himx : |s.im| ≤ x / 2 := by
    rw [hsim]
    dsimp [x]
    linarith
  obtain ⟨R, hzeta, hR⟩ :=
    happ s x (by rw [hsre]; linarith [hsigma.1])
      (by rw [hsre]; exact hsigma.2) hs1 hx himx
  let N : ℕ := Nat.floor x
  have hNx : (N : ℝ) ≤ x := by
    dsimp [N]
    exact Nat.floor_le (zero_le_one.trans hx)
  have hsqrtN : Real.sqrt N ≤ 2 * Real.sqrt T := by
    have hNnonneg : 0 ≤ (N : ℝ) := by positivity
    have hsquare : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt hNnonneg
    have hTsquare : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hTpos.le
    nlinarith [Real.sqrt_nonneg (N : ℝ), Real.sqrt_nonneg T]
  have hpoly :
      ‖∑ n ∈ Finset.Icc 1 N, 1 / (n : ℂ) ^ s‖ ≤
        4 * Real.sqrt T := by
    calc
      ‖∑ n ∈ Finset.Icc 1 N, 1 / (n : ℂ) ^ s‖ ≤
          ∑ n ∈ Finset.Icc 1 N, ‖1 / (n : ℂ) ^ s‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 N, (Real.sqrt n)⁻¹ := by
        apply Finset.sum_le_sum
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hnpos : 0 < n := Nat.zero_lt_of_lt hn1
        rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hnpos,
          one_div, ← Real.rpow_neg (Nat.cast_nonneg n)]
        calc
          (n : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le
              (by exact_mod_cast hn1)
                (by rw [hsre]; linarith [hsigma.1])
          _ = (Real.sqrt n)⁻¹ := by
            rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow]
      _ ≤ 2 * Real.sqrt N := sum_inv_sqrt_Icc_one_le_two_sqrt N
      _ ≤ 4 * Real.sqrt T := by linarith
  have hpole : ‖(x : ℂ) ^ (1 - s) / (s - 1)‖ ≤
      2 * Real.sqrt T := by
    have hden : 1 ≤ ‖s - 1‖ := by
      have himnorm := Complex.abs_im_le_norm (s - 1)
      have him_eq : |(s - 1).im| = |t| := by simp [s]
      rw [← him_eq] at htl
      exact (hT.trans htl).trans himnorm
    have hbase : 1 ≤ x := hx
    have hpow : x ^ (1 - sigma) ≤ x ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith [hsigma.1])
    have hsqrtx : x ^ (1 / 2 : ℝ) = 2 * Real.sqrt T := by
      dsimp [x]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by dsimp [x]; positivity)]
    simp only [sub_re, one_re, hsre]
    calc
      x ^ (1 - sigma) / ‖s - 1‖ ≤ x ^ (1 - sigma) :=
        div_le_self (Real.rpow_nonneg (by positivity) _) hden
      _ ≤ x ^ (1 / 2 : ℝ) := hpow
      _ = 2 * Real.sqrt T := hsqrtx
  have hR' : ‖R‖ ≤ A * Real.sqrt T := by
    have hxneg : x ^ (-s.re) ≤ 1 := by
      have hexp : -s.re ≤ 0 := by rw [hsre]; linarith [hsigma.1]
      simpa using Real.rpow_le_one_of_one_le_of_nonpos hx hexp
    calc
      ‖R‖ ≤ A * x ^ (-s.re) := hR
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left hxneg hA
      _ ≤ A * Real.sqrt T := by
        have hsqrt : 1 ≤ Real.sqrt T := Real.one_le_sqrt.mpr hT
        exact mul_le_mul_of_nonneg_left hsqrt hA
  rw [hzeta]
  change ‖(∑ n ∈ Finset.Icc 1 N, 1 / (n : ℂ) ^ s) +
      (x : ℂ) ^ (1 - s) / (s - 1) + R‖ ≤
    (A + 6) * Real.sqrt T
  calc
    ‖(∑ n ∈ Finset.Icc 1 N, 1 / (n : ℂ) ^ s) +
        (x : ℂ) ^ (1 - s) / (s - 1) + R‖ ≤
      ‖∑ n ∈ Finset.Icc 1 N, 1 / (n : ℂ) ^ s‖ +
        ‖(x : ℂ) ^ (1 - s) / (s - 1)‖ + ‖R‖ := by
      calc
        _ ≤ ‖(∑ n ∈ Finset.Icc 1 N, 1 / (n : ℂ) ^ s) +
              (x : ℂ) ^ (1 - s) / (s - 1)‖ + ‖R‖ := norm_add_le _ _
        _ ≤ (‖∑ n ∈ Finset.Icc 1 N, 1 / (n : ℂ) ^ s‖ +
              ‖(x : ℂ) ^ (1 - s) / (s - 1)‖) + ‖R‖ :=
          add_le_add (norm_add_le _ _) le_rfl
    _ ≤ 4 * Real.sqrt T + 2 * Real.sqrt T + A * Real.sqrt T :=
      add_le_add (add_le_add hpoly hpole) hR'
    _ = (A + 6) * Real.sqrt T := by ring

/-- Every square-root-zeta mollifier is `O(sqrt X)` throughout the half strip
`re(s) >= 1/2`, uniformly in the height. -/
theorem norm_selbergSqrtZetaMollifier_half_strip_le_two_sqrt
    {X : ℕ} (hX : 2 ≤ X) {sigma t : ℝ} (hsigma : 1 / 2 ≤ sigma) :
    ‖selbergSqrtZetaMollifier X ((sigma : ℂ) + I * t)‖ ≤
      2 * Real.sqrt X := by
  unfold selbergSqrtZetaMollifier selbergMollifier
  calc
    ‖∑ n ∈ Finset.Icc 1 X,
        (selbergSqrtZetaTaperedCoeff X n : ℂ) *
          (1 / (n : ℂ) ^ ((sigma : ℂ) + I * t))‖ ≤
      ∑ n ∈ Finset.Icc 1 X,
        ‖(selbergSqrtZetaTaperedCoeff X n : ℂ) *
          (1 / (n : ℂ) ^ ((sigma : ℂ) + I * t))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
      have hnpos : 0 < n := Nat.zero_lt_of_lt hn1
      have hcoeff : ‖(selbergSqrtZetaTaperedCoeff X n : ℂ)‖ ≤ 1 := by
        simpa [Complex.norm_real, Real.norm_eq_abs] using
          abs_selbergSqrtZetaTaperedCoeff_le_one hX hn1 hnX
      rw [norm_mul, norm_div, norm_one,
        Complex.norm_natCast_cpow_of_pos hnpos, one_div,
        ← Real.rpow_neg (Nat.cast_nonneg n)]
      have hre : (((sigma : ℂ) + I * t).re) = sigma := by simp
      rw [hre]
      have hpow : (n : ℝ) ^ (-sigma) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1)
          (neg_le_neg hsigma)
      calc
        ‖(selbergSqrtZetaTaperedCoeff X n : ℂ)‖ * (n : ℝ) ^ (-sigma) ≤
            1 * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul hcoeff hpow (Real.rpow_nonneg (by positivity) _)
            (by norm_num)
        _ = (Real.sqrt n)⁻¹ := by
          rw [one_mul, Real.rpow_neg (Nat.cast_nonneg n),
            ← Real.sqrt_eq_rpow]
    _ ≤ 2 * Real.sqrt X := sum_inv_sqrt_Icc_one_le_two_sqrt X

/-- Both horizontal contour sides are `O(X * sqrt T)` uniformly for dyadic
heights. -/
theorem exists_norm_intervalIntegral_selbergFirstMomentAuxiliary_horizontal_le :
    ∃ C T0 : ℝ, 0 < C ∧ 1 ≤ T0 ∧
      ∀ T t : ℝ, ∀ X : ℕ,
        T0 ≤ T → T ≤ |t| → |t| ≤ 2 * T → 2 ≤ X →
        ‖∫ sigma in (1 / 2 : ℝ)..2,
            selbergFirstMomentAuxiliary X ((sigma : ℂ) + I * t)‖ ≤
          C * X * Real.sqrt T := by
  obtain ⟨A, T0, hA, hT0, hzeta⟩ :=
    exists_norm_riemannZeta_half_two_strip_le_sqrt
  refine ⟨6 * A, T0, by positivity, hT0, ?_⟩
  intro T t X hT htl htu hX
  have hpoint : ∀ sigma ∈ Set.uIoc (1 / 2 : ℝ) 2,
      ‖selbergFirstMomentAuxiliary X ((sigma : ℂ) + I * t)‖ ≤
        4 * A * X * Real.sqrt T := by
    intro sigma hsigma
    rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hsigma
    have hsigmaIcc : sigma ∈ Set.Icc (1 / 2 : ℝ) 2 :=
      ⟨hsigma.1.le, hsigma.2⟩
    have hz := hzeta T t sigma hT htl htu hsigmaIcc
    have hM := norm_selbergSqrtZetaMollifier_half_strip_le_two_sqrt
      hX (t := t) hsigmaIcc.1
    unfold selbergFirstMomentAuxiliary
    rw [norm_mul, norm_mul]
    calc
      ‖riemannZeta ((sigma : ℂ) + I * t)‖ *
          ‖selbergSqrtZetaMollifier X ((sigma : ℂ) + I * t)‖ *
          ‖selbergSqrtZetaMollifier X ((sigma : ℂ) + I * t)‖ ≤
        (A * Real.sqrt T) * (2 * Real.sqrt X) *
          (2 * Real.sqrt X) := by gcongr
      _ = 4 * A * X * Real.sqrt T := by
        have hsqrtX : (Real.sqrt X) ^ 2 = (X : ℝ) :=
          Real.sq_sqrt (by positivity)
        calc
          (A * Real.sqrt T) * (2 * Real.sqrt X) *
              (2 * Real.sqrt X) =
            4 * A * Real.sqrt T * (Real.sqrt X) ^ 2 := by ring
          _ = 4 * A * X * Real.sqrt T := by rw [hsqrtX]; ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun sigma : ℝ =>
      selbergFirstMomentAuxiliary X ((sigma : ℂ) + I * t))
    (a := (1 / 2 : ℝ)) (b := 2)
    (C := 4 * A * X * Real.sqrt T) hpoint
  norm_num at hi
  calc
    ‖∫ sigma in (1 / 2 : ℝ)..2,
        selbergFirstMomentAuxiliary X ((sigma : ℂ) + I * t)‖ ≤
      (4 * A * X * Real.sqrt T) * (3 / 2 : ℝ) := hi
    _ = (6 * A) * X * Real.sqrt T := by ring

end HardyTheorem
