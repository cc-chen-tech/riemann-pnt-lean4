import HardyTheorem.ConreyExplicitIntegralBridge
import HardyTheorem.ConreyMollifierProduct
import PrimeNumberTheorem.CarlsonDivisorSquare

/-!
# Quantitative moving right edge for Conrey's explicit mollifier

This file proves the finite-Dirichlet-polynomial part of the corrected
right-edge estimate used in Conrey's equation (37).  It does not assert the
corresponding quantitative approximation for `V₁` or the long mollified
mean-square theorem.
-/

open Complex Set
open scoped BigOperators

namespace HardyTheorem

/-- The explicit polynomial used in the two-fifths certificate is bounded by
one on the mollifier interval. -/
theorem abs_conreyExplicitP_le_one {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    |conreyExplicitP x| ≤ 1 := by
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x - 1)]
  have hx3 : x ^ 3 ≤ x := by
    calc
      x ^ 3 = x * x ^ 2 := by ring
      _ ≤ x * 1 := mul_le_mul_of_nonneg_left hx2 hx0
      _ = x := by ring
  have hx4 : x ^ 4 ≤ 1 := by
    have hprod := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx2)
    nlinarith
  have hx5 : x ^ 5 ≤ x := by
    calc
      x ^ 5 = x * x ^ 4 := by ring
      _ ≤ x * 1 := mul_le_mul_of_nonneg_left hx4 hx0
      _ = x := by ring
  have hP0 : 0 ≤ conreyExplicitP x := by
    rw [conreyExplicitP]
    positivity
  rw [abs_of_nonneg hP0, conreyExplicitP]
  nlinarith

private theorem conreyMollifierLogRatio_mem_Icc
    {Y n : ℕ} (hY : 2 ≤ Y) (hn : n ∈ Finset.Icc 1 Y) :
    Real.log ((Y : ℝ) / (n : ℝ)) / Real.log Y ∈ Set.Icc (0 : ℝ) 1 := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnY : n ≤ Y := (Finset.mem_Icc.mp hn).2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hYpos : (0 : ℝ) < Y := by positivity
  have hYone : (1 : ℝ) < Y := by exact_mod_cast hY
  have hlogY : 0 < Real.log (Y : ℝ) := Real.log_pos hYone
  have hquotOne : (1 : ℝ) ≤ (Y : ℝ) / (n : ℝ) := by
    rw [le_div_iff₀ hnpos]
    simpa using (by exact_mod_cast hnY : (n : ℝ) ≤ Y)
  have hquotPos : (0 : ℝ) < (Y : ℝ) / (n : ℝ) := div_pos hYpos hnpos
  have hquotY : (Y : ℝ) / (n : ℝ) ≤ (Y : ℝ) := by
    rw [div_le_iff₀ hnpos]
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    nlinarith
  have hlogNonneg : 0 ≤ Real.log ((Y : ℝ) / (n : ℝ)) :=
    Real.log_nonneg hquotOne
  have hlogLe : Real.log ((Y : ℝ) / (n : ℝ)) ≤ Real.log (Y : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hquotPos hYpos hquotY
  constructor
  · exact div_nonneg hlogNonneg hlogY.le
  · exact (div_le_one hlogY).2 hlogLe

theorem norm_conreyMollifierCoefficient_le_one
    {Y n : ℕ} {sigma0 : ℝ} {P : ℝ → ℝ}
    (hY : 2 ≤ Y) (hn : n ∈ Finset.Icc 1 Y)
    (hsigma0 : sigma0 ≤ 1 / 2)
    (hP : ∀ x ∈ Set.Icc (0 : ℝ) 1, |P x| ≤ 1) :
    ‖conreyMollifierCoefficient Y sigma0 P n‖ ≤ 1 := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hmuReal : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_intCast] using hmuReal
  have hx := conreyMollifierLogRatio_mem_Icc hY hn
  have hpoly : ‖(P (Real.log ((Y : ℝ) / (n : ℝ)) / Real.log Y) : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hP _ hx
  have hpow : ‖(n : ℂ) ^ ((sigma0 - 1 / 2 : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hnpos]
    simp only [Complex.ofReal_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast hn1) (by linarith)
  rw [conreyMollifierCoefficient, norm_mul, norm_mul]
  have hfirst :
      ‖(ArithmeticFunction.moebius n : ℂ)‖ *
          ‖(P (Real.log ((Y : ℝ) / (n : ℝ)) / Real.log Y) : ℂ)‖ ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hmu hpoly (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  calc
    _ ≤ 1 * 1 := mul_le_mul hfirst hpow (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- On the closed right half-plane, the actual explicit Conrey mollifier is
bounded by the length of its finite support. -/
theorem norm_conreyExplicitMollifier_le_natCast_of_re_nonneg
    {Y : ℕ} {sigma0 : ℝ} {s : ℂ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2) (hsre : 0 ≤ s.re) :
    ‖conreyMollifier Y sigma0 conreyExplicitP s‖ ≤ Y := by
  unfold conreyMollifier selbergMollifier
  calc
    ‖∑ n ∈ Finset.Icc 1 Y,
        conreyMollifierCoefficient Y sigma0 conreyExplicitP n *
          (1 / (n : ℂ) ^ s)‖ ≤
        ∑ n ∈ Finset.Icc 1 Y,
          ‖conreyMollifierCoefficient Y sigma0 conreyExplicitP n *
            (1 / (n : ℂ) ^ s)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 Y, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      have hnRone : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      have hcoeff := norm_conreyMollifierCoefficient_le_one
        hY hn hsigma0 (fun _x hx => abs_conreyExplicitP_le_one hx)
      have hdenPos : 0 < (n : ℝ) ^ s.re :=
        Real.rpow_pos_of_pos (by exact_mod_cast hnpos) _
      have hden : (1 : ℝ) ≤ (n : ℝ) ^ s.re :=
        Real.one_le_rpow hnRone hsre
      have hterm : ‖1 / (n : ℂ) ^ s‖ ≤ 1 := by
        rw [norm_div, norm_one,
          Complex.norm_natCast_cpow_of_pos hnpos]
        exact (div_le_one hdenPos).2 hden
      rw [norm_mul]
      exact (mul_le_mul hcoeff hterm (norm_nonneg _) (by norm_num)).trans_eq
        (by norm_num)
    _ = Y := by simp

/-- For any normalized polynomial profile bounded by one on `[0,1]`, the
actual equation-(33) mollifier has the standard p-series right-tail bound.
The estimate is uniform in the imaginary part and in the cutoff `Y`. -/
theorem norm_conreyMollifier_sub_one_le_rightTail
    {Y : ℕ} {sigma0 : ℝ} {P : ℝ → ℝ} {s : ℂ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2)
    (hP1 : P 1 = 1)
    (hP : ∀ x ∈ Set.Icc (0 : ℝ) 1, |P x| ≤ 1)
    (hs : 1 < s.re) :
    ‖conreyMollifier Y sigma0 P s - 1‖ ≤
      (2 : ℝ) ^ (-s.re) * (1 + 2 / (s.re - 1)) := by
  let coeff : ℕ → ℂ := conreyMollifierCoefficient Y sigma0 P
  have hOneMem : 1 ∈ Finset.Icc 1 Y :=
    Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hcoeffOne : coeff 1 = 1 := by
    exact conreyMollifierCoefficient_one hY hP1 sigma0
  have herase : (Finset.Icc 1 Y).erase 1 = Finset.Icc 2 Y := by
    ext n
    simp only [Finset.mem_erase, Finset.mem_Icc]
    omega
  have hsplit :
      conreyMollifier Y sigma0 P s - 1 =
        ∑ n ∈ Finset.Icc 2 Y, coeff n * (1 / (n : ℂ) ^ s) := by
    unfold conreyMollifier selbergMollifier
    rw [← Finset.sum_erase_add _ _ hOneMem, herase]
    dsimp only [coeff] at hcoeffOne ⊢
    rw [hcoeffOne]
    simp
  rw [hsplit]
  have hfinite :
      ‖∑ n ∈ Finset.Icc 2 Y, coeff n * (1 / (n : ℂ) ^ s)‖ ≤
        ∑ n ∈ Finset.Icc 2 Y, (n : ℝ) ^ (-s.re) := by
    calc
      ‖∑ n ∈ Finset.Icc 2 Y, coeff n * (1 / (n : ℂ) ^ s)‖ ≤
          ∑ n ∈ Finset.Icc 2 Y, ‖coeff n * (1 / (n : ℂ) ^ s)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 2 Y, (n : ℝ) ^ (-s.re) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
        have hnpos : 0 < n := by omega
        have hnOneY : n ∈ Finset.Icc 1 Y :=
          Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hn).2⟩
        have hcoeff := norm_conreyMollifierCoefficient_le_one
          hY hnOneY hsigma0 hP
        rw [norm_mul, norm_div, norm_one,
          Complex.norm_natCast_cpow_of_pos hnpos,
          Real.rpow_neg (by exact_mod_cast (Nat.zero_le n) : (0 : ℝ) ≤ n)]
        simpa only [one_div, coeff] using
          (mul_le_of_le_one_left
            (inv_nonneg.mpr (Real.rpow_nonneg
              (by exact_mod_cast (Nat.zero_le n) : (0 : ℝ) ≤ n) s.re)) hcoeff)
  refine hfinite.trans ?_
  have hraw := PrimeNumberTheorem.CarlsonZeroDensity.sum_Icc_rpow_le_add_div_of_lt_neg_one
    (L := 2) (U := Y) (by omega) hY (q := -s.re) (by linarith)
  have hden : 0 < s.re - 1 := by linarith
  have hYpow : 0 ≤ (Y : ℝ) ^ (-s.re + 1) := Real.rpow_nonneg (by positivity) _
  have hfrac :
      ((Y : ℝ) ^ (-s.re + 1) - (2 : ℝ) ^ (-s.re + 1)) /
          (-s.re + 1) ≤
        (2 : ℝ) ^ (-s.re + 1) / (s.re - 1) := by
    have heq :
        ((Y : ℝ) ^ (-s.re + 1) - (2 : ℝ) ^ (-s.re + 1)) /
            (-s.re + 1) =
          ((2 : ℝ) ^ (-s.re + 1) - (Y : ℝ) ^ (-s.re + 1)) /
            (s.re - 1) := by
      rw [show -s.re + 1 = -(s.re - 1) by ring, div_neg, neg_sub]
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right (by linarith) hden.le
  calc
    (∑ n ∈ Finset.Icc 2 Y, (n : ℝ) ^ (-s.re)) ≤
        (2 : ℝ) ^ (-s.re) +
          ((Y : ℝ) ^ (-s.re + 1) - (2 : ℝ) ^ (-s.re + 1)) /
            (-s.re + 1) := by simpa [add_comm, add_left_comm, add_assoc] using hraw
    _ ≤ (2 : ℝ) ^ (-s.re) +
          (2 : ℝ) ^ (-s.re + 1) / (s.re - 1) :=
      add_le_add le_rfl hfrac
    _ = (2 : ℝ) ^ (-s.re) * (1 + 2 / (s.re - 1)) := by
      rw [show -s.re + 1 = -s.re + 1 by rfl,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      field_simp [hden.ne']

/-- On the corrected moving edge `Re s = 2 log L`, Conrey's explicit
mollifier is uniformly within `3 / L` of its constant term.  This repairs
the `sigma₁ = log L` scale mismatch in the printed 1983 argument. -/
theorem norm_conreyExplicitMollifier_movingRight_sub_one_le
    {Y : ℕ} {sigma0 L : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2)
    (hL : Real.exp 1 ≤ L) (t : ℝ) :
    ‖conreyMollifier Y sigma0 conreyExplicitP
        ((2 * Real.log L : ℂ) + I * t) - 1‖ ≤ 3 / L := by
  have hLpos : 0 < L := (Real.exp_pos 1).trans_le hL
  have hlogL : 1 ≤ Real.log L := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (Real.exp_pos 1) hLpos hL
    simpa only [Real.log_exp] using hmono
  have hs : 1 < (((2 * Real.log L : ℝ) : ℂ) + I * t).re := by
    norm_num [Complex.mul_re]
    linarith
  have hP1 : conreyExplicitP 1 = 1 := by
    norm_num [conreyExplicitP]
  have htail := norm_conreyMollifier_sub_one_le_rightTail
    (Y := Y) (sigma0 := sigma0) (P := conreyExplicitP)
    (s := ((2 * Real.log L : ℝ) : ℂ) + I * t)
    hY hsigma0 hP1 (fun _x hx => abs_conreyExplicitP_le_one hx) hs
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9 |>.le
  have hpow :
      (2 : ℝ) ^ (-(2 * Real.log L)) ≤ 1 / L := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hexponent :
        Real.log 2 * (-(2 * Real.log L)) ≤ -Real.log L := by
      have hlogL0 : 0 ≤ Real.log L := zero_le_one.trans hlogL
      nlinarith [mul_nonneg (sub_nonneg.mpr hlogTwo) hlogL0]
    calc
      Real.exp (Real.log 2 * (-(2 * Real.log L))) ≤
          Real.exp (-Real.log L) := Real.exp_le_exp.mpr hexponent
      _ = 1 / L := by
        rw [Real.exp_neg, Real.exp_log hLpos]
        simp only [one_div]
  have hfactor :
      1 + 2 / (2 * Real.log L - 1) ≤ (3 : ℝ) := by
    have hden : 0 < 2 * Real.log L - 1 := by linarith
    have hdiv : 2 / (2 * Real.log L - 1) ≤ (2 : ℝ) := by
      rw [div_le_iff₀ hden]
      nlinarith
    linarith
  have hfactor0 : 0 ≤ 1 + 2 / (2 * Real.log L - 1) := by
    have : 0 < 2 * Real.log L - 1 := by linarith
    positivity
  have hLinv0 : 0 ≤ 1 / L := by positivity
  calc
    ‖conreyMollifier Y sigma0 conreyExplicitP
        ((2 * Real.log L : ℂ) + I * t) - 1‖ ≤
        (2 : ℝ) ^ (-(2 * Real.log L)) *
          (1 + 2 / (2 * Real.log L - 1)) := by simpa using htail
    _ ≤ (1 / L) * 3 := mul_le_mul hpow hfactor hfactor0 hLinv0
    _ = 3 / L := by ring

end HardyTheorem
