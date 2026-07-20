import HardyTheorem.SelbergGoodWindowMeasure
import HardyTheorem.SelbergMollifiedCoefficientArithmetic

open Complex Filter MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-!
# A constant-term lower bound for the Selberg-mollified Hardy function

For an absolute-value estimate we may multiply the first zeta approximation
by `M ^ 2`: its norm is exactly `|zeta| * |M| ^ 2`, hence exactly the absolute
value of the sign-preserving mollified Hardy function.  The conjugate/phase
expansion needed for signed estimates belongs to a separate module.
-/

/-- The short integral of the finite zeta polynomial times `M ^ 2`, after
subtracting its distinguished unit contribution. -/
noncomputable def selbergMollifiedShortDirichletPolynomial
    (H : ℝ) (N X : ℕ) (t : ℝ) : ℂ :=
  ∫ u in t..t + H,
    (((∑ n ∈ Finset.Icc 1 N,
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * u)) *
      selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * u)) *
      selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * u) - 1)

/-- A pointwise finite-sum bound for the critical-line Selberg mollifier. -/
theorem norm_selbergMoebiusMollifier_criticalLine_le_sum_inv_sqrt
    {X : ℕ} (hX : 2 ≤ X) (t : ℝ) :
    ‖selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)‖ ≤
      ∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹ := by
  unfold selbergMoebiusMollifier selbergMollifier
  calc
    ‖∑ n ∈ Finset.Icc 1 X,
        (selbergMoebiusCoeff X n : ℂ) *
          (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))‖ ≤
        ∑ n ∈ Finset.Icc 1 X,
          ‖(selbergMoebiusCoeff X n : ℂ) *
            (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
      have hnpos : 0 < n := by omega
      have hcoeff : ‖(selbergMoebiusCoeff X n : ℂ)‖ ≤ 1 := by
        simpa [Complex.norm_real, Real.norm_eq_abs] using
          abs_selbergMoebiusCoeff_le_one hX hn1 hnX
      have hpow :
          ‖(n : ℂ) ^ ((1 / 2 : ℂ) + I * t)‖ = Real.sqrt n := by
        rw [Complex.norm_natCast_cpow_of_pos hnpos]
        simp [Real.sqrt_eq_rpow]
      rw [norm_mul, norm_div, norm_one, hpow, one_div]
      exact mul_le_of_le_one_left (inv_nonneg.mpr (Real.sqrt_nonneg n)) hcoeff

/-- The preceding pointwise bound is at most `2 * sqrt X`. -/
theorem norm_selbergMoebiusMollifier_criticalLine_le_two_sqrt
    {X : ℕ} (hX : 2 ≤ X) (t : ℝ) :
    ‖selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)‖ ≤
      2 * Real.sqrt X :=
  (norm_selbergMoebiusMollifier_criticalLine_le_sum_inv_sqrt hX t).trans
    (sum_inv_sqrt_Icc_one_le_two_sqrt X)

/-- Multiplying the exact zeta-polynomial/mollifier convolution by the second
mollifier gives the finite polynomial used by the absolute-value argument. -/
theorem criticalLineDirichletPolynomial_mul_selbergMoebiusMollifier_sq_eq
    (N X : ℕ) (t : ℝ) :
    ((∑ n ∈ Finset.Icc 1 N,
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) =
      (∑ k ∈ Finset.Icc 1 (N * X),
        (selbergMollifiedDirichletCoeff N X k : ℂ) *
          (1 / (k : ℂ) ^ ((1 / 2 : ℂ) + I * t))) *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) := by
  rw [criticalLineDirichletPolynomial_mul_selbergMoebiusMollifier_eq_convolutionSum]

/-- The absolute value of the sign-preserving mollified Hardy function is the
norm of `zeta * M ^ 2`. -/
theorem abs_selbergMoebiusMollifiedHardyZ_eq_norm_zeta_mul_mollifier_sq
    (X : ℕ) (t : ℝ) :
    |selbergMoebiusMollifiedHardyZ X t| =
      ‖(riemannZeta ((1 / 2 : ℂ) + I * t) *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)‖ := by
  rw [selbergMoebiusMollifiedHardyZ, selbergMollifiedHardyZ,
    abs_mul, abs_hardyZ_eq_norm_riemannZeta,
    Complex.normSq_eq_norm_sq]
  rw [abs_of_nonneg (sq_nonneg _)]
  rw [norm_mul, norm_mul]
  unfold selbergMoebiusMollifier
  ring

/-- Pointwise first approximation after multiplying by the two mollifier
factors required by the absolute-value argument.  The analytic error is
bounded by the square of the explicit finite `1 / sqrt n` majorant. -/
theorem exists_selbergMoebiusMollifiedZetaFirstApprox :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T t : ℝ,
        T0 ≤ T → t ∈ Icc T (2 * T) →
          ∃ E : ℂ,
            (riemannZeta ((1 / 2 : ℂ) + I * t) *
                selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) *
              selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) =
                ((∑ k ∈ Finset.Icc 1
                    (firstZetaApproximationCutoff T * X),
                    (selbergMollifiedDirichletCoeff
                      (firstZetaApproximationCutoff T) X k : ℂ) *
                      (1 / (k : ℂ) ^ ((1 / 2 : ℂ) + I * t))) *
                  selbergMoebiusMollifier X
                    ((1 / 2 : ℂ) + I * t)) + E ∧
            ‖E‖ ≤ C / Real.sqrt T *
              (∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹) ^ 2 := by
  obtain ⟨C, T0, hC, hT0, happ⟩ := criticalLineZetaFirstApprox
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro X hX T t hT ht
  obtain ⟨R, hzeta, hR⟩ := happ T t hT ht
  let M : ℂ := selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)
  refine ⟨(R * M) * M, ?_, ?_⟩
  · rw [hzeta]
    have hpoly :=
      criticalLineDirichletPolynomial_mul_selbergMoebiusMollifier_sq_eq
        (firstZetaApproximationCutoff T) X t
    dsimp only [M]
    rw [← hpoly]
    ring
  · have hM :=
      norm_selbergMoebiusMollifier_criticalLine_le_sum_inv_sqrt hX t
    have hsum_nonneg : 0 ≤
        ∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹ := by positivity
    dsimp only [M]
    rw [norm_mul, norm_mul]
    calc
      ‖R‖ * ‖selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)‖ *
          ‖selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)‖ ≤
        (C / Real.sqrt T) *
          ‖selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)‖ *
            ‖selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)‖ := by
          gcongr
      _ ≤ (C / Real.sqrt T) *
          (∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹) *
            (∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹) := by
          gcongr
      _ = C / Real.sqrt T *
          (∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹) ^ 2 := by ring

/-- The constant term in the first zeta approximation gives a uniform lower
bound for the short absolute mass of the sign-preserving Selberg-mollified
Hardy function.  The finite-sum factor is completely explicit and comes only
from bounding the two mollifier copies in the analytic remainder. -/
theorem exists_selbergMoebiusAbsShortIntegral_ge_sub_shortDirichlet :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H t : ℝ,
        T0 ≤ T → 0 ≤ H →
        t ∈ Icc T (2 * T - H) →
          H -
              ‖selbergMollifiedShortDirichletPolynomial H
                (firstZetaApproximationCutoff T) X t‖ -
              C * H / Real.sqrt T *
                (∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹) ^ 2 ≤
            selbergMoebiusAbsShortIntegral X H t := by
  obtain ⟨C, T0, hC, hT0, happ⟩ := criticalLineZetaFirstApprox
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro X hX T H t hT hH ht
  have hT1 : 1 ≤ T := hT0.trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have htt : t ≤ t + H := by linarith
  let N : ℕ := firstZetaApproximationCutoff T
  let M : ℝ → ℂ := fun u =>
    selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * u)
  let F : ℝ → ℂ := fun u =>
    (riemannZeta ((1 / 2 : ℂ) + I * u) * M u) * M u
  let Q : ℝ → ℂ := fun u =>
    (((∑ n ∈ Finset.Icc 1 N,
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * u)) * M u) * M u) - 1
  let E : ℝ → ℂ := fun u =>
    (riemannZeta ((1 / 2 : ℂ) + I * u) -
      ∑ n ∈ Finset.Icc 1 N,
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * u)) * M u * M u
  have hN : 1 ≤ N := by
    dsimp only [N, firstZetaApproximationCutoff]
    apply Nat.le_floor
    norm_num
    linarith
  have hpoint : ∀ u ∈ Icc t (t + H), F u = 1 + Q u + E u := by
    intro u hu
    have huT : u ∈ Icc T (2 * T) := by
      constructor
      · exact ht.1.trans hu.1
      · linarith [hu.2, ht.2]
    obtain ⟨R, hzeta, hR⟩ := happ T u hT huT
    dsimp only [F, Q, E, M]
    rw [hzeta]
    ring
  have hEpoint : ∀ u ∈ Icc t (t + H),
      ‖E u‖ ≤ C / Real.sqrt T *
        (∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹) ^ 2 := by
    intro u hu
    have huT : u ∈ Icc T (2 * T) := by
      constructor
      · exact ht.1.trans hu.1
      · linarith [hu.2, ht.2]
    obtain ⟨R, hzeta, hR⟩ := happ T u hT huT
    have hM := norm_selbergMoebiusMollifier_criticalLine_le_sum_inv_sqrt hX u
    have hsum_nonneg : 0 ≤
        ∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹ := by positivity
    have hRident :
        riemannZeta ((1 / 2 : ℂ) + I * u) -
            ∑ n ∈ Finset.Icc 1 N,
              1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * u) = R := by
      rw [hzeta]
      ring
    dsimp only [E, M]
    rw [hRident, norm_mul, norm_mul]
    have hMnonneg : 0 ≤
        ‖selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * u)‖ :=
      norm_nonneg _
    have hbase : 0 ≤ C / Real.sqrt T := by positivity
    calc
      ‖R‖ * ‖selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * u)‖ *
          ‖selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * u)‖ ≤
        (C / Real.sqrt T) *
          ‖selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * u)‖ *
            ‖selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * u)‖ := by
          gcongr
      _ ≤ (C / Real.sqrt T) *
          (∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹) *
            (∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹) := by
          gcongr
      _ = C / Real.sqrt T *
          (∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹) ^ 2 := by ring
  have hMcont : Continuous M := by
    simpa only [M] using
      continuous_selbergMollifier_criticalLine X
        (fun n => (selbergMoebiusCoeff X n : ℂ))
  have hPolyCont : Continuous (fun u : ℝ =>
      ∑ n ∈ Finset.Icc 1 N,
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * u)) := by
    apply continuous_finset_sum
    intro n hn
    have hn0 : n ≠ 0 := by
      have hn1 := (Finset.mem_Icc.mp hn).1
      omega
    rw [show (fun u : ℝ =>
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * u)) =
      fun u : ℝ => ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
        Complex.exp ((-I * (Real.log n : ℂ)) * u) by
        funext u
        rw [inv_nat_cpow_criticalLine_eq_exp hn0 u]]
    fun_prop
  have hQcont : Continuous Q := by
    dsimp only [Q]
    exact (hPolyCont.mul hMcont |>.mul hMcont).sub continuous_const
  have hEcont : ContinuousOn E (Icc t (t + H)) := by
    intro u hu
    have huT : T ≤ u := ht.1.trans hu.1
    have hupos : 0 < u := hTpos.trans_le huT
    have hs1 : ((1 / 2 : ℂ) + I * u) ≠ 1 := by
      intro h
      have him := congrArg Complex.im h
      norm_num at him
      linarith
    have hpath : ContinuousAt (fun v : ℝ => (1 / 2 : ℂ) + I * v) u := by
      fun_prop
    have hzbase : ContinuousAt riemannZeta ((1 / 2 : ℂ) + I * u) :=
      (differentiableAt_riemannZeta hs1).continuousAt
    have hzcont : ContinuousAt
        (fun v : ℝ => riemannZeta ((1 / 2 : ℂ) + I * v)) u :=
      (show Tendsto riemannZeta
          (nhds ((1 / 2 : ℂ) + I * u))
          (nhds (riemannZeta ((1 / 2 : ℂ) + I * u))) from hzbase).comp
        (show Tendsto (fun v : ℝ => (1 / 2 : ℂ) + I * v)
          (nhds u) (nhds ((1 / 2 : ℂ) + I * u)) from hpath)
    dsimp only [E, M]
    exact ((hzcont.sub hPolyCont.continuousAt).mul hMcont.continuousAt |>.mul
      hMcont.continuousAt).continuousWithinAt
  have hFcont : ContinuousOn F (Icc t (t + H)) := by
    intro u hu
    have huT : T ≤ u := ht.1.trans hu.1
    have hupos : 0 < u := hTpos.trans_le huT
    have hs1 : ((1 / 2 : ℂ) + I * u) ≠ 1 := by
      intro h
      have him := congrArg Complex.im h
      norm_num at him
      linarith
    have hpath : ContinuousAt (fun v : ℝ => (1 / 2 : ℂ) + I * v) u := by
      fun_prop
    have hzbase : ContinuousAt riemannZeta ((1 / 2 : ℂ) + I * u) :=
      (differentiableAt_riemannZeta hs1).continuousAt
    have hzcont : ContinuousAt
        (fun v : ℝ => riemannZeta ((1 / 2 : ℂ) + I * v)) u :=
      (show Tendsto riemannZeta
          (nhds ((1 / 2 : ℂ) + I * u))
          (nhds (riemannZeta ((1 / 2 : ℂ) + I * u))) from hzbase).comp
        (show Tendsto (fun v : ℝ => (1 / 2 : ℂ) + I * v)
          (nhds u) (nhds ((1 / 2 : ℂ) + I * u)) from hpath)
    dsimp only [F, M]
    exact (hzcont.mul hMcont.continuousAt |>.mul
      hMcont.continuousAt).continuousWithinAt
  have hQint : IntervalIntegrable Q volume t (t + H) :=
    hQcont.intervalIntegrable _ _
  have hEint : IntervalIntegrable E volume t (t + H) :=
    ContinuousOn.intervalIntegrable (by
      simpa only [uIcc_of_le htt] using hEcont)
  have hFint : IntervalIntegrable F volume t (t + H) :=
    ContinuousOn.intervalIntegrable (by
      simpa only [uIcc_of_le htt] using hFcont)
  have hintegralIdentity :
      (H : ℂ) = (∫ u in t..t + H, F u) -
          selbergMollifiedShortDirichletPolynomial H N X t -
            ∫ u in t..t + H, E u := by
    have hcongr :
        (∫ u in t..t + H, F u) =
          ∫ u in t..t + H, (1 + Q u + E u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le htt] at hu
      exact hpoint u hu
    rw [hcongr]
    have hOneCont : Continuous (fun _u : ℝ => (1 : ℂ)) := continuous_const
    have haddE := intervalIntegral.integral_add
      ((hOneCont.add hQcont).intervalIntegrable t (t + H)) hEint
    change
      (∫ u in t..t + H, ((1 : ℂ) + Q u) + E u) =
        (∫ u in t..t + H, (1 : ℂ) + Q u) +
          ∫ u in t..t + H, E u at haddE
    have haddQ := intervalIntegral.integral_add
      (hOneCont.intervalIntegrable t (t + H)) hQint
    change
      (∫ u in t..t + H, (1 : ℂ) + Q u) =
        (∫ _u in t..t + H, (1 : ℂ)) +
          ∫ u in t..t + H, Q u at haddQ
    have hsplit :
        (∫ u in t..t + H, (1 : ℂ) + Q u + E u) =
          (∫ _u in t..t + H, (1 : ℂ)) +
            (∫ u in t..t + H, Q u) +
              ∫ u in t..t + H, E u := by
      rw [haddE, haddQ]
    rw [hsplit]
    have hone : (∫ _u in t..t + H, (1 : ℂ)) = (H : ℂ) := by
      have h := intervalIntegral.integral_ofReal
        (μ := volume) (a := t) (b := t + H)
          (f := fun _u : ℝ => (1 : ℝ))
      have hreal : (∫ _u in t..t + H, (1 : ℝ)) = H := by simp
      rw [show (fun _u : ℝ => (1 : ℂ)) =
          fun _u : ℝ => ((1 : ℝ) : ℂ) by rfl]
      rw [h, hreal]
    rw [hone]
    dsimp only [selbergMollifiedShortDirichletPolynomial]
    ring
  have hEIntegral :
      ‖∫ u in t..t + H, E u‖ ≤
        C * H / Real.sqrt T *
          (∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹) ^ 2 := by
    have hmajor := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t) (b := t + H)
      (C := C / Real.sqrt T *
        (∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹) ^ 2)
      (f := E) (fun u hu => by
        rw [uIoc_of_le htt] at hu
        exact hEpoint u ⟨hu.1.le, hu.2⟩)
    calc
      ‖∫ u in t..t + H, E u‖ ≤
          (C / Real.sqrt T *
            (∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹) ^ 2) *
              |t + H - t| := hmajor
      _ = C * H / Real.sqrt T *
          (∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹) ^ 2 := by
        rw [abs_of_nonneg (by linarith : 0 ≤ t + H - t)]
        ring
  have htriangle :
      H ≤ ‖∫ u in t..t + H, F u‖ +
          ‖selbergMollifiedShortDirichletPolynomial H N X t‖ +
            ‖∫ u in t..t + H, E u‖ := by
    calc
      H = ‖(H : ℂ)‖ := by
        rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hH]
      _ = ‖(∫ u in t..t + H, F u) -
          selbergMollifiedShortDirichletPolynomial H N X t -
            ∫ u in t..t + H, E u‖ := congrArg norm hintegralIdentity
      _ ≤ ‖(∫ u in t..t + H, F u) -
          selbergMollifiedShortDirichletPolynomial H N X t‖ +
            ‖∫ u in t..t + H, E u‖ := norm_sub_le _ _
      _ ≤ (‖∫ u in t..t + H, F u‖ +
          ‖selbergMollifiedShortDirichletPolynomial H N X t‖) +
            ‖∫ u in t..t + H, E u‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
  have hnormIntegral := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := F) htt
  have hnormEq :
      (∫ u in t..t + H, ‖F u‖) =
        selbergMoebiusAbsShortIntegral X H t := by
    dsimp only [selbergMoebiusAbsShortIntegral]
    apply intervalIntegral.integral_congr
    intro u _hu
    dsimp only [F, M]
    exact (abs_selbergMoebiusMollifiedHardyZ_eq_norm_zeta_mul_mollifier_sq
      X u).symm
  rw [hnormEq] at hnormIntegral
  have htriangle' :
      H ≤ ‖∫ u in t..t + H, F u‖ +
          ‖selbergMollifiedShortDirichletPolynomial H
            (firstZetaApproximationCutoff T) X t‖ +
            ‖∫ u in t..t + H, E u‖ := by
    simpa only [N] using htriangle
  calc
    H -
          ‖selbergMollifiedShortDirichletPolynomial H
            (firstZetaApproximationCutoff T) X t‖ -
          C * H / Real.sqrt T *
            (∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹) ^ 2 ≤
        ‖∫ u in t..t + H, F u‖ := by
      linarith [htriangle', hEIntegral]
    _ ≤ selbergMoebiusAbsShortIntegral X H t := hnormIntegral

/-- A coarser but simpler form of the preceding lower bound, with the
remainder written as `4 * C * H * X / sqrt T`. -/
theorem exists_selbergMoebiusAbsShortIntegral_ge_sub_shortDirichlet_coarse :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H t : ℝ,
        T0 ≤ T → 0 ≤ H →
        t ∈ Icc T (2 * T - H) →
          H -
              ‖selbergMollifiedShortDirichletPolynomial H
                (firstZetaApproximationCutoff T) X t‖ -
              4 * C * H * X / Real.sqrt T ≤
            selbergMoebiusAbsShortIntegral X H t := by
  obtain ⟨C, T0, hC, hT0, hmain⟩ :=
    exists_selbergMoebiusAbsShortIntegral_ge_sub_shortDirichlet
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro X hX T H t hT hH ht
  have h := hmain X hX T H t hT hH ht
  have hsum := sum_inv_sqrt_Icc_one_le_two_sqrt X
  have hsqrtT : 0 < Real.sqrt T := by
    exact Real.sqrt_pos.2 (zero_lt_one.trans_le (hT0.trans hT))
  have hsqrtX : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hsquareX : (Real.sqrt (X : ℝ)) ^ 2 = X := by
    rw [Real.sq_sqrt]
    positivity
  have hsum_nonneg : 0 ≤
      ∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹ := by positivity
  have hsquare :
      (∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹) ^ 2 ≤
        4 * X := by
    nlinarith
  have hfactor : 0 ≤ C * H / Real.sqrt T := by positivity
  have herr :
      C * H / Real.sqrt T *
          (∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹) ^ 2 ≤
        4 * C * H * X / Real.sqrt T := by
    calc
      C * H / Real.sqrt T *
          (∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹) ^ 2 ≤
          C * H / Real.sqrt T * (4 * X) :=
        mul_le_mul_of_nonneg_left hsquare hfactor
      _ = 4 * C * H * X / Real.sqrt T := by ring
  linarith

end HardyTheorem
