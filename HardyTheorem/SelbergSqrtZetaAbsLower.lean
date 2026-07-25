import HardyTheorem.SelbergSqrtZetaCoeffBound

open Complex Filter MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-!
# A short absolute-mass lower bound for the square-root-zeta mollifier

The first zeta approximation is multiplied by two copies of the tapered
square-root-zeta mollifier.  The distinguished constant term of the resulting
finite polynomial contributes the interval length, while the analytic
remainder is controlled using
`norm_selbergSqrtZetaMollifier_criticalLine_le_two_sqrt`.
-/

/-- The Hardy function mollified by two copies of the tapered
square-root-zeta mollifier. -/
noncomputable def selbergSqrtZetaMollifiedHardyZ
    (X : ℕ) (t : ℝ) : ℝ :=
  selbergMollifiedHardyZ X
    (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ)) t

/-- The short integral of the absolute value of the square-root-zeta
mollified Hardy function. -/
noncomputable def selbergSqrtZetaAbsShortIntegral
    (X : ℕ) (H t : ℝ) : ℝ :=
  ∫ u in t..t + H, |selbergSqrtZetaMollifiedHardyZ X u|

/-- The short integral of the finite square-root-zeta polynomial after
subtracting its distinguished constant term. -/
noncomputable def selbergSqrtZetaShortDirichletPolynomialIntegral
    (H : ℝ) (N X : ℕ) (t : ℝ) : ℂ :=
  ∫ u in t..t + H,
    (selbergSqrtZetaShortDirichletTriplePolynomial N X u - 1)

/-- The triple-polynomial integral is the same short polynomial used by the
mean-square and gap-sum estimates. -/
theorem selbergSqrtZetaShortDirichletPolynomialIntegral_eq
    (H : ℝ) (N X : ℕ) (t : ℝ) :
    selbergSqrtZetaShortDirichletPolynomialIntegral H N X t =
      selbergSqrtZetaMollifiedShortDirichletPolynomial H N X t := by
  unfold selbergSqrtZetaShortDirichletPolynomialIntegral
  unfold selbergSqrtZetaMollifiedShortDirichletPolynomial
  apply intervalIntegral.integral_congr
  intro u _hu
  dsimp only
  rw [←
    criticalLineDirichletPolynomial_mul_sqrtZetaMollifier_sq_eq_exponentialPolynomial]

/-- The absolute value of the square-root-zeta mollified Hardy function is
the norm of `zeta * M ^ 2`. -/
theorem abs_selbergSqrtZetaMollifiedHardyZ_eq_norm_zeta_mul_mollifier_sq
    (X : ℕ) (t : ℝ) :
    |selbergSqrtZetaMollifiedHardyZ X t| =
      ‖(riemannZeta ((1 / 2 : ℂ) + I * t) *
          selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)) *
        selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)‖ := by
  rw [selbergSqrtZetaMollifiedHardyZ, selbergMollifiedHardyZ,
    abs_mul, abs_hardyZ_eq_norm_riemannZeta,
    Complex.normSq_eq_norm_sq]
  rw [abs_of_nonneg (sq_nonneg _)]
  rw [norm_mul, norm_mul]
  unfold selbergSqrtZetaMollifier
  ring

/-- The constant term in the first zeta approximation gives a lower bound
for the short absolute mass.  The two mollifier norms are bounded by
`2 * sqrt X`, giving the coarse remainder `4 * C * H * X / sqrt T`. -/
theorem exists_selbergSqrtZetaAbsShortIntegral_ge_sub_shortDirichlet :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H t : ℝ,
        T0 ≤ T → 0 ≤ H →
        t ∈ Icc T (2 * T - H) →
          H -
              ‖selbergSqrtZetaShortDirichletPolynomialIntegral H
                (firstZetaApproximationCutoff T) X t‖ -
              4 * C * H * X / Real.sqrt T ≤
            selbergSqrtZetaAbsShortIntegral X H t := by
  obtain ⟨C, T0, hC, hT0, happ⟩ := criticalLineZetaFirstApprox
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro X hX T H t hT hH ht
  have hT1 : 1 ≤ T := hT0.trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have htt : t ≤ t + H := by linarith
  let N : ℕ := firstZetaApproximationCutoff T
  let M : ℝ → ℂ := fun u =>
    selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * u)
  let F : ℝ → ℂ := fun u =>
    (riemannZeta ((1 / 2 : ℂ) + I * u) * M u) * M u
  let P : ℝ → ℂ := fun u =>
    selbergSqrtZetaShortDirichletTriplePolynomial N X u
  let Q : ℝ → ℂ := fun u => P u - 1
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
    obtain ⟨R, hzeta, _hR⟩ := happ T u hT huT
    have hpoly :=
      criticalLineDirichletPolynomial_mul_sqrtZetaMollifier_sq_eq_exponentialPolynomial
        N X u
    dsimp only [F, P, Q, E, M]
    rw [hzeta, ← hpoly]
    ring
  have hEpoint : ∀ u ∈ Icc t (t + H),
      ‖E u‖ ≤ 4 * C * X / Real.sqrt T := by
    intro u hu
    have huT : u ∈ Icc T (2 * T) := by
      constructor
      · exact ht.1.trans hu.1
      · linarith [hu.2, ht.2]
    obtain ⟨R, hzeta, hR⟩ := happ T u hT huT
    have hM :=
      norm_selbergSqrtZetaMollifier_criticalLine_le_two_sqrt hX u
    have hRident :
        riemannZeta ((1 / 2 : ℂ) + I * u) -
            ∑ n ∈ Finset.Icc 1 N,
              1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * u) = R := by
      rw [hzeta]
      ring
    have hsquareX : (Real.sqrt (X : ℝ)) ^ 2 = X := by
      rw [Real.sq_sqrt]
      positivity
    have hbase : 0 ≤ C / Real.sqrt T := by positivity
    dsimp only [E, M]
    rw [hRident, norm_mul, norm_mul]
    calc
      ‖R‖ *
            ‖selbergSqrtZetaMollifier X
              ((1 / 2 : ℂ) + I * u)‖ *
          ‖selbergSqrtZetaMollifier X
            ((1 / 2 : ℂ) + I * u)‖ ≤
        (C / Real.sqrt T) *
            ‖selbergSqrtZetaMollifier X
              ((1 / 2 : ℂ) + I * u)‖ *
          ‖selbergSqrtZetaMollifier X
            ((1 / 2 : ℂ) + I * u)‖ := by
          gcongr
      _ ≤ (C / Real.sqrt T) *
          (2 * Real.sqrt X) * (2 * Real.sqrt X) := by
          gcongr
      _ = 4 * (C / Real.sqrt T) * (Real.sqrt X) ^ 2 := by ring
      _ = 4 * C * X / Real.sqrt T := by
        rw [hsquareX]
        ring
  have hMcont : Continuous M := by
    simpa only [M, selbergSqrtZetaMollifier] using
      continuous_selbergMollifier_criticalLine X
        (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))
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
  have hPcont : Continuous P := by
    have heq : P = fun u : ℝ =>
        ((∑ n ∈ Finset.Icc 1 N,
            1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * u)) * M u) * M u := by
      funext u
      dsimp only [P, M]
      exact
        (criticalLineDirichletPolynomial_mul_sqrtZetaMollifier_sq_eq_exponentialPolynomial
          N X u).symm
    rw [heq]
    exact (hPolyCont.mul hMcont).mul hMcont
  have hQcont : Continuous Q := by
    dsimp only [Q]
    exact hPcont.sub continuous_const
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
    exact ((hzcont.sub hPolyCont.continuousAt).mul
      hMcont.continuousAt |>.mul hMcont.continuousAt).continuousWithinAt
  have hFcont : ContinuousOn F (Icc t (t + H)) := by
    intro u hu
    have huT : T ≤ u := ht.1.trans hu.1
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
          selbergSqrtZetaShortDirichletPolynomialIntegral H N X t -
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
    dsimp only [selbergSqrtZetaShortDirichletPolynomialIntegral, Q, P]
    ring
  have hEIntegral :
      ‖∫ u in t..t + H, E u‖ ≤
        4 * C * H * X / Real.sqrt T := by
    have hmajor := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t) (b := t + H)
      (C := 4 * C * X / Real.sqrt T)
      (f := E) (fun u hu => by
        rw [uIoc_of_le htt] at hu
        exact hEpoint u ⟨hu.1.le, hu.2⟩)
    calc
      ‖∫ u in t..t + H, E u‖ ≤
          (4 * C * X / Real.sqrt T) * |t + H - t| := hmajor
      _ = 4 * C * H * X / Real.sqrt T := by
        rw [abs_of_nonneg (by linarith : 0 ≤ t + H - t)]
        ring
  have htriangle :
      H ≤ ‖∫ u in t..t + H, F u‖ +
          ‖selbergSqrtZetaShortDirichletPolynomialIntegral H N X t‖ +
            ‖∫ u in t..t + H, E u‖ := by
    calc
      H = ‖(H : ℂ)‖ := by
        rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hH]
      _ = ‖(∫ u in t..t + H, F u) -
          selbergSqrtZetaShortDirichletPolynomialIntegral H N X t -
            ∫ u in t..t + H, E u‖ := congrArg norm hintegralIdentity
      _ ≤ ‖(∫ u in t..t + H, F u) -
          selbergSqrtZetaShortDirichletPolynomialIntegral H N X t‖ +
            ‖∫ u in t..t + H, E u‖ := norm_sub_le _ _
      _ ≤ (‖∫ u in t..t + H, F u‖ +
          ‖selbergSqrtZetaShortDirichletPolynomialIntegral H N X t‖) +
            ‖∫ u in t..t + H, E u‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
  have hnormIntegral := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := F) htt
  have hnormEq :
      (∫ u in t..t + H, ‖F u‖) =
        selbergSqrtZetaAbsShortIntegral X H t := by
    dsimp only [selbergSqrtZetaAbsShortIntegral]
    apply intervalIntegral.integral_congr
    intro u _hu
    dsimp only [F, M]
    exact
      (abs_selbergSqrtZetaMollifiedHardyZ_eq_norm_zeta_mul_mollifier_sq
        X u).symm
  rw [hnormEq] at hnormIntegral
  have htriangle' :
      H ≤ ‖∫ u in t..t + H, F u‖ +
          ‖selbergSqrtZetaShortDirichletPolynomialIntegral H
            (firstZetaApproximationCutoff T) X t‖ +
            ‖∫ u in t..t + H, E u‖ := by
    simpa only [N] using htriangle
  calc
    H -
          ‖selbergSqrtZetaShortDirichletPolynomialIntegral H
            (firstZetaApproximationCutoff T) X t‖ -
          4 * C * H * X / Real.sqrt T ≤
        ‖∫ u in t..t + H, F u‖ := by
      linarith [htriangle', hEIntegral]
    _ ≤ selbergSqrtZetaAbsShortIntegral X H t := hnormIntegral

/-- The preceding lower bound in the exact polynomial notation consumed by
the square-root-zeta mean-square and bad-window estimates. -/
theorem exists_selbergSqrtZetaAbsShortIntegral_ge_sub_mollifiedPolynomial :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H t : ℝ,
        T0 ≤ T → 0 ≤ H →
        t ∈ Icc T (2 * T - H) →
          H -
              ‖selbergSqrtZetaMollifiedShortDirichletPolynomial H
                (firstZetaApproximationCutoff T) X t‖ -
              4 * C * H * X / Real.sqrt T ≤
            selbergSqrtZetaAbsShortIntegral X H t := by
  obtain ⟨C, T0, hC, hT0, hmain⟩ :=
    exists_selbergSqrtZetaAbsShortIntegral_ge_sub_shortDirichlet
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro X hX T H t hT hH ht
  simpa only [selbergSqrtZetaShortDirichletPolynomialIntegral_eq] using
    hmain X hX T H t hT hH ht

end HardyTheorem
