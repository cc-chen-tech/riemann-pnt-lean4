import HardyTheorem.SelbergDiagonalTonelliReindex
import HardyTheorem.SelbergSArithmeticFinalBound

open Complex

namespace HardyTheorem

/-! # The two signed arithmetic main terms in Selberg's diagonal sum. -/

noncomputable def selbergDiagonalSZeroCoefficient
    (delta x theta : ℝ) : ℝ :=
  (Real.sqrt Real.pi / 2) / theta * x ^ (-theta) *
    (2 * Real.pi * Real.sin delta) ^ (-(1 / 2 : ℝ))

noncomputable def selbergDiagonalSThetaCoefficient
    (delta theta : ℝ) : ℝ :=
  (selbergDiagonalK1 theta / theta) *
    (2 * Real.pi * Real.sin delta) ^ ((theta - 1) / 2)

noncomputable def selbergDiagonalArithmeticMain
    (delta x theta : ℝ) (X : ℕ) : ℂ :=
  (selbergDiagonalSZeroCoefficient delta x theta : ℂ) *
      selbergArithmeticDiagonalSum X 0 +
    (selbergDiagonalSThetaCoefficient delta theta : ℂ) *
      selbergArithmeticDiagonalSum X theta

theorem exists_norm_selbergDiagonalArithmeticMain_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta x theta : ℝ),
        0 < theta → theta ≤ 1 / 2 → Real.exp 1 ≤ (X : ℝ) →
        ‖selbergDiagonalArithmeticMain delta x theta X‖ ≤
          |selbergDiagonalSZeroCoefficient delta x theta| *
              (C / Real.log (X : ℝ)) +
            |selbergDiagonalSThetaCoefficient delta theta| *
              (C * ((X : ℝ) ^ (2 * theta)) /
                Real.log (X : ℝ)) := by
  rcases exists_norm_selbergArithmeticDiagonalSum_le with ⟨C, hC, hS⟩
  refine ⟨C, hC, ?_⟩
  intro X delta x theta htheta0 hthetaHalf hX
  have hS0 : ‖selbergArithmeticDiagonalSum X 0‖ ≤
      C / Real.log (X : ℝ) := by
    simpa only [Real.rpow_zero, mul_zero, one_mul, mul_one] using
      hS X 0 (by norm_num) (by norm_num) hX
  have hStheta : ‖selbergArithmeticDiagonalSum X theta‖ ≤
      C * ((X : ℝ) ^ (2 * theta)) / Real.log (X : ℝ) :=
    hS X theta htheta0.le (hthetaHalf.trans (by norm_num)) hX
  unfold selbergDiagonalArithmeticMain
  calc
    ‖(selbergDiagonalSZeroCoefficient delta x theta : ℂ) *
          selbergArithmeticDiagonalSum X 0 +
        (selbergDiagonalSThetaCoefficient delta theta : ℂ) *
          selbergArithmeticDiagonalSum X theta‖ ≤
      ‖(selbergDiagonalSZeroCoefficient delta x theta : ℂ) *
          selbergArithmeticDiagonalSum X 0‖ +
        ‖(selbergDiagonalSThetaCoefficient delta theta : ℂ) *
          selbergArithmeticDiagonalSum X theta‖ := norm_add_le _ _
    _ = |selbergDiagonalSZeroCoefficient delta x theta| *
          ‖selbergArithmeticDiagonalSum X 0‖ +
        |selbergDiagonalSThetaCoefficient delta theta| *
          ‖selbergArithmeticDiagonalSum X theta‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |selbergDiagonalSZeroCoefficient delta x theta| *
          (C / Real.log (X : ℝ)) +
        |selbergDiagonalSThetaCoefficient delta theta| *
          (C * ((X : ℝ) ^ (2 * theta)) /
            Real.log (X : ℝ)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hS0 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hStheta (abs_nonneg _))

noncomputable def selbergDiagonalGaussianParameter
    (delta : ℝ) (kappa mu q : ℕ) : ℝ :=
  (2 * Real.pi * Real.sin delta) *
    ((((kappa * mu : ℕ) : ℝ) / (q : ℝ)) ^ 2)

theorem selbergDiagonalGaussianParameter_pos
    {delta : ℝ} {kappa mu q : ℕ}
    (hdelta0 : 0 < delta) (hdeltaPi : delta < Real.pi)
    (hkappa : 0 < kappa) (hmu : 0 < mu) (hq : 0 < q) :
    0 < selbergDiagonalGaussianParameter delta kappa mu q := by
  unfold selbergDiagonalGaussianParameter
  have hsin : 0 < Real.sin delta :=
    Real.sin_pos_of_pos_of_lt_pi hdelta0 hdeltaPi
  positivity

theorem selbergDiagonalGaussianParameter_rpow_neg_half
    {delta : ℝ} {kappa mu q : ℕ}
    (hdelta0 : 0 < delta) (hdeltaPi : delta < Real.pi)
    (hkappa : 0 < kappa) (hmu : 0 < mu) (hq : 0 < q) :
    selbergDiagonalGaussianParameter delta kappa mu q ^
        (-(1 / 2 : ℝ)) =
      (2 * Real.pi * Real.sin delta) ^ (-(1 / 2 : ℝ)) *
        ((q : ℝ) / ((kappa * mu : ℕ) : ℝ)) := by
  let c : ℝ := 2 * Real.pi * Real.sin delta
  let r : ℝ := ((kappa * mu : ℕ) : ℝ) / (q : ℝ)
  have hc : 0 < c := by
    dsimp [c]
    have hsin := Real.sin_pos_of_pos_of_lt_pi hdelta0 hdeltaPi
    positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hrinv : r⁻¹ = (q : ℝ) / ((kappa * mu : ℕ) : ℝ) := by
    dsimp [r]
    push_cast
    field_simp [show (kappa : ℝ) ≠ 0 by positivity,
      show (mu : ℝ) ≠ 0 by positivity, show (q : ℝ) ≠ 0 by positivity]
  change (c * r ^ 2) ^ (-(1 / 2 : ℝ)) =
    c ^ (-(1 / 2 : ℝ)) *
      ((q : ℝ) / ((kappa * mu : ℕ) : ℝ))
  rw [Real.mul_rpow hc.le (sq_nonneg r)]
  have hsquare : (r ^ 2) ^ (-(1 / 2 : ℝ)) = r⁻¹ := by
    rw [← Real.rpow_natCast r 2]
    rw [← Real.rpow_mul hr.le]
    norm_num
    rw [Real.rpow_neg_one]
  rw [hsquare, hrinv]

theorem selbergDiagonalGaussianParameter_rpow_theta_half
    {delta theta : ℝ} {kappa mu q : ℕ}
    (hdelta0 : 0 < delta) (hdeltaPi : delta < Real.pi)
    (hkappa : 0 < kappa) (hmu : 0 < mu) (hq : 0 < q) :
    selbergDiagonalGaussianParameter delta kappa mu q ^
        ((theta - 1) / 2) =
      (2 * Real.pi * Real.sin delta) ^ ((theta - 1) / 2) *
        ((q : ℝ) / ((kappa * mu : ℕ) : ℝ)) ^ (1 - theta) := by
  let c : ℝ := 2 * Real.pi * Real.sin delta
  let r : ℝ := ((kappa * mu : ℕ) : ℝ) / (q : ℝ)
  have hc : 0 < c := by
    dsimp [c]
    have hsin := Real.sin_pos_of_pos_of_lt_pi hdelta0 hdeltaPi
    positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hrinv : r⁻¹ = (q : ℝ) / ((kappa * mu : ℕ) : ℝ) := by
    dsimp [r]
    push_cast
    field_simp [show (kappa : ℝ) ≠ 0 by positivity,
      show (mu : ℝ) ≠ 0 by positivity, show (q : ℝ) ≠ 0 by positivity]
  change (c * r ^ 2) ^ ((theta - 1) / 2) =
    c ^ ((theta - 1) / 2) *
      ((q : ℝ) / ((kappa * mu : ℕ) : ℝ)) ^ (1 - theta)
  rw [Real.mul_rpow hc.le (sq_nonneg r)]
  have hsquare : (r ^ 2) ^ ((theta - 1) / 2) =
      r ^ (theta - 1) := by
    rw [← Real.rpow_natCast r 2]
    rw [← Real.rpow_mul hr.le]
    congr 1
    ring
  rw [hsquare]
  rw [show theta - 1 = -(1 - theta) by ring]
  rw [Real.rpow_neg_eq_inv_rpow, hrinv]

theorem selbergDiagonalTitchMain_gaussianParameter_eq
    {delta x theta : ℝ} {kappa mu q : ℕ}
    (hdelta0 : 0 < delta) (hdeltaPi : delta < Real.pi)
    (hkappa : 0 < kappa) (hmu : 0 < mu) (hq : 0 < q) :
    selbergDiagonalTitchMain
        (selbergDiagonalGaussianParameter delta kappa mu q) x theta =
      selbergDiagonalSZeroCoefficient delta x theta *
          ((q : ℝ) / ((kappa * mu : ℕ) : ℝ)) +
        selbergDiagonalSThetaCoefficient delta theta *
          (((q : ℝ) / ((kappa * mu : ℕ) : ℝ)) ^ (1 - theta)) := by
  unfold selbergDiagonalTitchMain selbergDiagonalMainCoefficient
  rw [selbergDiagonalGaussianParameter_rpow_neg_half
      hdelta0 hdeltaPi hkappa hmu hq,
    selbergDiagonalGaussianParameter_rpow_theta_half
      hdelta0 hdeltaPi hkappa hmu hq]
  unfold selbergDiagonalSZeroCoefficient selbergDiagonalSThetaCoefficient
  ring

theorem selbergDiagonalRatio_rpow_eq_cpow_factors
    {theta : ℝ} {kappa mu q : ℕ}
    (hkappa : 0 < kappa) (hmu : 0 < mu) (hq : 0 < q) :
    (((((q : ℝ) / ((kappa * mu : ℕ) : ℝ)) ^ (1 - theta) : ℝ) : ℂ)) =
      ((((q : ℝ) ^ (1 - theta) : ℝ) : ℂ)) *
        (kappa : ℂ) ^ (-((1 - theta : ℝ) : ℂ)) *
        (mu : ℂ) ^ (-((1 - theta : ℝ) : ℂ)) := by
  have hk0 : 0 ≤ (kappa : ℝ) := Nat.cast_nonneg _
  have hm0 : 0 ≤ (mu : ℝ) := Nat.cast_nonneg _
  have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  have hkne : (kappa : ℝ) ^ (1 - theta) ≠ 0 := by positivity
  have hmne : (mu : ℝ) ^ (1 - theta) ≠ 0 := by positivity
  have hreal :
      ((q : ℝ) / ((kappa * mu : ℕ) : ℝ)) ^ (1 - theta) =
        (q : ℝ) ^ (1 - theta) *
          (kappa : ℝ) ^ (-(1 - theta)) *
          (mu : ℝ) ^ (-(1 - theta)) := by
    rw [Real.div_rpow hq0 (Nat.cast_nonneg _) (1 - theta)]
    push_cast
    rw [Real.mul_rpow hk0 hm0]
    rw [Real.rpow_neg hk0, Real.rpow_neg hm0]
    field_simp [hkne, hmne]
  rw [hreal]
  push_cast
  rw [Complex.ofReal_cpow hk0, Complex.ofReal_cpow hm0]
  norm_num

noncomputable def selbergDiagonalMollifierProduct
    (X kappa nu mu lambda : ℕ) : ℂ :=
  (selbergSqrtZetaTaperedCoeff X kappa : ℂ) *
    (selbergSqrtZetaTaperedCoeff X nu : ℂ) *
    (selbergSqrtZetaTaperedCoeff X mu : ℂ) *
    (selbergSqrtZetaTaperedCoeff X lambda : ℂ)

noncomputable def selbergDiagonalPhysicalMainTerm
    (delta x theta : ℝ) (X kappa nu mu lambda q : ℕ) : ℂ :=
  selbergDiagonalMollifierProduct X kappa nu mu lambda /
      ((nu : ℂ) * (lambda : ℂ)) *
    (selbergDiagonalTitchMain
      (selbergDiagonalGaussianParameter delta kappa mu q) x theta : ℂ)

theorem selbergDiagonalPhysicalMainTerm_eq
    {delta x theta : ℝ} {X kappa nu mu lambda q : ℕ}
    (hdelta0 : 0 < delta) (hdeltaPi : delta < Real.pi)
    (hkappa : 0 < kappa) (hnu : 0 < nu) (hmu : 0 < mu)
    (hlambda : 0 < lambda) (hq : 0 < q) :
    selbergDiagonalPhysicalMainTerm delta x theta X kappa nu mu lambda q =
      (selbergDiagonalSZeroCoefficient delta x theta : ℂ) *
          (((((q : ℕ) : ℝ) ^ (1 - (0 : ℝ)) : ℝ) : ℂ) *
            selbergArithmeticPairTerm X 0 kappa nu *
            selbergArithmeticPairTerm X 0 mu lambda) +
        (selbergDiagonalSThetaCoefficient delta theta : ℂ) *
          (((((q : ℕ) : ℝ) ^ (1 - theta) : ℝ) : ℂ) *
            selbergArithmeticPairTerm X theta kappa nu *
            selbergArithmeticPairTerm X theta mu lambda) := by
  have hmain := selbergDiagonalTitchMain_gaussianParameter_eq
    (x := x) (theta := theta) hdelta0 hdeltaPi hkappa hmu hq
  have hrtheta := selbergDiagonalRatio_rpow_eq_cpow_factors
    (theta := theta) hkappa hmu hq
  have hmainC := congrArg (fun r : ℝ => (r : ℂ)) hmain
  push_cast at hmainC hrtheta
  have hr0C :
      (q : ℂ) / ((kappa : ℂ) * (mu : ℂ)) =
        (q : ℂ) * (kappa : ℂ)⁻¹ * (mu : ℂ)⁻¹ := by
    rw [div_eq_mul_inv, mul_inv_rev]
    ring
  have hkZero :
      (kappa : ℂ) ^ (-((1 - (0 : ℝ) : ℝ) : ℂ)) = (kappa : ℂ)⁻¹ := by
    norm_num [Complex.cpow_neg_one]
  have hnZero :
      (nu : ℂ) ^ (-((1 - (0 : ℝ) : ℝ) : ℂ)) = (nu : ℂ)⁻¹ := by
    norm_num [Complex.cpow_neg_one]
  have hmZero :
      (mu : ℂ) ^ (-((1 - (0 : ℝ) : ℝ) : ℂ)) = (mu : ℂ)⁻¹ := by
    norm_num [Complex.cpow_neg_one]
  have hlZero :
      (lambda : ℂ) ^ (-((1 - (0 : ℝ) : ℝ) : ℂ)) = (lambda : ℂ)⁻¹ := by
    norm_num [Complex.cpow_neg_one]
  have hqZero :
      ((((q : ℝ) ^ (1 - (0 : ℝ)) : ℝ) : ℂ)) = (q : ℂ) := by
    norm_num
  unfold selbergDiagonalPhysicalMainTerm
  rw [hmainC]
  rw [hr0C, hrtheta]
  push_cast
  unfold selbergDiagonalMollifierProduct selbergArithmeticPairTerm
  rw [hkZero, hnZero, hmZero, hlZero]
  rw [hqZero]
  have hexp : (-(1 - (theta : ℂ))) = -((1 - theta : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hexp]
  field_simp [show (nu : ℂ) ≠ 0 by exact_mod_cast hnu.ne',
    show (lambda : ℂ) ≠ 0 by exact_mod_cast hlambda.ne']

noncomputable def selbergDiagonalPhysicalMainPairTerm
    (delta x theta : ℝ) (X : ℕ)
    (p q : selbergTaperIndex X × selbergTaperIndex X) : ℂ :=
  selbergDiagonalPhysicalMainTerm delta x theta X
    p.1.1 p.2.1 q.1.1 q.2.1 (selbergArithmeticDiagonalGcd p q)

theorem selbergDiagonalPhysicalMainPairTerm_eq
    {delta x theta : ℝ} {X : ℕ}
    (p q : selbergTaperIndex X × selbergTaperIndex X)
    (hdelta0 : 0 < delta) (hdeltaPi : delta < Real.pi) :
    selbergDiagonalPhysicalMainPairTerm delta x theta X p q =
      (selbergDiagonalSZeroCoefficient delta x theta : ℂ) *
          (((((selbergArithmeticDiagonalGcd p q : ℕ) : ℝ) ^
              (1 - (0 : ℝ)) : ℝ) : ℂ) *
            selbergArithmeticPairTerm X 0 p.1.1 p.2.1 *
            selbergArithmeticPairTerm X 0 q.1.1 q.2.1) +
        (selbergDiagonalSThetaCoefficient delta theta : ℂ) *
          (((((selbergArithmeticDiagonalGcd p q : ℕ) : ℝ) ^
              (1 - theta) : ℝ) : ℂ) *
            selbergArithmeticPairTerm X theta p.1.1 p.2.1 *
            selbergArithmeticPairTerm X theta q.1.1 q.2.1) := by
  have hkappa : 0 < p.1.1 := (Finset.mem_Icc.mp p.1.2).1
  have hnu : 0 < p.2.1 := (Finset.mem_Icc.mp p.2.2).1
  have hmu : 0 < q.1.1 := (Finset.mem_Icc.mp q.1.2).1
  have hlambda : 0 < q.2.1 := (Finset.mem_Icc.mp q.2.2).1
  have hg : 0 < selbergArithmeticDiagonalGcd p q := by
    exact Nat.gcd_pos_of_pos_left _ (Nat.mul_pos hkappa hnu)
  exact selbergDiagonalPhysicalMainTerm_eq hdelta0 hdeltaPi
    hkappa hnu hmu hlambda hg

noncomputable def selbergDiagonalPhysicalMainSum
    (delta x theta : ℝ) (X : ℕ) : ℂ :=
  ∑ p : selbergTaperIndex X × selbergTaperIndex X,
    ∑ q : selbergTaperIndex X × selbergTaperIndex X,
      selbergDiagonalPhysicalMainPairTerm delta x theta X p q

theorem selbergDiagonalPhysicalMainSum_eq_arithmeticMain
    {delta x theta : ℝ} {X : ℕ}
    (hdelta0 : 0 < delta) (hdeltaPi : delta < Real.pi) :
    selbergDiagonalPhysicalMainSum delta x theta X =
      selbergDiagonalArithmeticMain delta x theta X := by
  classical
  unfold selbergDiagonalPhysicalMainSum
  simp_rw [selbergDiagonalPhysicalMainPairTerm_eq _ _ hdelta0 hdeltaPi]
  unfold selbergDiagonalArithmeticMain selbergArithmeticDiagonalSum
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

theorem exists_norm_selbergDiagonalPhysicalMainSum_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta x theta : ℝ),
        0 < delta → delta < Real.pi →
        0 < theta → theta ≤ 1 / 2 → Real.exp 1 ≤ (X : ℝ) →
        ‖selbergDiagonalPhysicalMainSum delta x theta X‖ ≤
          |selbergDiagonalSZeroCoefficient delta x theta| *
              (C / Real.log (X : ℝ)) +
            |selbergDiagonalSThetaCoefficient delta theta| *
              (C * ((X : ℝ) ^ (2 * theta)) /
                Real.log (X : ℝ)) := by
  rcases exists_norm_selbergDiagonalArithmeticMain_le with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro X delta x theta hdelta0 hdeltaPi htheta0 hthetaHalf hX
  rw [selbergDiagonalPhysicalMainSum_eq_arithmeticMain hdelta0 hdeltaPi]
  exact hbound X delta x theta htheta0 hthetaHalf hX

end HardyTheorem
