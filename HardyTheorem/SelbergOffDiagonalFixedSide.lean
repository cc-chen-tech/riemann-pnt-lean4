import HardyTheorem.SelbergOffDiagonalGapReindex
import HardyTheorem.SelbergGaussianHarmonicSum

namespace HardyTheorem

/-! # The fixed-side bracket in Selberg's off-diagonal estimate. -/

theorem selberg_reciprocal_square_gap_weight_le
    {A B L V : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (hL : 0 < L) (hV : 0 < V) (hgap : B * L < A * V) :
    (L * V)⁻¹ * (A ^ 2 / L ^ 2 - B ^ 2 / V ^ 2)⁻¹ ≤
      L / (A * (A * V - B * L)) := by
  let D := A ^ 2 / L ^ 2 - B ^ 2 / V ^ 2
  let R := A * (A * V - B * L) / (L ^ 2 * V)
  have hR : R ≤ D := by
    dsimp [R, D]
    exact selberg_difference_of_squares_gap_le hA.le hB hL hV hgap.le
  have hR0 : 0 < R := by
    dsimp [R]
    exact div_pos (mul_pos hA (sub_pos.mpr hgap)) (mul_pos (sq_pos_of_pos hL) hV)
  have hD0 : 0 < D := hR0.trans_le hR
  have hLV0 : 0 < L * V := mul_pos hL hV
  have hprod : (L * V) * R ≤ (L * V) * D :=
    mul_le_mul_of_nonneg_left hR hLV0.le
  calc
    (L * V)⁻¹ * (A ^ 2 / L ^ 2 - B ^ 2 / V ^ 2)⁻¹ =
        1 / ((L * V) * D) := by dsimp [D]; field_simp
    _ ≤ 1 / ((L * V) * R) :=
      one_div_le_one_div_of_le (mul_pos hLV0 hR0) hprod
    _ = L / (A * (A * V - B * L)) := by
      dsimp [R]
      field_simp [hA.ne', hL.ne', hV.ne', (sub_pos.mpr hgap).ne']

theorem selberg_nat_reciprocal_square_gap_weight_le
    {m n kappa lambda mu nu : ℕ}
    (hm : 1 ≤ m) (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda)
    (hmu : 1 ≤ mu) (hnu : 1 ≤ nu)
    (hgap : n * lambda * mu < m * kappa * nu) :
    (((lambda * nu : ℕ) : ℝ))⁻¹ *
        ((((m * kappa : ℕ) : ℝ) ^ 2 / (lambda : ℝ) ^ 2 -
          ((n * mu : ℕ) : ℝ) ^ 2 / (nu : ℝ) ^ 2))⁻¹ ≤
      (lambda : ℝ) /
        (((m * kappa : ℕ) : ℝ) *
          ((m * kappa * nu - n * lambda * mu : ℕ) : ℝ)) := by
  have hA : 0 < ((m * kappa : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hm hkappa
  have hB : 0 ≤ ((n * mu : ℕ) : ℝ) := Nat.cast_nonneg _
  have hL : 0 < (lambda : ℝ) := by exact_mod_cast hlambda
  have hV : 0 < (nu : ℝ) := by exact_mod_cast hnu
  have hgapReal : ((n * mu : ℕ) : ℝ) * (lambda : ℝ) <
      ((m * kappa : ℕ) : ℝ) * (nu : ℝ) := by
    norm_num
    exact_mod_cast (by simpa [mul_assoc, mul_comm, mul_left_comm] using hgap)
  have h := selberg_reciprocal_square_gap_weight_le
    hA hB hL hV hgapReal
  convert h using 1
  · push_cast
    rfl
  · rw [Nat.cast_sub hgap.le]
    push_cast
    ring

theorem selberg_nat_square_gap_pos
    {m n kappa lambda mu nu : ℕ}
    (hm : 1 ≤ m) (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda)
    (hnu : 1 ≤ nu) (hgap : n * lambda * mu < m * kappa * nu) :
    0 < ((m * kappa : ℕ) : ℝ) ^ 2 / (lambda : ℝ) ^ 2 -
      ((n * mu : ℕ) : ℝ) ^ 2 / (nu : ℝ) ^ 2 := by
  let A : ℝ := ((m * kappa : ℕ) : ℝ)
  let B : ℝ := ((n * mu : ℕ) : ℝ)
  let L : ℝ := lambda
  let V : ℝ := nu
  have hA : 0 < A := by dsimp [A]; exact_mod_cast Nat.mul_pos hm hkappa
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hL : 0 < L := by dsimp [L]; exact_mod_cast hlambda
  have hV : 0 < V := by dsimp [V]; exact_mod_cast hnu
  have hgapReal : B * L < A * V := by
    dsimp [A, B, L, V]
    push_cast
    exact_mod_cast (by simpa [mul_assoc, mul_comm, mul_left_comm] using hgap)
  have hLower := selberg_difference_of_squares_gap_le
    hA.le hB hL hV hgapReal.le
  have hLower0 : 0 < A * (A * V - B * L) / (L ^ 2 * V) :=
    div_pos (mul_pos hA (sub_pos.mpr hgapReal)) (mul_pos (sq_pos_of_pos hL) hV)
  exact hLower0.trans_le (by simpa only [A, B, L, V] using hLower)

noncomputable def selbergFixedSideSquareSum
    (a : ℝ) (m kappa lambda mu nu : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1
      (selbergPositiveGapCount (m * kappa * nu) (lambda * mu)),
    Real.exp (-a * (m : ℝ) ^ 2) *
      ((((lambda * nu : ℕ) : ℝ))⁻¹ *
        ((((m * kappa : ℕ) : ℝ) ^ 2 / (lambda : ℝ) ^ 2 -
          ((n * mu : ℕ) : ℝ) ^ 2 / (nu : ℝ) ^ 2))⁻¹)

theorem selbergFixedSideSquareSum_nonneg
    {a : ℝ} {m kappa lambda mu nu : ℕ}
    (hm : 1 ≤ m) (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda)
    (hmu : 1 ≤ mu) (hnu : 1 ≤ nu) :
    0 ≤ selbergFixedSideSquareSum a m kappa lambda mu nu := by
  unfold selbergFixedSideSquareSum
  apply Finset.sum_nonneg
  intro n hn
  have hd : 1 ≤ lambda * mu := Nat.mul_pos hlambda hmu
  have hgap : n * lambda * mu < m * kappa * nu :=
    by simpa only [mul_assoc] using
      ((selberg_positive_gap_admissible_iff hd).mpr hn |>.2)
  have hD := selberg_nat_square_gap_pos hm hkappa hlambda hnu hgap
  exact mul_nonneg (Real.exp_pos _).le
    (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (inv_nonneg.mpr hD.le))

theorem selberg_gap_factor_le_two_dampedBracket
    {a X ell : ℝ} {d : ℕ} (hd : 1 ≤ d) (n : ℕ)
    (hell : ell ≤ 2 * Real.log (((n + 1 : ℕ) : ℝ) * X)) :
    selbergGaussianHarmonic a n *
        (1 + (d : ℝ)⁻¹ * (1 + ell)) ≤
      2 * selbergOffDiagonalDampedBracket a X (d : ℝ) n := by
  let H := selbergGaussianHarmonic a n
  let D : ℝ := (d : ℝ)⁻¹
  let L := Real.log (((n + 1 : ℕ) : ℝ) * X)
  have hH0 : 0 ≤ H := by
    dsimp [H]
    unfold selbergGaussianHarmonic
    positivity
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hdReal : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hD1 : D ≤ 1 := by
    dsimp [D]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hdReal
    norm_num at h
    exact h
  have hDH : D * H ≤ H := by
    simpa using mul_le_mul_of_nonneg_right hD1 hH0
  have hEllH : ell * H ≤ (2 * L) * H :=
    mul_le_mul_of_nonneg_right (by simpa only [L] using hell) hH0
  have hDEllH : D * (ell * H) ≤ D * ((2 * L) * H) :=
    mul_le_mul_of_nonneg_left hEllH hD0
  unfold selbergOffDiagonalDampedBracket selbergGaussianLogHarmonic
  change H * (1 + D * (1 + ell)) ≤ 2 * (H + D * (L * H))
  calc
    H * (1 + D * (1 + ell)) = H + D * H + D * (ell * H) := by ring
    _ ≤ H + H + D * ((2 * L) * H) := by gcongr
    _ = 2 * (H + D * (L * H)) := by ring

theorem selberg_fixed_m_gap_majorant_le
    {a : ℝ} {m kappa lambda mu nu X : ℕ}
    (hm : 1 ≤ m) (hlambda : 1 ≤ lambda) (hmu : 1 ≤ mu)
    (hkappaX : kappa ≤ X) (hnuX : nu ≤ X) (hX : 1 ≤ X) :
    selbergGaussianHarmonic a (m - 1) *
        (1 + ((lambda * mu : ℕ) : ℝ)⁻¹ *
          (1 + Real.log (selbergPositiveGapCount
            (m * kappa * nu) (lambda * mu) : ℝ))) ≤
      2 * selbergOffDiagonalDampedBracket
        a (X : ℝ) ((lambda * mu : ℕ) : ℝ) (m - 1) := by
  apply selberg_gap_factor_le_two_dampedBracket (Nat.mul_pos hlambda hmu) (m - 1)
  simpa [Nat.sub_add_cancel hm] using
    (selberg_log_positive_gap_count_le_two_log_mul
      hm hlambda hmu hkappaX hnuX hX)

theorem selberg_fixed_side_square_sum_le_dampedBracket
    {a : ℝ} {m kappa lambda mu nu X : ℕ}
    (hm : 1 ≤ m) (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda)
    (hmu : 1 ≤ mu) (hnu : 1 ≤ nu)
    (hkappaX : kappa ≤ X) (hnuX : nu ≤ X) (hX : 1 ≤ X) :
    selbergFixedSideSquareSum a m kappa lambda mu nu ≤
      2 * ((lambda : ℝ) / (kappa : ℝ)) *
        selbergOffDiagonalDampedBracket
          a (X : ℝ) ((lambda * mu : ℕ) : ℝ) (m - 1) := by
  let K := m * kappa * nu
  let d := lambda * mu
  let H := selbergGaussianHarmonic a (m - 1)
  let C : ℝ := (lambda : ℝ) / (kappa : ℝ)
  have hK : 1 ≤ K := by
    dsimp [K]
    exact Nat.mul_pos (Nat.mul_pos hm hkappa) hnu
  have hd : 1 ≤ d := by
    dsimp [d]
    exact Nat.mul_pos hlambda hmu
  have hH0 : 0 ≤ H := by
    dsimp [H]
    unfold selbergGaussianHarmonic
    positivity
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hsum : selbergFixedSideSquareSum a m kappa lambda mu nu ≤
      C * H * selbergPositiveGapReciprocalSum K d := by
    unfold selbergFixedSideSquareSum selbergPositiveGapReciprocalSum
    change (∑ n ∈ Finset.Icc 1 (selbergPositiveGapCount K d),
      Real.exp (-a * (m : ℝ) ^ 2) *
        ((((lambda * nu : ℕ) : ℝ))⁻¹ *
          ((((m * kappa : ℕ) : ℝ) ^ 2 / (lambda : ℝ) ^ 2 -
            ((n * mu : ℕ) : ℝ) ^ 2 / (nu : ℝ) ^ 2))⁻¹)) ≤ _
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 (selbergPositiveGapCount K d),
          C * H * (((K - n * d : ℕ) : ℝ))⁻¹ := by
        apply Finset.sum_le_sum
        intro n hn
        have hgap : n * lambda * mu < m * kappa * nu := by
          have := (selberg_positive_gap_admissible_iff hd).mpr hn |>.2
          simpa only [K, d, mul_assoc] using this
        have hpair := selberg_nat_reciprocal_square_gap_weight_le
          hm hkappa hlambda hmu hnu hgap
        have hweighted :
            Real.exp (-a * (m : ℝ) ^ 2) *
                ((((lambda * nu : ℕ) : ℝ))⁻¹ *
                  ((((m * kappa : ℕ) : ℝ) ^ 2 / (lambda : ℝ) ^ 2 -
                    ((n * mu : ℕ) : ℝ) ^ 2 / (nu : ℝ) ^ 2))⁻¹) ≤
              Real.exp (-a * (m : ℝ) ^ 2) *
                ((lambda : ℝ) /
                  (((m * kappa : ℕ) : ℝ) *
                    ((m * kappa * nu - n * lambda * mu : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hpair (Real.exp_pos _).le
        calc
          Real.exp (-a * (m : ℝ) ^ 2) *
              ((((lambda * nu : ℕ) : ℝ))⁻¹ *
                ((((m * kappa : ℕ) : ℝ) ^ 2 / (lambda : ℝ) ^ 2 -
                  ((n * mu : ℕ) : ℝ) ^ 2 / (nu : ℝ) ^ 2))⁻¹) ≤
              Real.exp (-a * (m : ℝ) ^ 2) * (lambda : ℝ) /
                  (((m * kappa : ℕ) : ℝ) *
                  ((m * kappa * nu - n * lambda * mu : ℕ) : ℝ)) := by
            simpa only [mul_div_assoc] using hweighted
          _ = C * H * (((K - n * d : ℕ) : ℝ))⁻¹ := by
            dsimp [C, H, K, d]
            unfold selbergGaussianHarmonic
            rw [Nat.sub_add_cancel hm]
            push_cast
            field_simp [show (m : ℝ) ≠ 0 by positivity,
              show (kappa : ℝ) ≠ 0 by positivity]
            ring_nf
      _ = C * H *
          (∑ n ∈ Finset.Icc 1 (selbergPositiveGapCount K d),
            (((K - n * d : ℕ) : ℝ))⁻¹) := by
        rw [Finset.mul_sum]
  have hgapBound := selberg_positive_gap_reciprocal_sum_le hK hd
  have hfixed := selberg_fixed_m_gap_majorant_le
    (a := a) hm hlambda hmu hkappaX hnuX hX
  calc
    selbergFixedSideSquareSum a m kappa lambda mu nu ≤
        C * H * selbergPositiveGapReciprocalSum K d := hsum
    _ ≤ C * (H * (1 + (d : ℝ)⁻¹ *
          (1 + Real.log (selbergPositiveGapCount K d : ℝ)))) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hgapBound hH0) hC0
    _ ≤ C * (2 * selbergOffDiagonalDampedBracket
          a (X : ℝ) (d : ℝ) (m - 1)) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [H, d] using hfixed) hC0
    _ = 2 * ((lambda : ℝ) / (kappa : ℝ)) *
        selbergOffDiagonalDampedBracket
          a (X : ℝ) ((lambda * mu : ℕ) : ℝ) (m - 1) := by
      dsimp [C, d]
      ring

theorem summable_selbergFixedSideSquareSum_add_one
    {a : ℝ} (ha0 : 0 < a)
    {kappa lambda mu nu X : ℕ}
    (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda)
    (hmu : 1 ≤ mu) (hnu : 1 ≤ nu)
    (hkappaX : kappa ≤ X) (hnuX : nu ≤ X) (hX : 1 ≤ X) :
    Summable (fun n : ℕ =>
      selbergFixedSideSquareSum a (n + 1) kappa lambda mu nu) := by
  let C : ℝ := 2 * ((lambda : ℝ) / (kappa : ℝ))
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hXReal : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hbracket := summable_selbergOffDiagonalDampedBracket_of_pos
    (a := a) (X := (X : ℝ)) (d := ((lambda * mu : ℕ) : ℝ)) ha0 hXReal
  have hmajor : Summable (fun n : ℕ => C *
      selbergOffDiagonalDampedBracket
        a (X : ℝ) ((lambda * mu : ℕ) : ℝ) n) := hbracket.mul_left C
  refine Summable.of_nonneg_of_le ?_ ?_ hmajor
  · intro n
    exact selbergFixedSideSquareSum_nonneg
      (Nat.le_add_left 1 n) hkappa hlambda hmu hnu
  · intro n
    simpa only [C, Nat.add_sub_cancel] using
      (selberg_fixed_side_square_sum_le_dampedBracket
        (a := a) (m := n + 1) (kappa := kappa) (lambda := lambda)
        (mu := mu) (nu := nu) (X := X)
        (Nat.le_add_left 1 n) hkappa hlambda hmu hnu hkappaX hnuX hX)

theorem tsum_selbergFixedSideSquareSum_add_one_le
    {a : ℝ} (ha0 : 0 < a)
    {kappa lambda mu nu X : ℕ}
    (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda)
    (hmu : 1 ≤ mu) (hnu : 1 ≤ nu)
    (hkappaX : kappa ≤ X) (hnuX : nu ≤ X) (hX : 1 ≤ X) :
    (∑' n : ℕ, selbergFixedSideSquareSum a (n + 1) kappa lambda mu nu) ≤
      2 * ((lambda : ℝ) / (kappa : ℝ)) *
        (∑' n : ℕ, selbergOffDiagonalDampedBracket
          a (X : ℝ) ((lambda * mu : ℕ) : ℝ) n) := by
  let C : ℝ := 2 * ((lambda : ℝ) / (kappa : ℝ))
  have hXReal : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hbracket := summable_selbergOffDiagonalDampedBracket_of_pos
    (a := a) (X := (X : ℝ)) (d := ((lambda * mu : ℕ) : ℝ)) ha0 hXReal
  have hmajor : Summable (fun n : ℕ => C *
      selbergOffDiagonalDampedBracket
        a (X : ℝ) ((lambda * mu : ℕ) : ℝ) n) := hbracket.mul_left C
  have hsum := summable_selbergFixedSideSquareSum_add_one
    ha0 hkappa hlambda hmu hnu hkappaX hnuX hX
  calc
    (∑' n : ℕ, selbergFixedSideSquareSum a (n + 1) kappa lambda mu nu) ≤
        ∑' n : ℕ, C * selbergOffDiagonalDampedBracket
          a (X : ℝ) ((lambda * mu : ℕ) : ℝ) n :=
      hsum.tsum_le_tsum
        (fun n => by
          simpa only [C, Nat.add_sub_cancel] using
            (selberg_fixed_side_square_sum_le_dampedBracket
              (a := a) (m := n + 1) (kappa := kappa) (lambda := lambda)
              (mu := mu) (nu := nu) (X := X)
              (Nat.le_add_left 1 n) hkappa hlambda hmu hnu hkappaX hnuX hX))
        hmajor
    _ = C * (∑' n : ℕ, selbergOffDiagonalDampedBracket
          a (X : ℝ) ((lambda * mu : ℕ) : ℝ) n) := by rw [tsum_mul_left]
    _ = _ := rfl

end HardyTheorem
