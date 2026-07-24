import PrimeNumberTheorem.RieszDifference
import PrimeNumberTheorem.SecondOrderMovingLeft
import PrimeNumberTheorem.RightHorizontalEdge
import PrimeNumberTheorem.CentralHorizontalEdge
import PrimeNumberTheorem.LeftVerticalEdge

/-!
# Transferring smoothed approximation errors to Chebyshev psi

This module isolates the algebraic step needed after a finite-height
second-order explicit formula supplies approximations to the first Riesz mean.
In particular, callers can use the residue sum minus contour remainder from
`SecondOrderExplicitFormula` as `approx`. The approximation and its error may
both depend on the height parameter `T`.
-/

open Complex
open scoped BigOperators Interval

namespace PrimeNumberTheorem

namespace ExplicitFormulaResidues

/-- Difference, in the `x` variable, of one horizontal second-order contour
edge. -/
noncomputable def secondOrderHorizontalXDifference
    (x y a c T : ℝ) : ℂ :=
  (∫ σ : ℝ in a..c,
      secondOrderExplicitFormulaIntegrand y ((σ : ℂ) + T * I)) -
    ∫ σ : ℝ in a..c,
      secondOrderExplicitFormulaIntegrand x ((σ : ℂ) + T * I)

/-- Difference, in the `x` variable, of the left vertical second-order edge. -/
noncomputable def secondOrderLeftXDifference
    (x y a W : ℝ) : ℂ :=
  (∫ t : ℝ in (-(2 * Real.pi * W))..(2 * Real.pi * W),
      secondOrderExplicitFormulaIntegrand y ((a : ℂ) + t * I)) -
    ∫ t : ℝ in (-(2 * Real.pi * W))..(2 * Real.pi * W),
      secondOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)

/-- The negative-odd left-vertical majorant for the second-order Perron
kernel.  Relative to the first-order API, the extra kernel contributes the
explicit factor `(2N+1)^{-1}`. -/
noncomputable def secondOrderOddVerticalBound (x : ℝ) (N : ℕ) (T : ℝ) : ℝ :=
  (vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
      2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
        Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
      x ^ (-(2 * (N : ℝ) + 1)) / (2 * (N : ℝ) + 1)

/-- On a finite negative-odd vertical segment, the second-order Perron kernel
gains the reciprocal distance of the line from the imaginary axis.  Positivity
of `x` is sufficient, including the endpoint `x = 1` used by the smoothed
transfer theorem. -/
theorem norm_secondOrderExplicitFormulaIntegrand_odd_vertical_le_of_pos
    {x T t : ℝ} {N : ℕ} (hx : 0 < x) (hT : 0 ≤ T) (ht : |t| ≤ T) :
    ‖secondOrderExplicitFormulaIntegrand x
      (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      secondOrderOddVerticalBound x N T := by
  let s : ℂ := ((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I
  let Q : ℝ := vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
    2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
      Real.log (2 * (N : ℝ) + T + 4)) + Real.pi
  have hlog := norm_neg_logDeriv_riemannZeta_odd_vertical_le_of_abs_le
    (N := N) hT ht
  change ‖-logDeriv riemannZeta s‖ ≤ Q at hlog
  have hpow : ‖(x : ℂ) ^ s‖ = x ^ (-(2 * (N : ℝ) + 1)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp [s]
  have hline_one : 1 ≤ ‖s‖ := by
    have hre : 2 * (N : ℝ) + 1 ≤ |s.re| := by
      simp [s]
      have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      rw [abs_of_nonpos (by linarith)]
      linarith
    have habs := Complex.abs_re_le_norm s
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  change ‖explicitFormulaIntegrand x s / s‖ ≤ Q * x ^ (-(2 * (N : ℝ) + 1)) /
    (2 * (N : ℝ) + 1)
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hden_pos : 0 < 2 * (N : ℝ) + 1 := by linarith
  have hden : 2 * (N : ℝ) + 1 ≤ ‖s‖ := by
    have hre : 2 * (N : ℝ) + 1 ≤ |s.re| := by
      simp [s]
      rw [abs_of_nonpos (by linarith)]
      linarith
    exact hre.trans (Complex.abs_re_le_norm s)
  have hQ : 0 ≤ Q := by
    have hseries : 0 ≤ vonMangoldtLSeriesNorm 1 :=
      tsum_nonneg fun n => norm_nonneg _
    have hM : 1 ≤ 2 * (N : ℝ) + T + 4 := by linarith
    have hlog : 0 ≤ Real.log (2 * (N : ℝ) + T + 4) := Real.log_nonneg hM
    dsimp [Q]
    positivity
  have hnum : 0 ≤ Q * x ^ (-(2 * (N : ℝ) + 1)) :=
    mul_nonneg hQ (Real.rpow_nonneg hx.le _)
  have hfirst :
      ‖explicitFormulaIntegrand x s‖ ≤
        Q * x ^ (-(2 * (N : ℝ) + 1)) := by
    simp only [explicitFormulaIntegrand]
    rw [norm_div, norm_mul, hpow]
    calc
      ‖-logDeriv riemannZeta s‖ * x ^ (-(2 * (N : ℝ) + 1)) / ‖s‖ ≤
          (Q * x ^ (-(2 * (N : ℝ) + 1))) / ‖s‖ := by
        gcongr
      _ ≤ Q * x ^ (-(2 * (N : ℝ) + 1)) :=
        div_le_self hnum hline_one
  rw [norm_div]
  calc
    ‖explicitFormulaIntegrand x s‖ / ‖s‖ ≤
        (Q * x ^ (-(2 * (N : ℝ) + 1))) / ‖s‖ :=
      div_le_div_of_nonneg_right hfirst (norm_nonneg s)
    _ ≤ (Q * x ^ (-(2 * (N : ℝ) + 1))) / (2 * (N : ℝ) + 1) :=
      div_le_div_of_nonneg_left hnum hden_pos hden

/-- Compatibility form of
`norm_secondOrderExplicitFormulaIntegrand_odd_vertical_le_of_pos` with the
historical `1 < x` hypothesis. -/
theorem norm_secondOrderExplicitFormulaIntegrand_odd_vertical_le
    {x T t : ℝ} {N : ℕ} (hx : 1 < x) (hT : 0 ≤ T) (ht : |t| ≤ T) :
    ‖secondOrderExplicitFormulaIntegrand x
      (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      secondOrderOddVerticalBound x N T :=
  norm_secondOrderExplicitFormulaIntegrand_odd_vertical_le_of_pos
    (zero_lt_one.trans hx) hT ht

/-- Quantitative endpoint-difference bound for the second-order left vertical
edge on the negative-odd line `Re(s)=-(2N+1)`.  The only restriction on the
height parameter is nonnegativity; no good-height hypothesis is used here. -/
theorem norm_secondOrderLeftXDifference_odd_le_of_pos
    {x y W : ℝ} {N : ℕ} (hx : 0 < x) (hy : 0 < y) (hW : 0 ≤ W) :
    ‖secondOrderLeftXDifference x y (-(2 * (N : ℝ) + 1)) W‖ ≤
      (secondOrderOddVerticalBound y N (2 * Real.pi * W) +
        secondOrderOddVerticalBound x N (2 * Real.pi * W)) *
        (2 * (2 * Real.pi * W)) := by
  let T : ℝ := 2 * Real.pi * W
  have hT : 0 ≤ T := by
    dsimp [T]
    positivity
  have hyIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ => secondOrderExplicitFormulaIntegrand y
      (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I))
    (a := -T) (b := T) (C := secondOrderOddVerticalBound y N T)
    (fun t ht => by
      rw [Set.uIoc_of_le (by linarith)] at ht
      have habs : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      exact norm_secondOrderExplicitFormulaIntegrand_odd_vertical_le_of_pos
        hy hT habs)
  have hxIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ => secondOrderExplicitFormulaIntegrand x
      (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I))
    (a := -T) (b := T) (C := secondOrderOddVerticalBound x N T)
    (fun t ht => by
      rw [Set.uIoc_of_le (by linarith)] at ht
      have habs : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      exact norm_secondOrderExplicitFormulaIntegrand_odd_vertical_le_of_pos
        hx hT habs)
  rw [abs_of_nonneg (by linarith : 0 ≤ T - -T)] at hyIntegral hxIntegral
  unfold secondOrderLeftXDifference
  change ‖(∫ t : ℝ in (-T)..T,
      secondOrderExplicitFormulaIntegrand y
        (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)) -
      ∫ t : ℝ in (-T)..T,
        secondOrderExplicitFormulaIntegrand x
          (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ _
  calc
    _ ≤ ‖∫ t : ℝ in (-T)..T,
          secondOrderExplicitFormulaIntegrand y
            (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ +
        ‖∫ t : ℝ in (-T)..T,
          secondOrderExplicitFormulaIntegrand x
            (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
      norm_sub_le _ _
    _ ≤ secondOrderOddVerticalBound y N T * (T - -T) +
        secondOrderOddVerticalBound x N T * (T - -T) :=
      add_le_add hyIntegral hxIntegral
    _ = _ := by dsimp [T]; ring

/-- Compatibility form of `norm_secondOrderLeftXDifference_odd_le_of_pos`
with the historical strict endpoint hypotheses. -/
theorem norm_secondOrderLeftXDifference_odd_le
    {x y W : ℝ} {N : ℕ} (hx : 1 < x) (hy : 1 < y) (hW : 0 ≤ W) :
    ‖secondOrderLeftXDifference x y (-(2 * (N : ℝ) + 1)) W‖ ≤
      (secondOrderOddVerticalBound y N (2 * Real.pi * W) +
        secondOrderOddVerticalBound x N (2 * Real.pi * W)) *
        (2 * (2 * Real.pi * W)) :=
  norm_secondOrderLeftXDifference_odd_le_of_pos
    (zero_lt_one.trans hx) (zero_lt_one.trans hy) hW

/-- A good-height rectangle with negative-odd left edge has every candidate
pole (`0`, `1`, or a zeta zero) in its strict interior.  The parity argument
excludes trivial zeros from the left edge, while `goodHeight` excludes
nontrivial zeros from the horizontal edges. -/
theorem secondOrder_poleCandidate_mem_interior_negativeOdd_rectangle_of_goodHeight
    {N : ℕ} {T c : ℝ} (hT : 0 < T) (hc : 1 < c)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    ∀ p ∈
      ([[(-(2 * (N : ℝ) + 1)), c]] ×ℂ [[-T, T]] : Set ℂ),
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
        -(2 * (N : ℝ) + 1) < p.re ∧ p.re < c ∧
          -T < p.im ∧ p.im < T := by
  intro p hp hclass
  rcases hclass with rfl | rfl | hpzero
  · have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    simpa using
      (show -(2 * (N : ℝ) + 1) < (0 : ℝ) ∧ 0 < c ∧ -T < 0 ∧ 0 < T from
        ⟨by linarith, by linarith, by linarith, hT⟩)
  · have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    simpa using
      (show -(2 * (N : ℝ) + 1) < (1 : ℝ) ∧ 1 < c ∧ -T < 0 ∧ 0 < T from
        ⟨by linarith, hc, by linarith, hT⟩)
  · have hp' := hp
    simp only [Complex.mem_reProdIm] at hp'
    have ha_le_c : -(2 * (N : ℝ) + 1) ≤ c := by
      have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    rw [Set.uIcc_of_le ha_le_c] at hp'
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at hp'
    by_cases htriv : ∃ n : ℕ, p = -2 * ((n : ℂ) + 1)
    · rcases htriv with ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      have him := congrArg Complex.im hn
      norm_num at hre him
      have hre_lower : -(2 * (N : ℝ) + 1) < p.re := by
        by_contra hnot
        have hre_eq : p.re = -(2 * (N : ℝ) + 1) := by
          linarith [hp'.1.1]
        rw [hre_eq] at hre
        have hnat : 2 * N + 1 = 2 * (n + 1) := by
          exact_mod_cast (by linarith :
            (2 * (N : ℝ) + 1) = 2 * ((n : ℝ) + 1))
        omega
      exact ⟨hre_lower, by linarith [hp'.1.2], by linarith [hp'.2.1],
        by linarith [hp'.2.2]⟩
    · have hre_pos : 0 < p.re := by
        by_contra hnot
        exact (riemannZeta_ne_zero_of_re_le_zero
          (le_of_not_gt hnot) (by simpa [not_exists] using htriv)) hpzero
      have hre_lt_one : p.re < 1 := by
        by_contra hnot
        exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hnot)) hpzero
      have habs_le : |p.im| ≤ T := abs_le.mpr hp'.2
      have habs_ne : |p.im| ≠ T :=
        hgood p ⟨hpzero, hre_pos, hre_lt_one⟩
      have him_strict := abs_lt.mp (lt_of_le_of_ne habs_le habs_ne)
      exact ⟨by linarith, by linarith, him_strict.1, him_strict.2⟩

/-- A logarithmic-derivative bound on one horizontal point gains a second
factor of the height in the denominator for the second-order Perron kernel. -/
lemma norm_secondOrderExplicitFormulaIntegrand_horizontal_le_of_logDeriv_le_of_re_le
    {x σ b t K : ℝ} (hx : 1 ≤ x) (hσ : σ ≤ b) (ht : 0 < |t|)
    (hK : 0 ≤ K)
    (hlog : ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ K) :
    ‖secondOrderExplicitFormulaIntegrand x ((σ : ℂ) + I * t)‖ ≤
      K * x ^ b / |t| ^ 2 := by
  let s : ℂ := (σ : ℂ) + I * t
  have hfirst := norm_explicitFormulaIntegrand_horizontal_le_of_logDeriv_le_of_re_le
    hx hσ ht hK hlog
  have hline : |t| ≤ ‖s‖ := by
    have him := Complex.abs_im_le_norm s
    simpa [s] using him
  have hnum : 0 ≤ K * x ^ b :=
    mul_nonneg hK (Real.rpow_nonneg (zero_le_one.trans hx) _)
  change ‖explicitFormulaIntegrand x s / s‖ ≤ _
  rw [norm_div]
  calc
    ‖explicitFormulaIntegrand x s‖ / ‖s‖ ≤
        (K * x ^ b / |t|) / ‖s‖ :=
      div_le_div_of_nonneg_right hfirst (norm_nonneg s)
    _ ≤ (K * x ^ b / |t|) / |t| :=
      div_le_div_of_nonneg_left (div_nonneg hnum ht.le) ht hline
    _ = K * x ^ b / |t| ^ 2 := by ring

/-- In every unit height interval, one selected good height controls the full
central horizontal endpoint difference for the second-order contour. The
bound is uniform on every real interval `[a,b]` contained in `[-1,2]`. -/
theorem exists_goodHeight_Icc_norm_secondOrderHorizontalXDifference_le
    {x y a b : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (ha : -1 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ t : ℝ, |t| = T →
            ‖secondOrderHorizontalXDifference x y a b t‖ ≤
              ((C * y ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2) +
                (C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2)) *
                (b - a) := by
  rcases exists_goodHeight_Icc_norm_logDeriv_central_band_le_log_sq with
    ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hlog⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro t ht
  have hTabs : 0 < |t| := by rw [ht]; linarith [hT.1]
  have hK : 0 ≤ C * (1 + Real.log (A + 6)) ^ 2 :=
    mul_nonneg hC (sq_nonneg _)
  let Ky : ℝ := C * y ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2
  let Kx : ℝ := C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2
  have hyPoint : ∀ σ ∈ Set.uIoc a b,
      ‖secondOrderExplicitFormulaIntegrand y ((σ : ℂ) + t * I)‖ ≤ Ky := by
    intro σ hσ
    rw [Set.uIoc_of_le hab] at hσ
    have hpoint :=
      norm_secondOrderExplicitFormulaIntegrand_horizontal_le_of_logDeriv_le_of_re_le
        (b := 2) hy (le_trans hσ.2 hb) hTabs hK
          (hlog t ht σ (le_trans ha hσ.1.le) (le_trans hσ.2 hb))
    rw [ht] at hpoint
    simpa [Ky, mul_comm, mul_left_comm, mul_assoc] using hpoint
  have hxPoint : ∀ σ ∈ Set.uIoc a b,
      ‖secondOrderExplicitFormulaIntegrand x ((σ : ℂ) + t * I)‖ ≤ Kx := by
    intro σ hσ
    rw [Set.uIoc_of_le hab] at hσ
    have hpoint :=
      norm_secondOrderExplicitFormulaIntegrand_horizontal_le_of_logDeriv_le_of_re_le
        (b := 2) hx (le_trans hσ.2 hb) hTabs hK
          (hlog t ht σ (le_trans ha hσ.1.le) (le_trans hσ.2 hb))
    rw [ht] at hpoint
    simpa [Kx, mul_comm, mul_left_comm, mul_assoc] using hpoint
  have hyIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun σ : ℝ => secondOrderExplicitFormulaIntegrand y ((σ : ℂ) + t * I))
    (a := a) (b := b) (C := Ky) hyPoint
  have hxIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun σ : ℝ => secondOrderExplicitFormulaIntegrand x ((σ : ℂ) + t * I))
    (a := a) (b := b) (C := Kx) hxPoint
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hyIntegral hxIntegral
  unfold secondOrderHorizontalXDifference
  calc
    _ ≤ ‖∫ σ : ℝ in a..b,
          secondOrderExplicitFormulaIntegrand y ((σ : ℂ) + t * I)‖ +
        ‖∫ σ : ℝ in a..b,
          secondOrderExplicitFormulaIntegrand x ((σ : ℂ) + t * I)‖ :=
      norm_sub_le _ _
    _ ≤ Ky * (b - a) + Kx * (b - a) := add_le_add hyIntegral hxIntegral
    _ = _ := by dsimp [Ky, Kx]; ring

/-- The full second-order contour-remainder difference is controlled by the
three actual edge differences. This is an exact finite-height budget, not an
asymptotic estimate. -/
theorem norm_secondOrderContourRemainder_sub_le_edgeDifferences
    (x y a c W : ℝ) :
    ‖secondOrderContourRemainder y a c W -
        secondOrderContourRemainder x a c W‖ ≤
      (‖secondOrderHorizontalXDifference x y a c (-(2 * Real.pi * W))‖ +
          ‖secondOrderHorizontalXDifference x y a c (2 * Real.pi * W)‖ +
          ‖secondOrderLeftXDifference x y a W‖) /
        (2 * Real.pi) := by
  let B := secondOrderHorizontalXDifference x y a c (-(2 * Real.pi * W))
  let T := secondOrderHorizontalXDifference x y a c (2 * Real.pi * W)
  let L := secondOrderLeftXDifference x y a W
  have hremainder :
      secondOrderContourRemainder y a c W -
          secondOrderContourRemainder x a c W =
        (B - T - I * L) / (2 * Real.pi * I) := by
    dsimp [B, T, L, secondOrderHorizontalXDifference,
      secondOrderLeftXDifference, secondOrderContourRemainder]
    ring
  rw [hremainder, norm_div]
  have hden : ‖(2 : ℂ) * (Real.pi : ℂ) * I‖ = 2 * Real.pi := by
    rw [norm_mul, norm_I, mul_one, norm_mul, norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hden]
  apply (div_le_div_iff_of_pos_right (mul_pos (by norm_num) Real.pi_pos)).2
  calc
    ‖B - T - I * L‖ ≤ ‖B - T‖ + ‖I * L‖ := norm_sub_le _ _
    _ ≤ (‖B‖ + ‖T‖) + ‖L‖ := by
      gcongr
      · exact norm_sub_le B T
      · simp
    _ = ‖B‖ + ‖T‖ + ‖L‖ := rfl

/-- At one selected good height, the complete second-order contour-remainder
difference on the concrete negative-odd line `Re(s) = -1` has an explicit
finite-height budget.  This closes the three-edge estimate and boundary
safety at `a = -1`; it does not assert the still-missing moving-left
second-order residue identity across `s = 0` and the trivial zeros. -/
theorem exists_goodHeight_Icc_norm_secondOrderContourRemainder_sub_neg_one_le
    {x y c : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hc : 1 < c) (hc2 : c ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          (∀ p ∈
            ([[(-1 : ℝ), c]] ×ℂ [[-T, T]] : Set ℂ),
            p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
              -1 < p.re ∧ p.re < c ∧ -T < p.im ∧ p.im < T) ∧
          ‖secondOrderContourRemainder y (-1) c (T / (2 * Real.pi)) -
              secondOrderContourRemainder x (-1) c (T / (2 * Real.pi))‖ ≤
            (2 *
                (((C * y ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2) +
                    (C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2)) *
                  (c - (-1))) +
              (secondOrderOddVerticalBound y 0 T +
                  secondOrderOddVerticalBound x 0 T) *
                (2 * T)) /
              (2 * Real.pi) := by
  rcases exists_goodHeight_Icc_norm_secondOrderHorizontalXDifference_le
      hx hy (a := -1) (b := c) (by norm_num) (by linarith) hc2 with
    ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hhorizontal⟩
  have hTpos : 0 < T := by linarith [hT.1]
  have hboundary :
      ∀ p ∈
        ([[(-1 : ℝ), c]] ×ℂ [[-T, T]] : Set ℂ),
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
          -1 < p.re ∧ p.re < c ∧ -T < p.im ∧ p.im < T := by
    simpa using
      (secondOrder_poleCandidate_mem_interior_negativeOdd_rectangle_of_goodHeight
        (N := 0) hTpos hc hgood)
  let K : ℝ :=
    ((C * y ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2) +
      (C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2)) *
        (c - (-1))
  let L : ℝ :=
    (secondOrderOddVerticalBound y 0 T +
      secondOrderOddVerticalBound x 0 T) * (2 * T)
  have hbottom :
      ‖secondOrderHorizontalXDifference x y (-1) c (-T)‖ ≤ K := by
    exact hhorizontal (-T) (by rw [abs_neg, abs_of_pos hTpos])
  have htop :
      ‖secondOrderHorizontalXDifference x y (-1) c T‖ ≤ K := by
    exact hhorizontal T (abs_of_pos hTpos)
  have hden : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hscale : 2 * Real.pi * (T / (2 * Real.pi)) = T := by
    field_simp [Real.pi_ne_zero]
  have hleft :
      ‖secondOrderLeftXDifference x y (-1) (T / (2 * Real.pi))‖ ≤ L := by
    have hraw := norm_secondOrderLeftXDifference_odd_le_of_pos
      (N := 0) (lt_of_lt_of_le zero_lt_one hx)
        (lt_of_lt_of_le zero_lt_one hy)
        (div_nonneg hTpos.le hden.le)
    simpa [hscale, L] using hraw
  have hremainder :=
    norm_secondOrderContourRemainder_sub_le_edgeDifferences
      x y (-1) c (T / (2 * Real.pi))
  rw [hscale] at hremainder
  refine ⟨T, hT, hgood, hboundary, ?_⟩
  calc
    ‖secondOrderContourRemainder y (-1) c (T / (2 * Real.pi)) -
        secondOrderContourRemainder x (-1) c (T / (2 * Real.pi))‖ ≤
        (‖secondOrderHorizontalXDifference x y (-1) c (-T)‖ +
            ‖secondOrderHorizontalXDifference x y (-1) c T‖ +
            ‖secondOrderLeftXDifference x y (-1) (T / (2 * Real.pi))‖) /
          (2 * Real.pi) := hremainder
    _ ≤ (K + K + L) / (2 * Real.pi) := by
      exact (div_le_div_iff_of_pos_right hden).2
        (add_le_add (add_le_add hbottom htop) hleft)
    _ = _ := by
      dsimp [K, L]
      ring

/-- Concrete `T^-2` control of the change in the upper right horizontal edge
when the smoothing endpoint changes from `x` to `y`. -/
theorem norm_secondOrderHorizontalXDifference_right_le
    {x y ε c T : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hε : 0 < ε)
    (hc : 1 + ε ≤ c) (hT : 0 < T) :
    ‖secondOrderHorizontalXDifference x y (1 + ε) c T‖ ≤
      (vonMangoldtLSeriesNorm ε * y ^ c / T ^ 2) * (c - (1 + ε)) +
        (vonMangoldtLSeriesNorm ε * x ^ c / T ^ 2) * (c - (1 + ε)) := by
  unfold secondOrderHorizontalXDifference
  exact (norm_sub_le _ _).trans (add_le_add
    (norm_horizontal_right_secondOrderContour_le hy hε hc hT)
    (norm_horizontal_right_secondOrderContour_le hx hε hc hT))

/-- Concrete `T^-2` control of the corresponding lower right horizontal edge
difference. -/
theorem norm_secondOrderHorizontalXDifference_right_neg_height_le
    {x y ε c T : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hε : 0 < ε)
    (hc : 1 + ε ≤ c) (hT : 0 < T) :
    ‖secondOrderHorizontalXDifference x y (1 + ε) c (-T)‖ ≤
      (vonMangoldtLSeriesNorm ε * y ^ c / T ^ 2) * (c - (1 + ε)) +
        (vonMangoldtLSeriesNorm ε * x ^ c / T ^ 2) * (c - (1 + ε)) := by
  unfold secondOrderHorizontalXDifference
  simpa [sub_eq_add_neg] using
    (norm_sub_le
      (∫ σ : ℝ in (1 + ε)..c,
        secondOrderExplicitFormulaIntegrand y ((σ : ℂ) - T * I))
      (∫ σ : ℝ in (1 + ε)..c,
        secondOrderExplicitFormulaIntegrand x ((σ : ℂ) - T * I))).trans
      (add_le_add
        (norm_horizontal_right_secondOrderContour_neg_height_le hy hε hc hT)
        (norm_horizontal_right_secondOrderContour_neg_height_le hx hε hc hT))

end ExplicitFormulaResidues

/-- If a complex approximation controls the first Riesz mean at `x` and
`x + h`, its real-part finite difference gives explicit endpoint bounds for
`chebyshevPsi`. The theorem is uniform in the smoothing width `h` and the
external height parameter `T`. -/
theorem chebyshevPsi_bounds_of_smoothedApproximation
    (approx : ℝ → ℝ → ℂ) (error : ℝ → ℝ → ℝ)
    {x h T : ℝ} (hx : 0 < x) (hh : 0 < h)
    (hxError : ‖approx x T - (smoothedChebyshevPsi x : ℂ)‖ ≤ error x T)
    (hyError : ‖approx (x + h) T - (smoothedChebyshevPsi (x + h) : ℂ)‖ ≤
      error (x + h) T) :
    chebyshevPsi x ≤
        ((approx (x + h) T).re - (approx x T).re +
          (error x T + error (x + h) T)) /
            Real.log ((x + h) / x) ∧
      ((approx (x + h) T).re - (approx x T).re -
          (error x T + error (x + h) T)) /
            Real.log ((x + h) / x) ≤
        chebyshevPsi (x + h) := by
  have hxy : x < x + h := by linarith
  have hratio : 1 < (x + h) / x := (lt_div_iff₀ hx).2 (by linarith)
  have hlog : 0 < Real.log ((x + h) / x) := Real.log_pos hratio
  have hxReal : |(approx x T).re - smoothedChebyshevPsi x| ≤ error x T := by
    calc
      |(approx x T).re - smoothedChebyshevPsi x| =
          |(approx x T - (smoothedChebyshevPsi x : ℂ)).re| := by simp
      _ ≤ ‖approx x T - (smoothedChebyshevPsi x : ℂ)‖ := abs_re_le_norm _
      _ ≤ error x T := hxError
  have hyReal : |(approx (x + h) T).re - smoothedChebyshevPsi (x + h)| ≤
      error (x + h) T := by
    calc
      |(approx (x + h) T).re - smoothedChebyshevPsi (x + h)| =
          |(approx (x + h) T - (smoothedChebyshevPsi (x + h) : ℂ)).re| := by simp
      _ ≤ ‖approx (x + h) T - (smoothedChebyshevPsi (x + h) : ℂ)‖ :=
        abs_re_le_norm _
      _ ≤ error (x + h) T := hyError
  have hUpper : smoothedChebyshevPsi (x + h) - smoothedChebyshevPsi x ≤
      (approx (x + h) T).re - (approx x T).re +
        (error x T + error (x + h) T) := by
    rcases abs_le.mp hxReal with ⟨hxLower, hxUpper⟩
    rcases abs_le.mp hyReal with ⟨hyLower, hyUpper⟩
    linarith
  have hLower :
      (approx (x + h) T).re - (approx x T).re -
          (error x T + error (x + h) T) ≤
        smoothedChebyshevPsi (x + h) - smoothedChebyshevPsi x := by
    rcases abs_le.mp hxReal with ⟨hxLower, hxUpper⟩
    rcases abs_le.mp hyReal with ⟨hyLower, hyUpper⟩
    linarith
  have hRiesz := chebyshevPsi_le_rieszDifference_div_log_le hx hxy
  constructor
  · calc
      chebyshevPsi x ≤
          (smoothedChebyshevPsi (x + h) - smoothedChebyshevPsi x) /
            Real.log ((x + h) / x) := hRiesz.1
      _ ≤ ((approx (x + h) T).re - (approx x T).re +
          (error x T + error (x + h) T)) /
            Real.log ((x + h) / x) := (div_le_div_iff_of_pos_right hlog).2 hUpper
  · calc
      ((approx (x + h) T).re - (approx x T).re -
          (error x T + error (x + h) T)) /
            Real.log ((x + h) / x) ≤
          (smoothedChebyshevPsi (x + h) - smoothedChebyshevPsi x) /
            Real.log ((x + h) / x) := (div_le_div_iff_of_pos_right hlog).2 hLower
      _ ≤ chebyshevPsi (x + h) := hRiesz.2

namespace ExplicitFormulaResidues

/-- The explicit Perron truncation error appearing in the finite-height
second-order formula. This excludes the three shifted contour edges, which are
part of the approximation itself. -/
noncomputable def secondOrderPerronError (x c W : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldt n * (x / n) ^ c / (2 * Real.pi ^ 2 * W)

/-- Apply the finite-height second-order explicit formula at both endpoints of
one smoothing interval and feed the resulting, genuinely constructed Perron
error bounds into `chebyshevPsi_bounds_of_smoothedApproximation`.

The approximation at each endpoint is the finite residue sum minus the full
second-order contour remainder. No bound on that contour remainder is assumed
or manufactured here. -/
theorem exists_chebyshevPsi_bounds_of_secondOrderExplicitFormula
    {x h a c W : ℝ} (hx : 0 < x) (hh : 0 < h) (ha : 0 < a)
    (hac : a < c) (hc : 1 < c) (hW : 0 < W)
    (hboundary : ∀ p ∈
      ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (polesX : Finset ℂ) (residueX : ℂ → ℂ)
        (polesY : Finset ℂ) (residueY : ℂ → ℂ),
      (∀ p ∈ polesX,
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ polesX, p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ polesX, residueX p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 2) ∧
      (∀ p ∈ polesY,
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ polesY, p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ polesY, residueY p =
        if p = 1 then ((x + h : ℝ) : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) *
          ((x + h : ℝ) : ℂ) ^ p / p ^ 2) ∧
      ‖((∑ p ∈ polesX, residueX p) - secondOrderContourRemainder x a c W) -
          (smoothedChebyshevPsi x : ℂ)‖ ≤ secondOrderPerronError x c W ∧
      ‖((∑ p ∈ polesY, residueY p) -
          secondOrderContourRemainder (x + h) a c W) -
          (smoothedChebyshevPsi (x + h) : ℂ)‖ ≤
        secondOrderPerronError (x + h) c W ∧
      chebyshevPsi x ≤
          ((((∑ p ∈ polesY, residueY p) -
                secondOrderContourRemainder (x + h) a c W) -
              ((∑ p ∈ polesX, residueX p) -
                secondOrderContourRemainder x a c W)).re +
            (secondOrderPerronError x c W +
              secondOrderPerronError (x + h) c W)) /
              Real.log ((x + h) / x) ∧
        ((((∑ p ∈ polesY, residueY p) -
                secondOrderContourRemainder (x + h) a c W) -
              ((∑ p ∈ polesX, residueX p) -
                secondOrderContourRemainder x a c W)).re -
            (secondOrderPerronError x c W +
              secondOrderPerronError (x + h) c W)) /
              Real.log ((x + h) / x) ≤
          chebyshevPsi (x + h) := by
  have hy : 0 < x + h := by linarith
  rcases exists_norm_residue_sum_sub_contourRemainder_sub_smoothedPsi_le
      hx ha hac hc hW hboundary with
    ⟨polesX, residueX, hpolesX, hclassX, hresidueX, hxError⟩
  rcases exists_norm_residue_sum_sub_contourRemainder_sub_smoothedPsi_le
      hy ha hac hc hW hboundary with
    ⟨polesY, residueY, hpolesY, hclassY, hresidueY, hyError⟩
  have hxError' :
      ‖((∑ p ∈ polesX, residueX p) - secondOrderContourRemainder x a c W) -
          (smoothedChebyshevPsi x : ℂ)‖ ≤ secondOrderPerronError x c W := by
    simpa [secondOrderPerronError] using hxError
  have hyError' :
      ‖((∑ p ∈ polesY, residueY p) -
          secondOrderContourRemainder (x + h) a c W) -
          (smoothedChebyshevPsi (x + h) : ℂ)‖ ≤
        secondOrderPerronError (x + h) c W := by
    simpa [secondOrderPerronError] using hyError
  let approxX : ℂ :=
    (∑ p ∈ polesX, residueX p) - secondOrderContourRemainder x a c W
  let approxY : ℂ :=
    (∑ p ∈ polesY, residueY p) - secondOrderContourRemainder (x + h) a c W
  let approx : ℝ → ℝ → ℂ := fun u _ => if u = x then approxX else approxY
  let error : ℝ → ℝ → ℝ := fun u _ =>
    if u = x then secondOrderPerronError x c W
    else secondOrderPerronError (x + h) c W
  have hxy : x + h ≠ x := by linarith
  have hbounds := chebyshevPsi_bounds_of_smoothedApproximation
    approx error (T := W) hx hh
    (by simpa [approx, error, approxX] using hxError')
    (by simpa [approx, error, approxY, hxy] using hyError')
  refine ⟨polesX, residueX, polesY, residueY, hpolesX, hclassX, hresidueX,
    hpolesY, hclassY, hresidueY, hxError', hyError', ?_⟩
  simpa [approx, error, approxX, approxY, hxy] using hbounds

/-- Apply the crossing-zero second-order explicit formula at both endpoints of
one smoothing interval and feed the resulting concrete Perron errors into the
Riesz finite-difference sandwich. The finite residue families now include the
origin and retain its derivative coefficient explicitly. -/
theorem exists_chebyshevPsi_bounds_of_secondOrderExplicitFormula_crossing_zero
    {x h a c W : ℝ} (hx : 0 < x) (hh : 0 < h) (ha : a < 0)
    (hc : 1 < c) (hW : 0 < W)
    (hboundary : ∀ p ∈
      ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (polesX : Finset ℂ) (residueX : ℂ → ℂ)
        (polesY : Finset ℂ) (residueY : ℂ → ℂ),
      (∀ p ∈ polesX,
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ polesX, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈
          ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ polesX) ∧
      residueX 0 =
        deriv (fun z : ℂ =>
          -logDeriv riemannZeta z * (x : ℂ) ^ z) 0 ∧
      (∀ p ∈ polesX, p ≠ 0 → residueX p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) *
          (x : ℂ) ^ p / p ^ 2) ∧
      (∀ p ∈ polesY,
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ polesY, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈
          ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ polesY) ∧
      residueY 0 =
        deriv (fun z : ℂ =>
          -logDeriv riemannZeta z * ((x + h : ℝ) : ℂ) ^ z) 0 ∧
      (∀ p ∈ polesY, p ≠ 0 → residueY p =
        if p = 1 then ((x + h : ℝ) : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) *
          ((x + h : ℝ) : ℂ) ^ p / p ^ 2) ∧
      ‖((∑ p ∈ polesX, residueX p) -
          secondOrderContourRemainder x a c W) -
          (smoothedChebyshevPsi x : ℂ)‖ ≤
        secondOrderPerronError x c W ∧
      ‖((∑ p ∈ polesY, residueY p) -
          secondOrderContourRemainder (x + h) a c W) -
          (smoothedChebyshevPsi (x + h) : ℂ)‖ ≤
        secondOrderPerronError (x + h) c W ∧
      chebyshevPsi x ≤
          ((((∑ p ∈ polesY, residueY p) -
                secondOrderContourRemainder (x + h) a c W) -
              ((∑ p ∈ polesX, residueX p) -
                secondOrderContourRemainder x a c W)).re +
            (secondOrderPerronError x c W +
              secondOrderPerronError (x + h) c W)) /
              Real.log ((x + h) / x) ∧
        ((((∑ p ∈ polesY, residueY p) -
                secondOrderContourRemainder (x + h) a c W) -
              ((∑ p ∈ polesX, residueX p) -
                secondOrderContourRemainder x a c W)).re -
            (secondOrderPerronError x c W +
              secondOrderPerronError (x + h) c W)) /
              Real.log ((x + h) / x) ≤
          chebyshevPsi (x + h) := by
  have hy : 0 < x + h := by linarith
  rcases
      exists_norm_residue_sum_sub_contourRemainder_sub_smoothedPsi_le_crossing_zero
        hx ha hc hW hboundary with
    ⟨polesX, residueX, hpolesX, hclassX, hcompleteX, hzeroX,
      hresidueX, hxError⟩
  rcases
      exists_norm_residue_sum_sub_contourRemainder_sub_smoothedPsi_le_crossing_zero
        hy ha hc hW hboundary with
    ⟨polesY, residueY, hpolesY, hclassY, hcompleteY, hzeroY,
      hresidueY, hyError⟩
  have hxError' :
      ‖((∑ p ∈ polesX, residueX p) -
          secondOrderContourRemainder x a c W) -
          (smoothedChebyshevPsi x : ℂ)‖ ≤
        secondOrderPerronError x c W := by
    simpa [secondOrderPerronError] using hxError
  have hyError' :
      ‖((∑ p ∈ polesY, residueY p) -
          secondOrderContourRemainder (x + h) a c W) -
          (smoothedChebyshevPsi (x + h) : ℂ)‖ ≤
        secondOrderPerronError (x + h) c W := by
    simpa [secondOrderPerronError] using hyError
  let approxX : ℂ :=
    (∑ p ∈ polesX, residueX p) -
      secondOrderContourRemainder x a c W
  let approxY : ℂ :=
    (∑ p ∈ polesY, residueY p) -
      secondOrderContourRemainder (x + h) a c W
  let approx : ℝ → ℝ → ℂ := fun u _ =>
    if u = x then approxX else approxY
  let error : ℝ → ℝ → ℝ := fun u _ =>
    if u = x then secondOrderPerronError x c W
    else secondOrderPerronError (x + h) c W
  have hxy : x + h ≠ x := by linarith
  have hbounds := chebyshevPsi_bounds_of_smoothedApproximation
    approx error (T := W) hx hh
    (by simpa [approx, error, approxX] using hxError')
    (by simpa [approx, error, approxY, hxy] using hyError')
  refine
    ⟨polesX, residueX, polesY, residueY,
      hpolesX, hclassX, hcompleteX, hzeroX, hresidueX,
      hpolesY, hclassY, hcompleteY, hzeroY, hresidueY,
      hxError', hyError', ?_⟩
  simpa [approx, error, approxX, approxY, hxy] using hbounds

end ExplicitFormulaResidues

end PrimeNumberTheorem
