import PrimeNumberTheorem.RieszDifference
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
gains the reciprocal distance of the line from the imaginary axis. -/
theorem norm_secondOrderExplicitFormulaIntegrand_odd_vertical_le
    {x T t : ℝ} {N : ℕ} (hx : 1 < x) (hT : 0 ≤ T) (ht : |t| ≤ T) :
    ‖secondOrderExplicitFormulaIntegrand x
      (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      secondOrderOddVerticalBound x N T := by
  let s : ℂ := ((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I
  let Q : ℝ := vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
    2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
      Real.log (2 * (N : ℝ) + T + 4)) + Real.pi
  have hfirst := norm_explicitFormulaIntegrand_odd_vertical_le (N := N) hx hT ht
  change ‖explicitFormulaIntegrand x s / s‖ ≤ Q * x ^ (-(2 * (N : ℝ) + 1)) /
    (2 * (N : ℝ) + 1)
  change ‖explicitFormulaIntegrand x s‖ ≤ Q * x ^ (-(2 * (N : ℝ) + 1)) at hfirst
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
    mul_nonneg hQ (Real.rpow_nonneg (zero_lt_one.trans hx).le _)
  rw [norm_div]
  calc
    ‖explicitFormulaIntegrand x s‖ / ‖s‖ ≤
        (Q * x ^ (-(2 * (N : ℝ) + 1))) / ‖s‖ :=
      div_le_div_of_nonneg_right hfirst (norm_nonneg s)
    _ ≤ (Q * x ^ (-(2 * (N : ℝ) + 1))) / (2 * (N : ℝ) + 1) :=
      div_le_div_of_nonneg_left hnum hden_pos hden

/-- Quantitative endpoint-difference bound for the second-order left vertical
edge on the negative-odd line `Re(s)=-(2N+1)`.  The only restriction on the
height parameter is nonnegativity; no good-height hypothesis is used here. -/
theorem norm_secondOrderLeftXDifference_odd_le
    {x y W : ℝ} {N : ℕ} (hx : 1 < x) (hy : 1 < y) (hW : 0 ≤ W) :
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
      exact norm_secondOrderExplicitFormulaIntegrand_odd_vertical_le hy hT habs)
  have hxIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ => secondOrderExplicitFormulaIntegrand x
      (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I))
    (a := -T) (b := T) (C := secondOrderOddVerticalBound x N T)
    (fun t ht => by
      rw [Set.uIoc_of_le (by linarith)] at ht
      have habs : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      exact norm_secondOrderExplicitFormulaIntegrand_odd_vertical_le hx hT habs)
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

end ExplicitFormulaResidues

end PrimeNumberTheorem
