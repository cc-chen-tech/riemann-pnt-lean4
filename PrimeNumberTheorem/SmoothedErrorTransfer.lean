import PrimeNumberTheorem.RieszDifference
import PrimeNumberTheorem.RightHorizontalEdge

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
