import PrimeNumberTheorem.ZeroDensityLayerBudgetCubicKernelFactorization

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- The first exponential difference quotient whose square is the cubic
kernel multiplier. -/
noncomputable def cubicKernelDifferenceQuotient (rho : ℂ) (h : ℝ) : ℂ :=
  (Complex.exp ((h : ℂ) * rho) - 1) / ((h : ℂ) * rho)

theorem cubicKernelMultiplier_eq_differenceQuotient_sq
    (rho : ℂ) (h : ℝ) :
    cubicKernelMultiplier rho h = cubicKernelDifferenceQuotient rho h ^ 2 := by
  rfl

/-- The complex exponential Taylor remainder gives a linear error bound for
the normalized first difference quotient. -/
theorem norm_cubicKernelDifferenceQuotient_sub_one_le
    {rho : ℂ} {h : ℝ} (hh : 0 < h) (hrho : rho ≠ 0)
    (hsmall : h * ‖rho‖ ≤ 1) :
    ‖cubicKernelDifferenceQuotient rho h - 1‖ ≤ h * ‖rho‖ := by
  let u : ℂ := (h : ℂ) * rho
  have hu : u ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hh.ne') hrho
  have hunorm : ‖u‖ = h * ‖rho‖ := by
    dsimp [u]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  have hTaylor : ‖Complex.exp u - 1 - u‖ ≤ ‖u‖ ^ 2 :=
    Complex.norm_exp_sub_one_sub_id_le (by simpa [hunorm] using hsmall)
  change ‖(Complex.exp u - 1) / u - 1‖ ≤ h * ‖rho‖
  rw [show (Complex.exp u - 1) / u - 1 =
      (Complex.exp u - 1 - u) / u by field_simp [hu],
    norm_div]
  calc
    ‖Complex.exp u - 1 - u‖ / ‖u‖ ≤ ‖u‖ ^ 2 / ‖u‖ :=
      div_le_div_of_nonneg_right hTaylor (norm_nonneg u)
    _ = ‖u‖ := by
      field_simp [norm_ne_zero_iff.mpr hu]
    _ = h * ‖rho‖ := hunorm

/-- On the natural local range `h * |rho| <= 1`, the squared multiplier is
within `3 h |rho|` of one. -/
theorem norm_cubicKernelMultiplier_sub_one_le_three_mul
    {rho : ℂ} {h : ℝ} (hh : 0 < h) (hrho : rho ≠ 0)
    (hsmall : h * ‖rho‖ ≤ 1) :
    ‖cubicKernelMultiplier rho h - 1‖ ≤ 3 * (h * ‖rho‖) := by
  let q := cubicKernelDifferenceQuotient rho h
  let d := h * ‖rho‖
  have hd0 : 0 ≤ d := mul_nonneg hh.le (norm_nonneg rho)
  have hqsub : ‖q - 1‖ ≤ d := by
    exact norm_cubicKernelDifferenceQuotient_sub_one_le hh hrho hsmall
  have hqnorm : ‖q‖ ≤ 1 + d := by
    calc
      ‖q‖ = ‖(q - 1) + 1‖ := by congr 1 <;> ring
      _ ≤ ‖q - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ d + 1 := add_le_add hqsub (by simp)
      _ = 1 + d := by ring
  have hqplus : ‖q + 1‖ ≤ 2 + d := by
    calc
      ‖q + 1‖ ≤ ‖q‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ (1 + d) + 1 := add_le_add hqnorm (by simp)
      _ = 2 + d := by ring
  rw [cubicKernelMultiplier_eq_differenceQuotient_sq]
  change ‖q ^ 2 - 1‖ ≤ 3 * d
  rw [show q ^ 2 - 1 = (q - 1) * (q + 1) by ring, norm_mul]
  calc
    ‖q - 1‖ * ‖q + 1‖ ≤ d * (2 + d) :=
      mul_le_mul hqsub hqplus (norm_nonneg _) hd0
    _ ≤ 3 * d := by
      have hd1 : d ≤ 1 := hsmall
      nlinarith

/-- A norm-near-one multiplier lies in the corresponding scalar annulus. -/
theorem norm_multiplier_bounds_of_sub_one_le
    {M : ℂ} {epsilon : ℝ} (hnear : ‖M - 1‖ ≤ epsilon) :
    1 - epsilon ≤ ‖M‖ ∧ ‖M‖ ≤ 1 + epsilon := by
  have hlower : 1 ≤ ‖M - 1‖ + ‖M‖ := by
    calc
      1 = ‖(1 : ℂ)‖ := by simp
      _ = ‖(1 - M) + M‖ := by congr 1 <;> ring
      _ ≤ ‖1 - M‖ + ‖M‖ := norm_add_le _ _
      _ = ‖M - 1‖ + ‖M‖ := by rw [norm_sub_rev]
  have hupper : ‖M‖ ≤ ‖M - 1‖ + 1 := by
    calc
      ‖M‖ = ‖(M - 1) + 1‖ := by congr 1 <;> ring
      _ ≤ ‖M - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖M - 1‖ + 1 := by simp
  constructor <;> linarith

/-- Multiplier control transfers directly to two-sided bounds at the exact
`multiplicity * x^(Re rho) / |rho|` scale. -/
theorem norm_cubicZeroResidueSecondDifference_correctScale_bounds
    {rho : ℂ} {x h epsilon : ℝ} (hx : 0 < x) (hh : 0 < h)
    (hrho : rho ≠ 0)
    (hnear : ‖cubicKernelMultiplier rho h - 1‖ ≤ epsilon) :
    let scale :=
      (analyticOrderNatAt riemannZeta rho : ℝ) * x ^ rho.re / ‖rho‖
    (1 - epsilon) * scale ≤
        ‖cubicZeroResidueSecondDifference rho x h / (h : ℂ) ^ 2‖ ∧
      ‖cubicZeroResidueSecondDifference rho x h / (h : ℂ) ^ 2‖ ≤
        (1 + epsilon) * scale := by
  dsimp only
  have hscale :
      0 ≤ (analyticOrderNatAt riemannZeta rho : ℝ) * x ^ rho.re / ‖rho‖ := by
    positivity
  have hmult := norm_multiplier_bounds_of_sub_one_le hnear
  rw [norm_cubicZeroResidueSecondDifference_div_sq_eq hx hh hrho]
  constructor
  · rw [mul_comm (1 - epsilon)]
    exact mul_le_mul_of_nonneg_left hmult.1 hscale
  · rw [mul_comm (1 + epsilon)]
    exact mul_le_mul_of_nonneg_left hmult.2 hscale

/-- Every finite nonzero pole set admits one positive step-size threshold on
which all cubic multipliers are uniformly epsilon-close to one. -/
theorem exists_pos_forall_mem_norm_cubicKernelMultiplier_sub_one_lt
    (P : Finset ℂ) (hnonzero : ∀ rho ∈ P, rho ≠ 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ h : ℝ, 0 < h → h < delta →
        ∀ rho ∈ P, ‖cubicKernelMultiplier rho h - 1‖ < epsilon := by
  let S : ℝ := ∑ rho ∈ P, ‖rho‖
  let M : ℝ := 1 + S
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun rho _ => norm_nonneg rho
  have hMpos : 0 < M := by
    dsimp [M]
    linarith
  let delta : ℝ := min (1 / (2 * M)) (epsilon / (6 * M))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min
      (div_pos zero_lt_one (mul_pos (by norm_num) hMpos))
      (div_pos hepsilon (mul_pos (by norm_num) hMpos))
  refine ⟨delta, hdelta, ?_⟩
  intro h hh hhdelta rho hrho
  have hnormS : ‖rho‖ ≤ S := by
    dsimp [S]
    exact Finset.single_le_sum (fun z _ => norm_nonneg z) hrho
  have hnormM : ‖rho‖ ≤ M := by
    dsimp [M]
    linarith
  have hhFirst : h < 1 / (2 * M) :=
    hhdelta.trans_le (min_le_left _ _)
  have hhSecond : h < epsilon / (6 * M) :=
    hhdelta.trans_le (min_le_right _ _)
  have hsmallM : h * M < 1 := by
    have htwoM : 0 < 2 * M := mul_pos (by norm_num) hMpos
    have := (lt_div_iff₀ htwoM).1 hhFirst
    nlinarith
  have hsmallRho : h * ‖rho‖ ≤ 1 := by
    calc
      h * ‖rho‖ ≤ h * M := mul_le_mul_of_nonneg_left hnormM hh.le
      _ ≤ 1 := hsmallM.le
  have hlocal := norm_cubicKernelMultiplier_sub_one_le_three_mul
    hh (hnonzero rho hrho) hsmallRho
  have hepsilonM : 3 * (h * M) < epsilon := by
    have hsixM : 0 < 6 * M := mul_pos (by norm_num) hMpos
    have := (lt_div_iff₀ hsixM).1 hhSecond
    nlinarith
  calc
    ‖cubicKernelMultiplier rho h - 1‖ ≤ 3 * (h * ‖rho‖) := hlocal
    _ ≤ 3 * (h * M) := by
      gcongr
    _ < epsilon := hepsilonM

end ExplicitFormulaResidues
end PrimeNumberTheorem
