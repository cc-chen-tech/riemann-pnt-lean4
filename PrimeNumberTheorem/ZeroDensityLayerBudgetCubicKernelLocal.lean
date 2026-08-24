import ZeroFreeRegion.MeromorphicAux
import PrimeNumberTheorem.GlobalZeroCount

/-!
# Local cubic zero kernel: definitions, factorization, near-one multiplier

Local re-derivation (merge-test-amplification worktree) of the per-zero
cubic kernel layer that lives on the user's active cubic line
(`actual-cubic-two-height-l2-tail`:

- `ZeroDensityLayerBudgetCubicResidueSecondDifferenceKernel.lean`
- `ZeroDensityLayerBudgetCubicKernelFactorization.lean`
- `ZeroDensityLayerBudgetCubicKernelNearOne.lean`).

Only the *local* per-zero content is included (definitions, the exact
`/ h²` factorization, the simple-kernel norm identity, the near-one
multiplier bounds, the finite-pole-set uniform threshold); the explicit
formula machinery (`thirdOrderContourRemainder`, `chebyshevPsi`, the
common-pole approximants) stays on the cubic line.  Declaration names and
the namespace `ExplicitFormulaResidues` are identical to the cubic line,
so when that line merges its files supersede this one.
-/

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

open ExplicitFormulaAux

/-- The contribution of the zeta pole at one after the logarithmic second
forward difference of the cubic residue sum. -/
noncomputable def cubicPoleOneSecondDifference (x h : ℝ) : ℂ :=
  ((x * Real.exp (2 * h) : ℝ) : ℂ) -
    2 * ((x * Real.exp h : ℝ) : ℂ) + (x : ℂ)

/-- The exact cubic residue kernel of one non-one pole after the logarithmic
second forward difference. -/
noncomputable def cubicZeroResidueSecondDifference
    (rho : ℂ) (x h : ℝ) : ℂ :=
  -(analyticOrderNatAt riemannZeta rho : ℂ) *
      (((x * Real.exp (2 * h) : ℝ) : ℂ) ^ rho -
        2 * (((x * Real.exp h : ℝ) : ℂ) ^ rho) + (x : ℂ) ^ rho) /
    rho ^ 3

/-- The normalized exponential second-difference multiplier attached to a
cubic residue kernel. -/
noncomputable def cubicKernelMultiplier (rho : ℂ) (h : ℝ) : ℂ :=
  ((Complex.exp ((h : ℂ) * rho) - 1) / ((h : ℂ) * rho)) ^ 2

/-- The classical unnormalized simple zero kernel. -/
noncomputable def cubicSimpleZeroKernel (rho : ℂ) (x : ℝ) : ℂ :=
  -(analyticOrderNatAt riemannZeta rho : ℂ) * (x : ℂ) ^ rho / rho

/-- Multiplying a positive real base by `exp h` translates its complex power
by the exact factor `exp (h * rho)`. -/
theorem ofReal_mul_exp_cpow_eq_cpow_mul_exp
    {x h : ℝ} (hx : 0 < x) (rho : ℂ) :
    ((x * Real.exp h : ℝ) : ℂ) ^ rho =
      (x : ℂ) ^ rho * Complex.exp ((h : ℂ) * rho) := by
  rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (mul_pos hx (Real.exp_pos h)).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.ofReal_log (mul_pos hx (Real.exp_pos h)).le,
    Real.log_mul hx.ne' (Real.exp_ne_zero h), Real.log_exp,
    ← Complex.ofReal_log hx.le]
  rw [show (((Real.log x + h : ℝ) : ℂ) * rho) =
      (Real.log x : ℂ) * rho + (h : ℂ) * rho by push_cast; ring,
    Complex.exp_add]

/-- Exact factorization of the normalized cubic discrete kernel into the
classical simple zero kernel and its exponential difference multiplier. -/
theorem cubicZeroResidueSecondDifference_div_sq_eq_simple_mul_multiplier
    {rho : ℂ} {x h : ℝ} (hx : 0 < x) (hh : 0 < h) (hrho : rho ≠ 0) :
    cubicZeroResidueSecondDifference rho x h / (h : ℂ) ^ 2 =
      cubicSimpleZeroKernel rho x * cubicKernelMultiplier rho h := by
  rw [cubicZeroResidueSecondDifference, cubicSimpleZeroKernel,
    cubicKernelMultiplier,
    ofReal_mul_exp_cpow_eq_cpow_mul_exp (h := h) hx rho,
    ofReal_mul_exp_cpow_eq_cpow_mul_exp (h := 2 * h) hx rho]
  have hexpTwo :
      Complex.exp (((2 * h : ℝ) : ℂ) * rho) =
        Complex.exp ((h : ℂ) * rho) * Complex.exp ((h : ℂ) * rho) := by
    rw [show (((2 * h : ℝ) : ℂ) * rho) =
        (h : ℂ) * rho + (h : ℂ) * rho by push_cast; ring,
      Complex.exp_add]
  rw [hexpTwo]
  field_simp [Complex.ofReal_ne_zero.mpr hh.ne', hrho]
  ring

/-- The classical simple kernel has exactly the desired
`multiplicity * x^(Re rho) / |rho|` norm. -/
theorem norm_cubicSimpleZeroKernel_eq
    {rho : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖cubicSimpleZeroKernel rho x‖ =
      (analyticOrderNatAt riemannZeta rho : ℝ) * x ^ rho.re / ‖rho‖ := by
  rw [cubicSimpleZeroKernel, norm_div, norm_mul, norm_neg,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- Consequently the normalized cubic kernel preserves the correct simple
zero scale, up to the explicit multiplier norm. -/
theorem norm_cubicZeroResidueSecondDifference_div_sq_eq
    {rho : ℂ} {x h : ℝ} (hx : 0 < x) (hh : 0 < h) (hrho : rho ≠ 0) :
    ‖cubicZeroResidueSecondDifference rho x h / (h : ℂ) ^ 2‖ =
      ((analyticOrderNatAt riemannZeta rho : ℝ) * x ^ rho.re / ‖rho‖) *
        ‖cubicKernelMultiplier rho h‖ := by
  rw [cubicZeroResidueSecondDifference_div_sq_eq_simple_mul_multiplier
    hx hh hrho, norm_mul, norm_cubicSimpleZeroKernel_eq hx]

/-- The pole-at-one term admits the analogous exact real multiplier
factorization. -/
theorem cubicPoleOneSecondDifference_div_sq_eq
    {x h : ℝ} (hh : 0 < h) :
    cubicPoleOneSecondDifference x h / (h : ℂ) ^ 2 =
      (x : ℂ) * ((((Real.exp h - 1) / h : ℝ) : ℂ) ^ 2) := by
  rw [cubicPoleOneSecondDifference]
  have hexpTwo : Real.exp (2 * h) = Real.exp h * Real.exp h := by
    rw [show 2 * h = h + h by ring, Real.exp_add]
  rw [hexpTwo]
  push_cast
  field_simp [hh.ne']
  ring

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

/-- Far range: for `Re rho ∈ [0, 1]` and `h ≤ log 2`, the multiplier norm
decays like `9 / (h |rho|)^2`. -/
theorem norm_cubicKernelMultiplier_le_nine_div_sq
    {rho : ℂ} {h : ℝ} (hh : 0 < h) (hre : 0 ≤ rho.re) (hre1 : rho.re ≤ 1)
    (hhsmall : h ≤ Real.log 2) (hrho : rho ≠ 0) :
    ‖cubicKernelMultiplier rho h‖ ≤ 9 / (h * ‖rho‖) ^ 2 := by
  let u : ℂ := (h : ℂ) * rho
  have hu : u ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hh.ne') hrho
  have hunorm : ‖u‖ = h * ‖rho‖ := by
    dsimp [u]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  have hRe : u.re ≤ Real.log 2 := by
    dsimp [u]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    nlinarith [hre1, hhsmall, hh]
  have hexp : ‖Complex.exp u‖ ≤ 2 := by
    rw [Complex.norm_exp]
    have h1 : Real.exp u.re ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hRe
    rwa [Real.exp_log (by norm_num : 0 < (2 : ℝ))] at h1
  have hq : ‖cubicKernelDifferenceQuotient rho h‖ ≤ 3 / (h * ‖rho‖) := by
    dsimp [cubicKernelDifferenceQuotient]
    rw [norm_div]
    have hnum : ‖Complex.exp u - 1‖ ≤ ‖Complex.exp u‖ + 1 := by
      calc
        ‖Complex.exp u - 1‖ ≤ ‖Complex.exp u‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖Complex.exp u‖ + 1 := by simp
    calc
      ‖Complex.exp u - 1‖ / ‖u‖ ≤ (‖Complex.exp u‖ + 1) / ‖u‖ :=
        div_le_div_of_nonneg_right hnum (norm_nonneg u)
      _ ≤ (2 + 1) / ‖u‖ :=
        div_le_div_of_nonneg_right (by linarith [hexp]) (norm_nonneg u)
      _ = 3 / (h * ‖rho‖) := by rw [hunorm]; norm_num
  calc
    ‖cubicKernelMultiplier rho h‖ =
        ‖cubicKernelDifferenceQuotient rho h‖ ^ 2 := by
      rw [cubicKernelMultiplier_eq_differenceQuotient_sq, norm_pow]
    _ ≤ (3 / (h * ‖rho‖)) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hq 2
    _ = 9 / (h * ‖rho‖) ^ 2 := by
      field_simp [mul_ne_zero hh.ne' (norm_ne_zero_iff.mpr hu)]
      ring

/-- Uniform two-sided multiplier bound on the top layer
(`|rho| ≥ T0/2`, `Re rho ∈ [0, 1]`, `h ≤ log 2`): near `h|rho| ≤ 1` the
norm is at most 4; far away it decays as `36 / (h T0)^2`. -/
theorem norm_cubicKernelMultiplier_le_uniform
    {rho : ℂ} {h T0 : ℝ} (hh : 0 < h) (hre : 0 ≤ rho.re) (hre1 : rho.re ≤ 1)
    (hT0 : 0 < T0) (hT0half : T0 / 2 ≤ ‖rho‖) (hhsmall : h ≤ Real.log 2)
    (hrho : rho ≠ 0) :
    ‖cubicKernelMultiplier rho h‖ ≤ max 4 (36 / (h * (T0 / 2)) ^ 2) := by
  by_cases hsmall : h * ‖rho‖ ≤ 1
  · have hnear := norm_cubicKernelMultiplier_sub_one_le_three_mul hh hrho hsmall
    have hb := (norm_multiplier_bounds_of_sub_one_le hnear).2
    have h1 : 1 + 3 * (h * ‖rho‖) ≤ 4 := by nlinarith [hsmall]
    exact (le_trans hb h1).trans (le_max_left _ _)
  · have hfar := norm_cubicKernelMultiplier_le_nine_div_sq hh hre hre1 hhsmall hrho
    have hdenom : h * (T0 / 2) ≤ h * ‖rho‖ :=
      mul_le_mul_of_nonneg_left hT0half hh.le
    have hT0half_pos : 0 < T0 / 2 := div_pos hT0 (by norm_num)
    have hdenom_pos : 0 < h * (T0 / 2) := mul_pos hh hT0half_pos
    have h9 : 9 / (h * ‖rho‖) ^ 2 ≤ 36 / (h * (T0 / 2)) ^ 2 := by
      have h1 : (h * (T0 / 2)) ^ 2 ≤ (h * ‖rho‖) ^ 2 := by
        exact pow_le_pow_left₀ hdenom_pos.le hdenom 2
      have h2 : 9 / (h * ‖rho‖) ^ 2 ≤ 9 / (h * (T0 / 2)) ^ 2 := by
        have hrec : 1 / (h * ‖rho‖) ^ 2 ≤ 1 / (h * (T0 / 2)) ^ 2 := by
          exact one_div_le_one_div_of_le (pow_pos hdenom_pos 2) h1
        simpa [div_eq_mul_inv, mul_assoc] using
          (mul_le_mul_of_nonneg_left hrec (by norm_num : 0 ≤ (9 : ℝ)))
      have h3 : 9 / (h * (T0 / 2)) ^ 2 ≤ 36 / (h * (T0 / 2)) ^ 2 := by
        exact div_le_div_of_nonneg_right (by norm_num : (9 : ℝ) ≤ 36)
          (sq_nonneg (h * (T0 / 2)))
      exact h2.trans h3
    exact (hfar.trans h9).trans (le_max_right _ _)

end ExplicitFormulaResidues
end PrimeNumberTheorem
