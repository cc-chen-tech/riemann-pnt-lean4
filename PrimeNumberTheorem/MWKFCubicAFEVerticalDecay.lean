import MathlibAux.MellinVerticalStripBound
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import PrimeNumberTheorem.MWKFCubicAFEKernel

open Complex Filter MeasureTheory Set
open scoped Interval

namespace PrimeNumberTheorem
namespace MWKFCubic

/-!
# Vertical-strip bounds and horizontal-edge decay for the cubic AFE

The completed zeta function in Mathlib is built from the Mellin transform of
a rapidly decaying modified theta kernel.  Absolute convergence at the two
real endpoints therefore supplies a bound uniform in the imaginary part.
-/

/-- Mathlib's entire completed Riemann zeta numerator is uniformly bounded on
every closed vertical strip. -/
theorem exists_norm_completedRiemannZeta₀_le_on_reIcc (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      a ≤ z.re → z.re ≤ b → ‖completedRiemannZeta₀ z‖ ≤ C := by
  let P := HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)
  have ha : MellinConvergent P.f_modif ((a / 2 : ℝ) : ℂ) := by
    exact (P.isStrongFEPair_toStrongFEPair.hasMellin ((a / 2 : ℝ) : ℂ)).1
  have hb : MellinConvergent P.f_modif ((b / 2 : ℝ) : ℂ) := by
    exact (P.isStrongFEPair_toStrongFEPair.hasMellin ((b / 2 : ℝ) : ℂ)).1
  obtain ⟨C, hC, hbound⟩ :=
    MathlibAux.exists_norm_mellin_le_on_reIcc ha hb
  refine ⟨C / 2, div_nonneg hC (by norm_num), ?_⟩
  intro z haz hzb
  have hzre : (z / (2 : ℂ)).re = z.re / 2 := by
    norm_num [div_re, normSq_apply]
  have hzbound : ‖mellin P.f_modif (z / 2)‖ ≤ C := by
    apply hbound
    · rw [hzre]
      linarith
    · rw [hzre]
      linarith
  change ‖mellin P.f_modif (z / 2) / 2‖ ≤ C / 2
  rw [norm_div]
  norm_num
  exact div_le_div_of_nonneg_right hzbound zero_le_two

/-- Natural polynomial scale on a horizontal AFE edge. -/
noncomputable def cubicAFEHorizontalScale (t X V : ℝ) : ℝ :=
  1 + ‖cubicCriticalPoint t‖ + ‖1 - cubicCriticalPoint t‖ + X + |V|

/-- On a fixed horizontal-width box, the completed AFE integrand is bounded
by a degree-six polynomial times the exact Gaussian `exp (-V^2)`. -/
theorem exists_norm_cubicAFECompletedIntegrand_horizontal_le
    (t : ℝ) {X : ℝ} (hX : 0 ≤ X) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {x V : ℝ},
      x ∈ [[-X, X]] → 1 ≤ V →
        ‖cubicAFECompletedIntegrand t
            ((x : ℂ) + (V : ℂ) * I)‖ ≤
          K * cubicAFEHorizontalScale t X V ^ 6 * Real.exp (-V ^ 2) := by
  obtain ⟨C, hC, hCZ⟩ := exists_norm_completedRiemannZeta₀_le_on_reIcc
    (1 / 2 - X) (1 / 2 + X)
  let s := cubicCriticalPoint t
  let u := 1 - s
  let K : ℝ :=
    5 * (C + 2) ^ 2 * (‖s ^ 2‖⁻¹ * ‖u ^ 2‖⁻¹) * Real.exp (X ^ 2)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro x V hx hV
  let z : ℂ := (x : ℂ) + (V : ℂ) * I
  let Y : ℝ := cubicAFEHorizontalScale t X V
  have hxIcc : -X ≤ x ∧ x ≤ X := by
    rw [uIcc_of_le (by linarith : -X ≤ X)] at hx
    exact hx
  have habsx : |x| ≤ X := abs_le.mpr hxIcc
  have hV0 : 0 ≤ V := by linarith
  have habsV : |V| = V := abs_of_nonneg hV0
  have hY : 1 ≤ Y := by
    dsimp [Y, cubicAFEHorizontalScale]
    linarith [norm_nonneg (cubicCriticalPoint t),
      norm_nonneg (1 - cubicCriticalPoint t), abs_nonneg V]
  have hzbound : ‖z‖ ≤ X + |V| := by
    calc
      ‖z‖ ≤ ‖(x : ℂ)‖ + ‖(V : ℂ) * I‖ := by
        exact norm_add_le _ _
      _ = |x| + |V| := by simp
      _ ≤ X + |V| := add_le_add habsx le_rfl
  have hzY : ‖z‖ ≤ Y := by
    dsimp [Y, cubicAFEHorizontalScale]
    linarith [norm_nonneg (cubicCriticalPoint t),
      norm_nonneg (1 - cubicCriticalPoint t)]
  have hsplus : ‖s + z‖ ≤ Y := by
    calc
      ‖s + z‖ ≤ ‖s‖ + ‖z‖ := norm_add_le _ _
      _ ≤ Y := by
        dsimp [Y, cubicAFEHorizontalScale, s, u]
        linarith [norm_nonneg (1 - cubicCriticalPoint t)]
  have husub : ‖u - z‖ ≤ Y := by
    calc
      ‖u - z‖ ≤ ‖u‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ Y := by
        dsimp [Y, cubicAFEHorizontalScale, s, u]
        linarith [norm_nonneg (cubicCriticalPoint t)]
  have huplus : ‖u + z‖ ≤ Y := by
    calc
      ‖u + z‖ ≤ ‖u‖ + ‖z‖ := norm_add_le _ _
      _ ≤ Y := by
        dsimp [Y, cubicAFEHorizontalScale, s, u]
        linarith [norm_nonneg (cubicCriticalPoint t)]
  have hssub : ‖s - z‖ ≤ Y := by
    calc
      ‖s - z‖ ≤ ‖s‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ Y := by
        dsimp [Y, cubicAFEHorizontalScale, s, u]
        linarith [norm_nonneg (1 - cubicCriticalPoint t)]
  have hsplus_re : (s + z).re = 1 / 2 + x := by
    simp [s, z, cubicCriticalPoint]
  have huplus_re : (u + z).re = 1 / 2 + x := by
    norm_num [u, s, z, cubicCriticalPoint]
  have hCZs : ‖completedRiemannZeta₀ (s + z)‖ ≤ C := by
    apply hCZ
    · rw [hsplus_re]
      linarith
    · rw [hsplus_re]
      linarith
  have hCZu : ‖completedRiemannZeta₀ (u + z)‖ ≤ C := by
    apply hCZ
    · rw [huplus_re]
      linarith
    · rw [huplus_re]
      linarith
  have hYsq : Y ≤ Y ^ 2 := by
    calc
      Y = Y * 1 := by ring
      _ ≤ Y * Y := mul_le_mul_of_nonneg_left hY (by linarith)
      _ = Y ^ 2 := by ring
  have hprod1 :
      ‖completedRiemannZeta₀ (s + z) * (s + z) * (u - z)‖ ≤
        C * Y ^ 2 := by
    rw [norm_mul, norm_mul]
    calc
      ‖completedRiemannZeta₀ (s + z)‖ * ‖s + z‖ * ‖u - z‖ ≤
          C * Y * Y := by gcongr
      _ = C * Y ^ 2 := by ring
  have hprod2 :
      ‖completedRiemannZeta₀ (u + z) * (u + z) * (s - z)‖ ≤
        C * Y ^ 2 := by
    rw [norm_mul, norm_mul]
    calc
      ‖completedRiemannZeta₀ (u + z)‖ * ‖u + z‖ * ‖s - z‖ ≤
          C * Y * Y := by gcongr
      _ = C * Y ^ 2 := by ring
  have hbracket1 :
      ‖completedRiemannZeta₀ (s + z) * (s + z) * (u - z) -
          (u - z) - (s + z)‖ ≤ (C + 2) * Y ^ 2 := by
    calc
      _ ≤ ‖completedRiemannZeta₀ (s + z) * (s + z) * (u - z)‖ +
          ‖u - z‖ + ‖s + z‖ := by
            calc
              _ ≤ ‖completedRiemannZeta₀ (s + z) * (s + z) * (u - z) -
                  (u - z)‖ + ‖s + z‖ := norm_sub_le _ _
              _ ≤ (‖completedRiemannZeta₀ (s + z) * (s + z) * (u - z)‖ +
                  ‖u - z‖) + ‖s + z‖ := by
                gcongr
                exact norm_sub_le _ _
      _ ≤ C * Y ^ 2 + Y + Y := by gcongr
      _ ≤ (C + 2) * Y ^ 2 := by nlinarith
  have hbracket2 :
      ‖completedRiemannZeta₀ (u + z) * (u + z) * (s - z) -
          (s - z) - (u + z)‖ ≤ (C + 2) * Y ^ 2 := by
    calc
      _ ≤ ‖completedRiemannZeta₀ (u + z) * (u + z) * (s - z)‖ +
          ‖s - z‖ + ‖u + z‖ := by
            calc
              _ ≤ ‖completedRiemannZeta₀ (u + z) * (u + z) * (s - z) -
                  (s - z)‖ + ‖u + z‖ := norm_sub_le _ _
              _ ≤ (‖completedRiemannZeta₀ (u + z) * (u + z) * (s - z)‖ +
                  ‖s - z‖) + ‖u + z‖ := by
                gcongr
                exact norm_sub_le _ _
      _ ≤ C * Y ^ 2 + Y + Y := by gcongr
      _ ≤ (C + 2) * Y ^ 2 := by nlinarith
  have hfactor : ‖1 - 4 * z ^ 2‖ ≤ 5 * Y ^ 2 := by
    calc
      ‖1 - 4 * z ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖4 * z ^ 2‖ := norm_sub_le _ _
      _ = 1 + 4 * ‖z‖ ^ 2 := by norm_num [norm_mul, norm_pow]
      _ ≤ 1 + 4 * Y ^ 2 := by gcongr
      _ ≤ 5 * Y ^ 2 := by nlinarith
  have hxSq : x ^ 2 ≤ X ^ 2 := by
    nlinarith [sq_nonneg (X - |x|), sq_abs x]
  have hzsqre : (z ^ 2).re = x ^ 2 - V ^ 2 := by
    rw [pow_two, mul_re]
    simp [z]
    ring
  have hexp : ‖Complex.exp (z ^ 2)‖ ≤ Real.exp (X ^ 2 - V ^ 2) := by
    rw [Complex.norm_exp, hzsqre]
    exact Real.exp_le_exp.mpr (by linarith)
  have hext : ‖cubicAFECompletedExtension t z‖ ≤
      K * Y ^ 6 * Real.exp (-V ^ 2) := by
    change ‖Complex.exp (z ^ 2) * (1 - 4 * z ^ 2) / (s ^ 2 * u ^ 2) *
      (completedRiemannZeta₀ (s + z) * (s + z) * (u - z) -
        (u - z) - (s + z)) *
      (completedRiemannZeta₀ (u + z) * (u + z) * (s - z) -
        (s - z) - (u + z))‖ ≤ _
    simp only [norm_mul, norm_div]
    calc
      ‖Complex.exp (z ^ 2)‖ * ‖1 - 4 * z ^ 2‖ / (‖s ^ 2‖ * ‖u ^ 2‖) *
            ‖completedRiemannZeta₀ (s + z) * (s + z) * (u - z) -
              (u - z) - (s + z)‖ *
          ‖completedRiemannZeta₀ (u + z) * (u + z) * (s - z) -
              (s - z) - (u + z)‖ ≤
          Real.exp (X ^ 2 - V ^ 2) * (5 * Y ^ 2) /
              (‖s ^ 2‖ * ‖u ^ 2‖) * ((C + 2) * Y ^ 2) *
            ((C + 2) * Y ^ 2) := by gcongr
      _ = K * Y ^ 6 * Real.exp (-V ^ 2) := by
        rw [show X ^ 2 - V ^ 2 = X ^ 2 + (-V ^ 2) by ring,
          Real.exp_add]
        simp only [K, div_eq_mul_inv]
        ring
  have hzNorm : 1 ≤ ‖z‖ := by
    have him : |V| ≤ ‖z‖ := by
      simpa [z] using abs_im_le_norm z
    rw [habsV] at him
    linarith
  unfold cubicAFECompletedIntegrand
  rw [norm_div]
  calc
    ‖cubicAFECompletedExtension t z‖ / ‖z‖ ≤
        ‖cubicAFECompletedExtension t z‖ / 1 := by
      exact div_le_div_of_nonneg_left (norm_nonneg _) zero_lt_one hzNorm
    _ ≤ K * Y ^ 6 * Real.exp (-V ^ 2) := by simpa using hext
    _ = K * cubicAFEHorizontalScale t X V ^ 6 * Real.exp (-V ^ 2) := rfl

private theorem tendsto_const_mul_add_pow_six_mul_exp_neg_sq
    {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) :
    Tendsto (fun V : ℝ ↦ K * (A + V) ^ 6 * Real.exp (-V ^ 2))
      atTop (nhds 0) := by
  have hgaussCocompact :=
    tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
      (a := (1 : ℝ)) one_pos (6 : ℝ)
  have hgauss : Tendsto
      (fun V : ℝ ↦ V ^ 6 * Real.exp (-V ^ 2)) atTop (nhds 0) := by
    apply (hgaussCocompact.mono_left atTop_le_cocompact).congr'
    filter_upwards [eventually_gt_atTop 0] with V hV
    simp [abs_of_pos hV]
  have hmajor : Tendsto
      (fun V : ℝ ↦ (64 * K) * (V ^ 6 * Real.exp (-V ^ 2)))
      atTop (nhds 0) := by simpa using hgauss.const_mul (64 * K)
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop 0] with V hV
    positivity
  · filter_upwards [eventually_ge_atTop (max A 1)] with V hV
    have hVA : A ≤ V := le_trans (le_max_left _ _) hV
    have hV0 : 0 ≤ V := le_trans zero_le_one (le_trans (le_max_right _ _) hV)
    have hAV0 : 0 ≤ A + V := add_nonneg hA hV0
    have hAV : A + V ≤ 2 * V := by linarith
    have hpow : (A + V) ^ 6 ≤ (2 * V) ^ 6 := by gcongr
    calc
      K * (A + V) ^ 6 * Real.exp (-V ^ 2) ≤
          K * (2 * V) ^ 6 * Real.exp (-V ^ 2) := by gcongr
      _ = (64 * K) * (V ^ 6 * Real.exp (-V ^ 2)) := by ring

/-- The top horizontal edge of the finite AFE rectangle tends to zero at
infinite height.  This is an unconditional consequence of the actual
completed-zeta Mellin representation and the Gaussian kernel. -/
theorem tendsto_cubicAFECompletedIntegrand_horizontalIntegral
    (t : ℝ) {X : ℝ} (hX : 0 < X) :
    Tendsto
      (fun V : ℝ ↦ ∫ x : ℝ in -X..X,
        cubicAFECompletedIntegrand t ((x : ℂ) + (V : ℂ) * I))
      atTop (nhds 0) := by
  obtain ⟨K, hK, hpoint⟩ :=
    exists_norm_cubicAFECompletedIntegrand_horizontal_le t hX.le
  let A : ℝ :=
    1 + ‖cubicCriticalPoint t‖ + ‖1 - cubicCriticalPoint t‖ + X
  have hA : 0 ≤ A := by
    dsimp [A]
    linarith [norm_nonneg (cubicCriticalPoint t),
      norm_nonneg (1 - cubicCriticalPoint t)]
  have hmajor : Tendsto
      (fun V : ℝ ↦ (2 * X * K) * (A + V) ^ 6 * Real.exp (-V ^ 2))
      atTop (nhds 0) :=
    tendsto_const_mul_add_pow_six_mul_exp_neg_sq hA
      (mul_nonneg (mul_nonneg (by norm_num) hX.le) hK)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hmajor
  filter_upwards [eventually_ge_atTop 1] with V hV
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ ↦
      cubicAFECompletedIntegrand t ((x : ℂ) + (V : ℂ) * I))
    (a := -X) (b := X)
    (C := K * cubicAFEHorizontalScale t X V ^ 6 * Real.exp (-V ^ 2))
    (fun x hx ↦ hpoint (uIoc_subset_uIcc hx) hV)
  have hscale : cubicAFEHorizontalScale t X V = A + V := by
    simp [cubicAFEHorizontalScale, A, abs_of_nonneg (by linarith : 0 ≤ V)]
  calc
    ‖∫ x : ℝ in -X..X,
        cubicAFECompletedIntegrand t ((x : ℂ) + (V : ℂ) * I)‖ ≤
        (K * (A + V) ^ 6 * Real.exp (-V ^ 2)) * |X - -X| := by
      simpa [hscale] using hbound
    _ = (2 * X * K) * (A + V) ^ 6 * Real.exp (-V ^ 2) := by
      rw [abs_of_nonneg (by linarith : 0 ≤ X - -X)]
      ring

/-- Infinite-height right-vertical-line form of the completed AFE contour
identity. -/
theorem tendsto_cubicAFECompletedIntegrand_verticalIntegral
    (t : ℝ) {X : ℝ} (hX : 0 < X) :
    Tendsto
      (fun V : ℝ ↦ ∫ y : ℝ in -V..V,
        cubicAFECompletedIntegrand t ((X : ℂ) + (y : ℂ) * I))
      atTop
      (nhds (Real.pi *
        (completedRiemannZeta (cubicCriticalPoint t) *
          completedRiemannZeta (1 - cubicCriticalPoint t)))) := by
  let P : ℂ := Real.pi *
    (completedRiemannZeta (cubicCriticalPoint t) *
      completedRiemannZeta (1 - cubicCriticalPoint t))
  have hhorizontal :=
    tendsto_cubicAFECompletedIntegrand_horizontalIntegral t hX
  have htarget : Tendsto
      (fun V : ℝ ↦ P - I *
        (∫ x : ℝ in -X..X,
          cubicAFECompletedIntegrand t ((x : ℂ) + (V : ℂ) * I)))
      atTop (nhds P) := by
    simpa using tendsto_const_nhds.sub (hhorizontal.const_mul I)
  apply htarget.congr'
  filter_upwards [eventually_gt_atTop 0] with V hV
  have hid := cubicAFEFiniteVerticalIdentity t hX hV
  change
    P - I * (∫ x : ℝ in -X..X,
      cubicAFECompletedIntegrand t ((x : ℂ) + (V : ℂ) * I)) =
      (∫ y : ℝ in -V..V,
        cubicAFECompletedIntegrand t ((X : ℂ) + (y : ℂ) * I))
  exact (eq_sub_of_add_eq hid).symm

end MWKFCubic
end PrimeNumberTheorem
