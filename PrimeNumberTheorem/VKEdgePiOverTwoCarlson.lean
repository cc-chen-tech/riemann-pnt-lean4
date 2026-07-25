import PrimeNumberTheorem.CarlsonAsymptotic
import Mathlib.Analysis.Real.Pi.Bounds

open Complex Filter Asymptotics

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The point on the vertical line `Re s = beta` whose ordinate is the
`(2k+1)`-st positive odd multiple of `gamma`. -/
def oddHarmonicPoint (beta gamma : ℝ) (k : ℕ) : ℂ :=
  (beta : ℂ) + I * ((((2 * k + 1 : ℕ) : ℝ) * gamma : ℝ) : ℂ)

@[simp]
theorem oddHarmonicPoint_re (beta gamma : ℝ) (k : ℕ) :
    (oddHarmonicPoint beta gamma k).re = beta := by
  simp [oddHarmonicPoint]

@[simp]
theorem oddHarmonicPoint_im (beta gamma : ℝ) (k : ℕ) :
    (oddHarmonicPoint beta gamma k).im =
      ((2 * k + 1 : ℕ) : ℝ) * gamma := by
  simp [oddHarmonicPoint]

theorem oddHarmonicPoint_injective (beta : ℝ) {gamma : ℝ}
    (hgamma : 0 < gamma) :
    Function.Injective (oddHarmonicPoint beta gamma) := by
  intro k l hkl
  have him := congrArg Complex.im hkl
  simp only [oddHarmonicPoint_im] at him
  have hcast : (k : ℝ) = l := by
    push_cast at him
    nlinarith
  exact_mod_cast hcast

/-- If the multiplicity-counted zero density up to
`(2M+2) * gamma` is at most `M`, then the first `M+1` positive odd multiples
of `gamma` on a fixed line in the critical strip cannot all be zeta zeros. -/
theorem exists_riemannZeta_ne_zero_at_oddHarmonic_of_zeroDensityCount_le
    {beta gamma sigma : ℝ} {M : ℕ}
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (hgamma : 0 < gamma) (hsigma : sigma < beta)
    (hcount :
      ZeroDensity.zeroDensityCount sigma
          (((2 * M + 2 : ℕ) : ℝ) * gamma) ≤ M) :
    ∃ k : ℕ, k < M + 1 ∧
      riemannZeta (oddHarmonicPoint beta gamma k) ≠ 0 := by
  classical
  by_contra hmissing
  push Not at hmissing
  let S : Finset ℂ :=
    (Finset.range (M + 1)).image (oddHarmonicPoint beta gamma)
  have hS_subset :
      S ⊆ ZeroDensity.zeroDensityZerosFinset sigma
        (((2 * M + 2 : ℕ) : ℝ) * gamma) := by
    intro rho hrho
    rcases Finset.mem_image.mp hrho with ⟨k, hk, rfl⟩
    have hklt : k < M + 1 := Finset.mem_range.mp hk
    have hzero :
        riemannZeta (oddHarmonicPoint beta gamma k) = 0 :=
      hmissing k hklt
    have hodd_pos : 0 < (2 * k + 1 : ℕ) := by omega
    have him_pos :
        0 < (oddHarmonicPoint beta gamma k).im := by
      simp only [oddHarmonicPoint_im]
      exact mul_pos (by exact_mod_cast hodd_pos) hgamma
    have hodd_lt : 2 * k + 1 < 2 * M + 2 := by omega
    have him_le :
        (oddHarmonicPoint beta gamma k).im ≤
          ((2 * M + 2 : ℕ) : ℝ) * gamma := by
      simp only [oddHarmonicPoint_im]
      exact (mul_lt_mul_of_pos_right (by exact_mod_cast hodd_lt) hgamma).le
    exact ZeroDensity.mem_zeroDensityZerosFinset.mpr
      ⟨⟨hzero, by simpa using hbeta0, by simpa using hbeta1⟩,
        him_pos, him_le, by simpa using hsigma⟩
  have hcard : S.card = M + 1 := by
    dsimp [S]
    rw [Finset.card_image_of_injective _
      (oddHarmonicPoint_injective beta hgamma)]
    simp
  have hmult_one :
      ∀ rho ∈ S, 1 ≤ analyticOrderNatAt riemannZeta rho := by
    intro rho hrho
    have hrho_density :=
      ZeroDensity.mem_zeroDensityZerosFinset.mp (hS_subset hrho)
    exact
      (ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
        (by
          intro hrho_one
          have hre := congrArg Complex.re hrho_one
          simp at hre
          linarith [hrho_density.1.2.2])
        hrho_density.1.1)
  have hcard_le_sum :
      S.card ≤ ∑ rho ∈ S, analyticOrderNatAt riemannZeta rho := by
    simpa using
      S.card_nsmul_le_sum
        (fun rho => analyticOrderNatAt riemannZeta rho) 1 hmult_one
  have hsum_le_count :
      (∑ rho ∈ S, analyticOrderNatAt riemannZeta rho) ≤
        ZeroDensity.zeroDensityCount sigma
          (((2 * M + 2 : ℕ) : ℝ) * gamma) := by
    unfold ZeroDensity.zeroDensityCount
    exact Finset.sum_le_sum_of_subset_of_nonneg hS_subset
      (fun _ _ _ => Nat.zero_le _)
  omega

/-- The denominator in the explicit missing-odd-harmonic dual certificate. -/
def missingHarmonicDenominator (n : ℕ) : ℝ :=
  2 / Real.pi -
    Real.sin (1 / (4 * (n : ℝ))) / (Real.pi * (n : ℝ))

/-- The normalized oscillation lower bound supplied by a missing odd
harmonic `n`. -/
def missingHarmonicLowerBound (n : ℕ) : ℝ :=
  1 / missingHarmonicDenominator n

theorem missingHarmonicDenominator_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < missingHarmonicDenominator n := by
  have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := zero_lt_one.trans_le hn_real
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hsin_le :
      Real.sin (1 / (4 * (n : ℝ))) ≤ 1 :=
    Real.sin_le_one _
  have hterm_lt :
      Real.sin (1 / (4 * (n : ℝ))) / (Real.pi * (n : ℝ)) <
        2 / Real.pi := by
    rw [div_lt_div_iff₀ (mul_pos hpi_pos hn_pos) hpi_pos]
    nlinarith
  unfold missingHarmonicDenominator
  linarith

theorem missingHarmonicDenominator_lt_two_div_pi {n : ℕ} (hn : 1 ≤ n) :
    missingHarmonicDenominator n < 2 / Real.pi := by
  have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := zero_lt_one.trans_le hn_real
  have hangle_pos : 0 < 1 / (4 * (n : ℝ)) := by positivity
  have hangle_le : 1 / (4 * (n : ℝ)) ≤ (1 : ℝ) / 4 := by
    (gcongr; nlinarith)
  have hangle_lt_pi : 1 / (4 * (n : ℝ)) < Real.pi := by
    calc
      1 / (4 * (n : ℝ)) ≤ (1 : ℝ) / 4 := hangle_le
      _ < Real.pi := by nlinarith [Real.pi_gt_three]
  have hsin_pos :
      0 < Real.sin (1 / (4 * (n : ℝ))) :=
    Real.sin_pos_of_pos_of_lt_pi hangle_pos hangle_lt_pi
  have hterm_pos :
      0 <
        Real.sin (1 / (4 * (n : ℝ))) /
          (Real.pi * (n : ℝ)) := by
    exact div_pos hsin_pos (mul_pos Real.pi_pos hn_pos)
  unfold missingHarmonicDenominator
  linarith

theorem pi_div_two_lt_missingHarmonicLowerBound {n : ℕ} (hn : 1 ≤ n) :
    Real.pi / 2 < missingHarmonicLowerBound n := by
  have hden_pos := missingHarmonicDenominator_pos hn
  have hden_lt := missingHarmonicDenominator_lt_two_div_pi hn
  calc
    Real.pi / 2 = 1 / (2 / Real.pi) := by
      field_simp [Real.pi_ne_zero]
    _ < 1 / missingHarmonicDenominator n :=
      one_div_lt_one_div_of_lt hden_pos hden_lt
    _ = missingHarmonicLowerBound n := rfl

/-- The uniform lower bound when the missing odd harmonic is known only to
lie among `1,3,...,2M+1`. -/
def finiteOddHarmonicLowerBound (M : ℕ) : ℝ :=
  missingHarmonicLowerBound (2 * M + 1)

theorem pi_div_two_lt_finiteOddHarmonicLowerBound (M : ℕ) :
    Real.pi / 2 < finiteOddHarmonicLowerBound M := by
  exact pi_div_two_lt_missingHarmonicLowerBound (by omega)

/-- Carlson's fixed-line zero-density estimate is sublinear for every
`sigma` strictly between `1/2` and `1`. -/
theorem carlson_zeroDensity_isLittleO_id {sigma : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigma1 : sigma < 1) :
    (fun T : ℝ => (ZeroDensity.zeroDensityCount sigma T : ℝ)) =o[atTop]
      (id : ℝ → ℝ) := by
  let alpha : ℝ := 4 * sigma * (1 - sigma)
  have halpha_lt : alpha < 1 := by
    dsimp [alpha]
    nlinarith [sq_nonneg (2 * sigma - 1)]
  have hgap : 0 < 1 - alpha := sub_pos.mpr halpha_lt
  have hlog :
      (fun T : ℝ => Real.log T ^ (4 : ℕ)) =o[atTop]
        (fun T : ℝ => T ^ (1 - alpha)) :=
    (isLittleO_log_rpow_rpow_atTop (4 : ℝ) hgap).congr_left
      (fun T => Real.rpow_natCast (Real.log T) 4)
  have hmodel :
      (fun T : ℝ => T ^ alpha * Real.log T ^ (4 : ℕ)) =o[atTop]
        (id : ℝ → ℝ) := by
    apply Asymptotics.isLittleO_of_tendsto'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      intro hid
      exact (hT.ne' (by simpa using hid)).elim
    · refine hlog.tendsto_div_nhds_zero.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      simp only [id_eq]
      rw [Real.rpow_sub hT, Real.rpow_one]
      field_simp [(Real.rpow_pos_of_pos hT alpha).ne']
  exact
    (CarlsonZeroDensity.carlson_zeroDensity_isBigO hsigma hsigma1).trans_isLittleO
      (by simpa [alpha] using hmodel)

/-- Any sublinear multiplicity count eventually falls below an odd-harmonic
pigeonhole budget along the heights `(2M+2) * gamma`. -/
theorem exists_oddHarmonicBudget_of_zeroDensity_isLittleO
    {sigma gamma : ℝ} (hgamma : 0 < gamma)
    (hdensity :
      (fun T : ℝ => (ZeroDensity.zeroDensityCount sigma T : ℝ)) =o[atTop]
        (id : ℝ → ℝ)) :
    ∃ M : ℕ, 1 ≤ M ∧
      ZeroDensity.zeroDensityCount sigma
          (((2 * M + 2 : ℕ) : ℝ) * gamma) ≤ M := by
  have hc : 0 < 1 / (4 * gamma) := by positivity
  rcases eventually_atTop.mp (hdensity.def hc) with ⟨A, hA⟩
  obtain ⟨M, hM⟩ := exists_nat_ge (max 1 (A / gamma))
  have hM_real : (1 : ℝ) ≤ M :=
    (le_max_left 1 (A / gamma)).trans hM
  have hM_nat : 1 ≤ M := by exact_mod_cast hM_real
  let T : ℝ := (((2 * M + 2 : ℕ) : ℝ) * gamma)
  have hT_eq : T = (2 * (M : ℝ) + 2) * gamma := by
    simp [T]
  have hA_le_Mgamma : A ≤ (M : ℝ) * gamma := by
    apply (div_le_iff₀ hgamma).mp
    exact (le_max_right 1 (A / gamma)).trans hM
  have hT_ge : A ≤ T := by
    rw [hT_eq]
    nlinarith
  have hT_pos : 0 < T := by
    rw [hT_eq]
    positivity
  have hbound := hA T hT_ge
  have hbound' :
      (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        (1 / (4 * gamma)) * T := by
    change
      |(ZeroDensity.zeroDensityCount sigma T : ℝ)| ≤
        (1 / (4 * gamma)) * |T| at hbound
    rw [abs_of_nonneg (by positivity), abs_of_pos hT_pos] at hbound
    exact hbound
  have hscale :
      (1 / (4 * gamma)) * T = ((M : ℝ) + 1) / 2 := by
    rw [hT_eq]
    field_simp [ne_of_gt hgamma]
    ring
  have hcount_real :
      (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤ M := by
    rw [hscale] at hbound'
    nlinarith
  refine ⟨M, hM_nat, ?_⟩
  change ZeroDensity.zeroDensityCount sigma T ≤ M
  exact_mod_cast hcount_real

/-- For every fixed right-hand zeta zero line, Carlson density supplies a
missing odd harmonic together with a strictly positive gap above `pi/2` in
the dual-certificate constant. -/
theorem exists_missing_oddHarmonic_with_strict_gap_of_carlson
    {beta gamma sigma : ℝ}
    (hbeta1 : beta < 1) (hgamma : 0 < gamma)
    (hsigmaHalf : 1 / 2 < sigma) (hsigmaBeta : sigma < beta) :
    ∃ k : ℕ,
      riemannZeta (oddHarmonicPoint beta gamma k) ≠ 0 ∧
        Real.pi / 2 < missingHarmonicLowerBound (2 * k + 1) := by
  have hsigma1 : sigma < 1 := hsigmaBeta.trans hbeta1
  have hbeta0 : 0 < beta := by linarith
  rcases exists_oddHarmonicBudget_of_zeroDensity_isLittleO hgamma
      (carlson_zeroDensity_isLittleO_id hsigmaHalf hsigma1) with
    ⟨M, _hM, hcount⟩
  rcases
      exists_riemannZeta_ne_zero_at_oddHarmonic_of_zeroDensityCount_le
        hbeta0 hbeta1 hgamma hsigmaBeta hcount with
    ⟨k, _hk, hkzero⟩
  exact ⟨k, hkzero, pi_div_two_lt_missingHarmonicLowerBound (by omega)⟩

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
