import PrimeNumberTheorem.LeftVerticalEdge
import PrimeNumberTheorem.QuantitativeGoodHeight
import ZeroFreeRegion.ShiftedJensen

open Complex Filter MeasureTheory Set Topology

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- A good contour height excludes every zeta zero on either horizontal line
with that absolute height, including points outside the open critical strip. -/
theorem riemannZeta_ne_zero_on_goodHeight_horizontal
    {T t σ : ℝ} (hT : 0 < T) (ht : |t| = T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    riemannZeta ((σ : ℂ) + I * t) ≠ 0 := by
  let s : ℂ := (σ : ℂ) + I * t
  have htne : t ≠ 0 := by
    intro h
    subst t
    simp at ht
    linarith
  by_cases hσ0 : σ ≤ 0
  · apply PrimeNumberTheorem.riemannZeta_ne_zero_of_re_le_zero
      (s := s) (by simpa [s] using hσ0)
    intro n hn
    have him := congrArg Complex.im hn
    apply htne
    simpa [s] using him
  · have hσpos : 0 < σ := lt_of_not_ge hσ0
    by_cases hσ1 : 1 ≤ σ
    · exact riemannZeta_ne_zero_of_one_le_re (by simpa [s] using hσ1)
    · have hσlt : σ < 1 := lt_of_not_ge hσ1
      intro hzero
      have hnontrivial : RiemannHypothesis.IsNontrivialZero s := by
        exact ⟨hzero, by simpa [s] using hσpos, by simpa [s] using hσlt⟩
      exact (hgood s hnontrivial) (by simpa [s] using ht)

/-- Separation of absolute zero ordinates gives the same lower bound for the
complex distance from every point on the corresponding horizontal line. -/
lemma horizontal_norm_sub_ge_of_abs_height_separated
    {δ T t σ : ℝ} {u : ℂ} (ht : |t| = T)
    (hsep : δ ≤ abs (T - abs u.im)) :
    δ ≤ ‖((σ : ℂ) + I * t) - u‖ := by
  calc
    δ ≤ abs (T - abs u.im) := hsep
    _ = abs (abs t - abs u.im) := by rw [ht]
    _ ≤ |t - u.im| := abs_abs_sub_abs_le_abs_sub t u.im
    _ = |((((σ : ℂ) + I * t) - u).im)| := by simp
    _ ≤ ‖((σ : ℂ) + I * t) - u‖ := Complex.abs_im_le_norm _

/-- Every divisor point in the shifted high Jensen disk is a nontrivial zeta
zero.  The disk lies strictly to the right of `Re(s)=0`, while the Euler
product excludes zeros on and to the right of `Re(s)=1`. -/
lemma isNontrivialZero_of_mem_shifted_divisor_support
    {t : ℝ} (ht : 4 ≤ |t|) {u : ℂ}
    (hu : u ∈ (MeromorphicOn.divisor riemannZeta
      (Metric.closedBall ((3 / 2 : ℂ) + I * t) (7 / 5 : ℝ))).support) :
    RiemannHypothesis.IsNontrivialZero u := by
  let c : ℂ := (3 / 2 : ℂ) + I * t
  let D := MeromorphicOn.divisor riemannZeta
    (Metric.closedBall c (7 / 5 : ℝ))
  have huD : u ∈ D.support := by simpa [D, c] using hu
  have hu_closed : u ∈ Metric.closedBall c (7 / 5 : ℝ) :=
    D.supportWithinDomain huD
  have havoid : ∀ z : ℂ,
      z ∈ Metric.closedBall c (7 / 5 : ℝ) → z ≠ 1 := by
    intro z hz
    exact ZeroFreeRegion.closedBall_sigma_it_ne_one_of_height_add_le
      (z := z) (σ := (3 / 2 : ℝ)) (t := t) (R := (7 / 5 : ℝ))
      (H := |t| - 7 / 5)
      (by simpa [c] using hz) (by linarith) (by linarith)
  have hzero : riemannZeta u = 0 := by
    by_contra hne
    have hu_analytic : AnalyticAt ℂ riemannZeta u :=
      ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one u
        (havoid u hu_closed)
    have horder : meromorphicOrderAt riemannZeta u = 0 :=
      (hu_analytic.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).2 hne
    have hDu0 : D u = 0 := by
      dsimp [D]
      rw [MeromorphicOn.divisor_apply
        (ZeroFreeRegion.meromorphicOn_riemannZeta_closedBall c (7 / 5 : ℝ))
        hu_closed, horder]
      simp
    have hDne : D u ≠ 0 := by
      simpa [Function.mem_support] using huD
    exact hDne hDu0
  have hdist : ‖u - c‖ ≤ (7 / 5 : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu_closed
  have hre_abs : |u.re - 3 / 2| ≤ (7 / 5 : ℝ) := by
    have hre := Complex.abs_re_le_norm (u - c)
    simpa [c] using hre.trans hdist
  have hre_pos : 0 < u.re := by
    rw [abs_le] at hre_abs
    linarith
  have hre_lt : u.re < 1 := by
    by_contra h
    exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h)) hzero
  exact ⟨hzero, hre_pos, hre_lt⟩

/-- Every sufficiently high unit interval contains a good contour height on
which the full logarithmic derivative is `O(log^2 A)` throughout the shifted
right half of the central band.  This combines the shifted Jensen regular
part, its local divisor-mass bound, and logarithmic good-height separation. -/
theorem exists_goodHeight_Icc_norm_logDeriv_central_right_le_log_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ t : ℝ, |t| = T →
            ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 2 →
              ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
                C * (1 + Real.log (A + 6)) ^ 2 := by
  rcases ExplicitFormulaAux.exists_goodHeight_Icc_logarithmically_separated with
    ⟨Bsep, hBsep, hchoose⟩
  rcases ZeroFreeRegion.exists_shifted_disk_regularized_logDeriv_riemannZeta_log_bound with
    ⟨Breg, hBreg, hregular⟩
  rcases ZeroFreeRegion.exists_finsum_divisor_riemannZeta_shifted_disk_log_bound with
    ⟨Bmass, hBmass, hmass_bound⟩
  let C : ℝ := Breg + 4 * Bmass * (Bsep + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hheight_sep⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro t ht_abs
  intro σ hσlo hσhi
  let z : ℂ := (σ : ℂ) + I * t
  let c : ℂ := (3 / 2 : ℂ) + I * t
  let D := MeromorphicOn.divisor riemannZeta
    (Metric.closedBall c (7 / 5 : ℝ))
  let LA : ℝ := 1 + Real.log (A + 6)
  let LT : ℝ := 1 + Real.log (|t| + 5)
  let delta : ℝ :=
    1 / ((4 : ℝ) * (Bsep * (1 + Real.log (A + 6)) + 1))
  have hT4 : 4 ≤ |t| := by rw [ht_abs]; exact hA.trans hT.1
  have hzeta : riemannZeta z ≠ 0 := by
    exact riemannZeta_ne_zero_on_goodHeight_horizontal
      (T := T) (t := t) (σ := σ) (by linarith [hA, hT.1]) ht_abs hgood
  have hzball : z ∈ Metric.closedBall c 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : z - c = ((σ - 3 / 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [z, c]
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith
  have hreg : ‖logDeriv riemannZeta z -
      ∑ᶠ u, (D u : ℂ) * (z - u)⁻¹‖ ≤ Breg * LT := by
    simpa [z, c, D, LT] using hregular t hT4 z hzball hzeta
  have hmass : (∑ᶠ u, (D u : ℝ)) ≤ Bmass * LT := by
    simpa [c, D, LT] using hmass_bound t hT4
  have havoid : ∀ u : ℂ,
      u ∈ Metric.closedBall c (7 / 5 : ℝ) → u ≠ 1 := by
    intro u hu
    exact ZeroFreeRegion.closedBall_sigma_it_ne_one_of_height_add_le
      (z := u) (σ := (3 / 2 : ℝ)) (t := t) (R := (7 / 5 : ℝ))
      (H := |t| - 7 / 5)
      (by simpa [c] using hu) (by linarith) (by linarith)
  have hD : ∀ u, 0 ≤ D u := by
    exact ZeroFreeRegion.divisor_riemannZeta_closedBall_nonneg havoid
  have hfinite : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall c (7 / 5 : ℝ))
  have hdelta : 0 < delta := by
    dsimp [delta]
    apply one_div_pos.mpr
    have hlogA : 0 ≤ Real.log (A + 6) :=
      Real.log_nonneg (by linarith)
    positivity
  have hsepD : ∀ u ∈ D.support, delta ≤ ‖z - u‖ := by
    intro u hu
    have hu_nontrivial : RiemannHypothesis.IsNontrivialZero u :=
      isNontrivialZero_of_mem_shifted_divisor_support hT4
        (by simpa [D, c] using hu)
    have hu_height := hheight_sep u hu_nontrivial
    have hu_norm := horizontal_norm_sub_ge_of_abs_height_separated
      (σ := σ) (u := u) ht_abs hu_height
    simpa [z, delta] using hu_norm
  have hprincipal :
      ‖∑ᶠ u, (D u : ℂ) * (z - u)⁻¹‖ ≤
        (∑ᶠ u, (D u : ℝ)) / delta := by
    exact ZeroFreeRegion.norm_finsum_divisor_mul_inv_le_mass_div
      hfinite hD hdelta hsepD
  have hLAone : 1 ≤ LA := by
    dsimp [LA]
    have : 1 ≤ A + 6 := by linarith
    exact le_add_of_nonneg_right (Real.log_nonneg this)
  have hLTnonneg : 0 ≤ LT := by
    dsimp [LT]
    have : 1 ≤ |t| + 5 := by linarith [abs_nonneg t]
    linarith [Real.log_nonneg this]
  have hLTLA : LT ≤ LA := by
    have hlog : Real.log (|t| + 5) ≤ Real.log (A + 6) := by
      apply Real.log_le_log
      · positivity
      · rw [ht_abs]
        linarith [hT.2]
    simpa [LT, LA] using add_le_add_left hlog 1
  have hregSq :
      ‖logDeriv riemannZeta z -
          ∑ᶠ u, (D u : ℂ) * (z - u)⁻¹‖ ≤ Breg * LA ^ 2 := by
    apply hreg.trans
    calc
      Breg * LT ≤ Breg * LA := mul_le_mul_of_nonneg_left hLTLA hBreg
      _ ≤ Breg * LA ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hBreg
        nlinarith [sq_nonneg (LA - 1)]
  have hprincipalSq :
      ‖∑ᶠ u, (D u : ℂ) * (z - u)⁻¹‖ ≤
        (4 * Bmass * (Bsep + 1)) * LA ^ 2 := by
    apply hprincipal.trans
    calc
      (∑ᶠ u, (D u : ℝ)) / delta ≤ (Bmass * LT) / delta :=
        div_le_div_of_nonneg_right hmass hdelta.le
      _ = (Bmass * LT) * (4 * (Bsep * LA + 1)) := by
        simp [delta, LA, div_eq_mul_inv]
      _ ≤ (Bmass * LA) * (4 * (Bsep * LA + 1)) := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLTLA hBmass)
        positivity
      _ ≤ (Bmass * LA) * (4 * ((Bsep + 1) * LA)) := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg hBmass (zero_le_one.trans hLAone))
        nlinarith
      _ = (4 * Bmass * (Bsep + 1)) * LA ^ 2 := by ring
  have htri : ‖logDeriv riemannZeta z‖ ≤
      ‖logDeriv riemannZeta z -
          ∑ᶠ u, (D u : ℂ) * (z - u)⁻¹‖ +
        ‖∑ᶠ u, (D u : ℂ) * (z - u)⁻¹‖ := by
    calc
      ‖logDeriv riemannZeta z‖ =
          ‖(logDeriv riemannZeta z -
            ∑ᶠ u, (D u : ℂ) * (z - u)⁻¹) +
              ∑ᶠ u, (D u : ℂ) * (z - u)⁻¹‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  calc
    ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ =
        ‖logDeriv riemannZeta z‖ := by rfl
    _ ≤ _ := htri
    _ ≤ Breg * LA ^ 2 +
        (4 * Bmass * (Bsep + 1)) * LA ^ 2 :=
      add_le_add hregSq hprincipalSq
    _ = C * (1 + Real.log (A + 6)) ^ 2 := by
      dsimp [C, LA]
      ring

/-- A logarithmic digamma bound one recurrence step to the left of the
standard `Re z >= 1` region.  The imaginary-height hypothesis uniformly
controls the recurrence term `z⁻¹`. -/
theorem norm_digamma_le_log_of_quarter_le_re
    {z : ℂ} (hre : (1 / 4 : ℝ) ≤ z.re) (him : 1 ≤ |z.im|) :
    ‖Complex.digamma z‖ ≤
      ‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
        Real.log (‖z + 1‖ + 1) := by
  have him_ne : z.im ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at him
    norm_num at him
  have hregular : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m hm
    apply him_ne
    have h := congrArg Complex.im hm
    simpa using h
  have hshift_re : (1 : ℝ) ≤ (z + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hshift := PrimeNumberTheorem.norm_digamma_le_log hshift_re
  have hnorm : (1 : ℝ) ≤ ‖z‖ :=
    him.trans (Complex.abs_im_le_norm z)
  have hinv : ‖z⁻¹‖ ≤ (1 : ℝ) := by
    rw [norm_inv]
    simpa [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnorm)
  have hrec := Complex.digamma_apply_add_one z hregular
  have heq : Complex.digamma z = Complex.digamma (z + 1) - z⁻¹ := by
    linear_combination -hrec
  rw [heq]
  calc
    ‖Complex.digamma (z + 1) - z⁻¹‖ ≤
        ‖Complex.digamma (z + 1)‖ + ‖z⁻¹‖ := norm_sub_le _ _
    _ ≤ (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
          Real.log (‖z + 1‖ + 1)) + 1 := add_le_add hshift hinv
    _ = ‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
          Real.log (‖z + 1‖ + 1) := by ring

/-- On a nonreal horizontal line, the functional equation moves the zeta
logarithmic derivative to the reflected point.  Digamma reflection leaves
both digamma arguments in the right half-plane. -/
theorem neg_logDeriv_riemannZeta_central_eq_right_shift
    {σ T : ℝ} (hT : T ≠ 0)
    (hzs : riemannZeta ((σ : ℂ) + I * T) ≠ 0)
    (hz1s : riemannZeta (1 - ((σ : ℂ) + I * T)) ≠ 0) :
    -logDeriv riemannZeta ((σ : ℂ) + I * T) =
      logDeriv riemannZeta (1 - ((σ : ℂ) + I * T)) - Complex.log Real.pi +
        Complex.digamma ((1 - ((σ : ℂ) + I * T)) / 2) / 2 +
        Complex.digamma (1 - ((σ : ℂ) + I * T) / 2) / 2 -
        ((Real.pi : ℂ) *
          Complex.cot (Real.pi * ((σ : ℂ) + I * T) / 2)) / 2 := by
  let s : ℂ := (σ : ℂ) + I * T
  change -logDeriv riemannZeta s = _
  have hs_im : s.im ≠ 0 := by simpa [s] using hT
  have hs0 : s ≠ 0 := by
    intro hs
    apply hs_im
    simpa using congrArg Complex.im hs
  have hs1 : s ≠ 1 := by
    intro hs
    apply hs_im
    simpa using congrArg Complex.im hs
  have hsGamma : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
    intro n hn
    have him := congrArg Complex.im hn
    apply hT
    simp [s] at him
    linarith
  have h1sGamma : ∀ n : ℕ, (1 - s) / 2 ≠ -(n : ℂ) := by
    intro n hn
    have him := congrArg Complex.im hn
    apply hT
    simp [s] at him
    linarith
  have hbase := neg_logDeriv_riemannZeta_eq_right_shift_add_digamma
    hs0 hs1 hsGamma h1sGamma hzs hz1s
  have hreflect := digamma_eq_one_sub_sub_pi_mul_cot
    (s := s / 2) (by simpa using hs_im)
  have hresult :
      -logDeriv riemannZeta s =
        logDeriv riemannZeta (1 - s) - Complex.log Real.pi +
          Complex.digamma ((1 - s) / 2) / 2 +
          Complex.digamma (1 - s / 2) / 2 -
          ((Real.pi : ℂ) * Complex.cot (Real.pi * s / 2)) / 2 := by
    rw [hbase, hreflect]
    ring
  simpa [s] using hresult

/-- A bound for the reflected logarithmic derivative controls the entire
left half of the central horizontal band.  The remaining Archimedean terms
grow only logarithmically with the height. -/
theorem norm_logDeriv_riemannZeta_central_left_le
    {σ T K : ℝ} (hσhi : σ ≤ 1 / 2) (hT : 2 ≤ |T|)
    (hzs : riemannZeta ((σ : ℂ) + I * T) ≠ 0)
    (hz1s : riemannZeta (1 - ((σ : ℂ) + I * T)) ≠ 0)
    (hright :
      ‖logDeriv riemannZeta (1 - ((σ : ℂ) + I * T))‖ ≤ K) :
    let s : ℂ := (σ : ℂ) + I * T
    ‖logDeriv riemannZeta s‖ ≤
      K + ‖Complex.log Real.pi‖ +
        (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
          Real.log (‖(1 - s) / 2 + 1‖ + 1)) +
        (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
          Real.log (‖1 - s / 2 + 1‖ + 1)) + Real.pi := by
  let s : ℂ := (σ : ℂ) + I * T
  change ‖logDeriv riemannZeta s‖ ≤ _
  have hTne : T ≠ 0 := by
    intro h
    subst T
    norm_num at hT
  have hhalf : 1 ≤ |T| / 2 := by linarith
  have hD1 := norm_digamma_le_log_of_quarter_le_re
    (z := (1 - s) / 2)
    (by simp [s]; linarith)
    (by simpa [s, abs_div] using hhalf)
  have hD2 := norm_digamma_le_log_of_quarter_le_re
    (z := 1 - s / 2)
    (by simp [s]; linarith)
    (by simpa [s, abs_div] using hhalf)
  have hD1div :
      ‖Complex.digamma ((1 - s) / 2) / 2‖ ≤
        ‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
          Real.log (‖(1 - s) / 2 + 1‖ + 1) := by
    calc
      _ ≤ ‖Complex.digamma ((1 - s) / 2)‖ := by
        rw [norm_div]
        norm_num
      _ ≤ _ := hD1
  have hD2div :
      ‖Complex.digamma (1 - s / 2) / 2‖ ≤
        ‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
          Real.log (‖1 - s / 2 + 1‖ + 1) := by
    calc
      _ ≤ ‖Complex.digamma (1 - s / 2)‖ := by
        rw [norm_div]
        norm_num
      _ ≤ _ := hD2
  have harg : 1 ≤ |(Real.pi * s / 2).im| := by
    have hpi : 1 ≤ Real.pi * |T| / 2 := by
      nlinarith [Real.two_le_pi]
    simpa [s, abs_div, abs_mul, abs_of_pos Real.pi_pos] using hpi
  have hcot := norm_cot_le_two_of_one_le_abs_im harg
  have hcotTerm :
      ‖((Real.pi : ℂ) * Complex.cot (Real.pi * s / 2)) / 2‖ ≤ Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
    nlinarith [Real.pi_pos,
      norm_nonneg (Complex.cot (Real.pi * s / 2))]
  have heq := neg_logDeriv_riemannZeta_central_eq_right_shift
    hTne hzs hz1s
  change (-logDeriv riemannZeta s) = _ at heq
  change ‖logDeriv riemannZeta (1 - s)‖ ≤ K at hright
  have htri (a b c d e : ℂ) :
      ‖a - b + c + d - e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
    calc
      _ ≤ ‖a - b + c + d‖ + ‖e‖ := norm_sub_le _ _
      _ ≤ (‖a - b + c‖ + ‖d‖) + ‖e‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((‖a - b‖ + ‖c‖) + ‖d‖) + ‖e‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ (((‖a‖ + ‖b‖) + ‖c‖) + ‖d‖) + ‖e‖ := by
        gcongr
        exact norm_sub_le _ _
  calc
    ‖logDeriv riemannZeta s‖ = ‖-logDeriv riemannZeta s‖ := by simp
    _ = ‖logDeriv riemannZeta (1 - s) - Complex.log Real.pi +
          Complex.digamma ((1 - s) / 2) / 2 +
          Complex.digamma (1 - s / 2) / 2 -
          ((Real.pi : ℂ) * Complex.cot (Real.pi * s / 2)) / 2‖ := by rw [heq]
    _ ≤ ‖logDeriv riemannZeta (1 - s)‖ + ‖Complex.log Real.pi‖ +
          ‖Complex.digamma ((1 - s) / 2) / 2‖ +
          ‖Complex.digamma (1 - s / 2) / 2‖ +
          ‖((Real.pi : ℂ) * Complex.cot (Real.pi * s / 2)) / 2‖ :=
      htri _ _ _ _ _
    _ ≤ K + ‖Complex.log Real.pi‖ +
          (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
            Real.log (‖(1 - s) / 2 + 1‖ + 1)) +
          (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
            Real.log (‖1 - s / 2 + 1‖ + 1)) + Real.pi := by
      gcongr

/-- A single logarithmically separated good height controls the full central
horizontal band on both signs of the height.  The right half comes from the
shifted Jensen disk; the left half follows from the zeta functional equation
and logarithmic bounds for the Archimedean factors. -/
theorem exists_goodHeight_Icc_norm_logDeriv_central_band_le_log_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ t : ℝ, |t| = T →
            ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
              ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
                C * (1 + Real.log (A + 6)) ^ 2 := by
  rcases exists_goodHeight_Icc_norm_logDeriv_central_right_le_log_sq with
    ⟨Cr, hCr, hchoose⟩
  let G : ℝ := ‖Complex.log Real.pi‖ +
    2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4) + Real.pi
  let C : ℝ := Cr + G + 2
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hright⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro t ht_abs σ hσlo hσhi
  let s : ℂ := (σ : ℂ) + I * t
  let L : ℝ := Real.log (A + 6)
  let LA : ℝ := 1 + L
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by linarith)
  have hLA : 1 ≤ LA := by dsimp [LA]; linarith
  by_cases hσright : 1 / 2 ≤ σ
  · have hbase := hright t ht_abs σ hσright hσhi
    apply hbase.trans
    have hCrC : Cr ≤ C := by dsimp [C]; linarith
    simpa [LA, L] using
      mul_le_mul_of_nonneg_right hCrC (sq_nonneg LA)
  · have hσhalf : σ ≤ 1 / 2 := le_of_not_ge hσright
    have hT2 : 2 ≤ |t| := by rw [ht_abs]; linarith [hA, hT.1]
    have hTpos : 0 < T := by linarith [hA, hT.1]
    have hzs : riemannZeta s ≠ 0 := by
      simpa [s] using riemannZeta_ne_zero_on_goodHeight_horizontal
        (T := T) (t := t) (σ := σ) hTpos ht_abs hgood
    have hneg_abs : |-t| = T := by simpa using ht_abs
    have hreflect_point :
        (((1 - σ : ℝ) : ℂ) + I * ((-t : ℝ) : ℂ)) = 1 - s := by
      apply Complex.ext <;> simp [s]
    have hz1s : riemannZeta (1 - s) ≠ 0 := by
      have h := riemannZeta_ne_zero_on_goodHeight_horizontal
        (T := T) (t := -t) (σ := 1 - σ) hTpos hneg_abs hgood
      rw [hreflect_point] at h
      exact h
    have hright_reflect :
        ‖logDeriv riemannZeta (1 - s)‖ ≤ Cr * LA ^ 2 := by
      have h := hright (-t) hneg_abs (1 - σ) (by linarith) (by linarith)
      rw [hreflect_point] at h
      simpa [LA, L] using h
    have hleft := norm_logDeriv_riemannZeta_central_left_le
      (σ := σ) (T := t) (K := Cr * LA ^ 2)
      hσhalf hT2 (by simpa [s] using hzs)
      (by simpa [s] using hz1s) (by simpa [s] using hright_reflect)
    change ‖logDeriv riemannZeta s‖ ≤
      Cr * LA ^ 2 + ‖Complex.log Real.pi‖ +
        (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
          Real.log (‖(1 - s) / 2 + 1‖ + 1)) +
        (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
          Real.log (‖1 - s / 2 + 1‖ + 1)) + Real.pi at hleft
    have hnorm1 : ‖(1 - s) / 2 + 1‖ + 1 ≤ A + 6 := by
      have hnorm := Complex.norm_le_abs_re_add_abs_im ((1 - s) / 2 + 1)
      have hre : |(((1 - s) / 2 + 1).re)| ≤ 2 := by
        have hre_eq : (((1 - s) / 2 + 1).re) = (1 - σ) / 2 + 1 := by
          simp [s]
        have hnonneg : 0 ≤ (1 - σ) / 2 + 1 := by linarith
        rw [hre_eq, abs_of_nonneg hnonneg]
        linarith
      have him : |(((1 - s) / 2 + 1).im)| = |t| / 2 := by
        have him_eq : (((1 - s) / 2 + 1).im) = -t / 2 := by simp [s]
        rw [him_eq, abs_div, abs_neg]
        norm_num
      calc
        ‖(1 - s) / 2 + 1‖ + 1 ≤
            (|(((1 - s) / 2 + 1).re)| +
              |(((1 - s) / 2 + 1).im)|) + 1 := add_le_add hnorm le_rfl
        _ ≤ 2 + |t| / 2 + 1 := by rw [him]; linarith
        _ ≤ A + 6 := by rw [ht_abs]; linarith [hT.2]
    have hnorm2 : ‖1 - s / 2 + 1‖ + 1 ≤ A + 6 := by
      have hnorm := Complex.norm_le_abs_re_add_abs_im (1 - s / 2 + 1)
      have hre : |((1 - s / 2 + 1).re)| ≤ 5 / 2 := by
        have hre_eq : ((1 - s / 2 + 1).re) = 2 - σ / 2 := by
          simp [s]
          ring
        have hnonneg : 0 ≤ 2 - σ / 2 := by linarith
        rw [hre_eq, abs_of_nonneg hnonneg]
        linarith
      have him : |((1 - s / 2 + 1).im)| = |t| / 2 := by
        have him_eq : ((1 - s / 2 + 1).im) = -t / 2 := by
          simp [s]
          ring
        rw [him_eq, abs_div, abs_neg]
        norm_num
      calc
        ‖1 - s / 2 + 1‖ + 1 ≤
            (|((1 - s / 2 + 1).re)| + |((1 - s / 2 + 1).im)|) + 1 :=
          add_le_add hnorm le_rfl
        _ ≤ 5 / 2 + |t| / 2 + 1 := by rw [him]; linarith
        _ ≤ A + 6 := by rw [ht_abs]; linarith [hT.2]
    have harg1pos : 0 < ‖(1 - s) / 2 + 1‖ + 1 := by positivity
    have harg2pos : 0 < ‖1 - s / 2 + 1‖ + 1 := by positivity
    have hlog1 : Real.log (‖(1 - s) / 2 + 1‖ + 1) ≤ L := by
      dsimp [L]
      exact Real.log_le_log harg1pos hnorm1
    have hlog2 : Real.log (‖1 - s / 2 + 1‖ + 1) ≤ L := by
      dsimp [L]
      exact Real.log_le_log harg2pos hnorm2
    apply hleft.trans
    have harch : G + 2 * L ≤ (G + 2) * LA ^ 2 := by
      dsimp [LA]
      nlinarith [sq_nonneg L]
    calc
      Cr * LA ^ 2 + ‖Complex.log Real.pi‖ +
            (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
              Real.log (‖(1 - s) / 2 + 1‖ + 1)) +
            (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
              Real.log (‖1 - s / 2 + 1‖ + 1)) + Real.pi ≤
          Cr * LA ^ 2 + G + 2 * L := by
        dsimp [G]
        linarith
      _ ≤ Cr * LA ^ 2 + (G + 2) * LA ^ 2 :=
        by nlinarith
      _ = C * (1 + Real.log (A + 6)) ^ 2 := by
        dsimp [C, LA, L]
        ring

/-- The full central horizontal first-order contour has the explicit
`O(log^2 A / T)` bound at the selected good height, simultaneously on the top
and bottom edges. -/
theorem exists_goodHeight_Icc_norm_horizontal_central_explicitFormulaContour_le
    {x : ℝ} (hx : 1 ≤ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ t : ℝ, |t| = T →
            IntervalIntegrable
              (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * t))
              volume (-1) 2 ∧
            ‖∫ σ : ℝ in (-1)..2,
                explicitFormulaIntegrand x ((σ : ℂ) + I * t)‖ ≤
              (C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T) * 3 := by
  rcases exists_goodHeight_Icc_norm_logDeriv_central_band_le_log_sq with
    ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hlog⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro t ht_abs
  have hTpos : 0 < T := by linarith [hA, hT.1]
  have htne : t ≠ 0 := by
    intro ht
    subst t
    simp at ht_abs
    linarith
  have hK : 0 ≤ C * (1 + Real.log (A + 6)) ^ 2 :=
    mul_nonneg hC (sq_nonneg _)
  have hpoint : ∀ σ ∈ Set.uIoc (-1 : ℝ) 2,
      ‖explicitFormulaIntegrand x ((σ : ℂ) + I * t)‖ ≤
        C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T := by
    intro σ hσ
    rw [Set.uIoc_of_le (by norm_num)] at hσ
    have hld := hlog t ht_abs σ hσ.1.le hσ.2
    have hbase := norm_explicitFormulaIntegrand_horizontal_le_of_logDeriv_le
      hx hσ.2 (abs_pos.mpr htne) hK hld
    rw [ht_abs] at hbase
    convert hbase using 1 <;> ring
  have hintegrable : IntervalIntegrable
      (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * t))
      volume (-1) 2 := by
    apply ContinuousOn.intervalIntegrable
    intro σ hσ
    rw [Set.uIcc_of_le (by norm_num)] at hσ
    have hzeta := riemannZeta_ne_zero_on_goodHeight_horizontal
      (T := T) (t := t) (σ := σ) hTpos ht_abs hgood
    have hs0 : (σ : ℂ) + I * t ≠ 0 := by
      intro hs
      apply htne
      have him := congrArg Complex.im hs
      simpa using him
    have hs1 : (σ : ℂ) + I * t ≠ 1 := by
      intro hs
      apply htne
      have him := congrArg Complex.im hs
      simpa using him
    have han : ContinuousAt (explicitFormulaIntegrand x) ((σ : ℂ) + I * t) :=
      (analyticAt_explicitFormulaIntegrand_of_ne_zero_of_ne_one_of_zeta_ne_zero
        (zero_lt_one.trans_le hx) hs0 hs1 hzeta).continuousAt
    have hmap : ContinuousAt (fun r : ℝ => ((r : ℂ) + I * t)) σ := by
      fun_prop
    change ContinuousWithinAt
      (explicitFormulaIntegrand x ∘ fun r : ℝ => ((r : ℂ) + I * t)) _ σ
    exact (ContinuousAt.comp
      (f := fun r : ℝ => ((r : ℂ) + I * t))
      (x := σ) (g := explicitFormulaIntegrand x) han hmap).continuousWithinAt
  refine ⟨hintegrable, ?_⟩
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * t))
    (a := (-1 : ℝ)) (b := 2)
    (C := C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T)
    hpoint
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 - (-1))] at hbound
  convert hbound using 1 <;> ring

/-- At one good height in every unit interval, the complete bottom-minus-top
horizontal contribution has the explicit `O_x(log^2 A / A)` bound, uniformly
in every left endpoint `a ≤ -1`.  This combines the central Jensen/Borel bound
with the functional-equation estimate on the entire far-left segment. -/
theorem
    exists_goodHeight_Icc_norm_horizontal_complete_explicitFormulaContour_difference_le
    {x : ℝ} (hx : 1 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧ ∀ {a : ℝ}, a ≤ -1 →
          ‖(∫ σ : ℝ in a..2,
                explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))) -
            (∫ σ : ℝ in a..2,
                explicitFormulaIntegrand x ((σ : ℂ) + I * T))‖ ≤
            C * (1 + Real.log (A + 6)) ^ 2 / T := by
  rcases exists_goodHeight_Icc_norm_horizontal_central_explicitFormulaContour_le
      hx.le with ⟨Cc, hCc, hcentral⟩
  rcases exists_norm_integral_farLeft_explicit_le_log_div
      hx one_pos with ⟨Cf, hCf, hfar⟩
  let C : ℝ := 2 * (Cf + 3 * Cc * x ^ (2 : ℝ))
  have hx0 : 0 ≤ x := (zero_lt_one.trans hx).le
  have hxpow : 0 ≤ x ^ (2 : ℝ) := Real.rpow_nonneg hx0 _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hcentral A hA with ⟨T, hTmem, hgood, hcentralT⟩
  have hTpos : 0 < T := by linarith [hTmem.1]
  have hTabs : |T| = T := abs_of_pos hTpos
  have hTlarge : 1 ≤ |T| := by rw [hTabs]; linarith [hTmem.1]
  let L : ℝ := 1 + Real.log (A + 6)
  have hlogA : 0 ≤ Real.log (A + 6) :=
    Real.log_nonneg (by linarith)
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hlogT : Real.log (1 + T) ≤ Real.log (A + 6) := by
    exact Real.log_le_log (by linarith) (by linarith [hTmem.2])
  have hheight : 1 + Real.log (1 + T) ≤ L ^ 2 := by
    have hlin : 1 + Real.log (1 + T) ≤ L := by dsimp [L]; linarith
    have hsq : L ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
    exact hlin.trans hsq
  refine ⟨T, hTmem, hgood, ?_⟩
  intro a ha
  have hfarTop0 := hfar (a := a) (T := T) ha hTlarge
  have hfarBottom0 := hfar (a := a) (T := -T) ha (by simpa using hTlarge)
  have hfarTop :
      ‖∫ σ : ℝ in a..(-1),
          explicitFormulaIntegrand x ((σ : ℂ) + I * T)‖ ≤
        Cf * L ^ 2 / T := by
    have hbase :
        ‖∫ σ : ℝ in a..(-1),
            explicitFormulaIntegrand x ((σ : ℂ) + I * T)‖ ≤
          Cf * (1 + Real.log (1 + T)) / T := by
      simpa [mul_comm, hTabs] using hfarTop0.2
    apply hbase.trans
    apply div_le_div_of_nonneg_right _ hTpos.le
    exact mul_le_mul_of_nonneg_left hheight hCf
  have hfarBottom :
      ‖∫ σ : ℝ in a..(-1),
          explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))‖ ≤
        Cf * L ^ 2 / T := by
    have hbase :
        ‖∫ σ : ℝ in a..(-1),
            explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))‖ ≤
          Cf * (1 + Real.log (1 + T)) / T := by
      simpa [mul_comm, hTabs] using hfarBottom0.2
    apply hbase.trans
    apply div_le_div_of_nonneg_right _ hTpos.le
    exact mul_le_mul_of_nonneg_left hheight hCf
  have hcentralTop := hcentralT T hTabs
  have hcentralBottom := hcentralT (-T) (by simpa [hTabs])
  have hfarTopInt : IntervalIntegrable
      (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * T))
      volume a (-1) := by
    simpa [mul_comm] using hfarTop0.1
  have hfarBottomInt : IntervalIntegrable
      (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * (-T)))
      volume a (-1) := by
    simpa [mul_comm] using hfarBottom0.1
  have hcentralBottomInt : IntervalIntegrable
      (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * (-T)))
      volume (-1) 2 := by
    simpa using hcentralBottom.1
  have hjoinTop :
      (∫ σ : ℝ in a..2,
          explicitFormulaIntegrand x ((σ : ℂ) + I * T)) =
        (∫ σ : ℝ in a..(-1),
          explicitFormulaIntegrand x ((σ : ℂ) + I * T)) +
        ∫ σ : ℝ in (-1)..2,
          explicitFormulaIntegrand x ((σ : ℂ) + I * T) :=
    (intervalIntegral.integral_add_adjacent_intervals hfarTopInt hcentralTop.1).symm
  have hjoinBottom :
      (∫ σ : ℝ in a..2,
          explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))) =
        (∫ σ : ℝ in a..(-1),
          explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))) +
        ∫ σ : ℝ in (-1)..2,
          explicitFormulaIntegrand x ((σ : ℂ) + I * (-T)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      hfarBottomInt hcentralBottomInt).symm
  let K : ℝ := Cf + 3 * Cc * x ^ (2 : ℝ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have htop :
      ‖∫ σ : ℝ in a..2,
          explicitFormulaIntegrand x ((σ : ℂ) + I * T)‖ ≤
        K * L ^ 2 / T := by
    rw [hjoinTop]
    calc
      _ ≤ ‖∫ σ : ℝ in a..(-1),
              explicitFormulaIntegrand x ((σ : ℂ) + I * T)‖ +
            ‖∫ σ : ℝ in (-1)..2,
              explicitFormulaIntegrand x ((σ : ℂ) + I * T)‖ := norm_add_le _ _
      _ ≤ Cf * L ^ 2 / T + (Cc * x ^ (2 : ℝ) * L ^ 2 / T) * 3 :=
        add_le_add hfarTop (by simpa [L] using hcentralTop.2)
      _ = K * L ^ 2 / T := by dsimp [K]; ring
  have hbottom :
      ‖∫ σ : ℝ in a..2,
          explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))‖ ≤
        K * L ^ 2 / T := by
    rw [hjoinBottom]
    calc
      _ ≤ ‖∫ σ : ℝ in a..(-1),
              explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))‖ +
            ‖∫ σ : ℝ in (-1)..2,
              explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))‖ := norm_add_le _ _
      _ ≤ Cf * L ^ 2 / T + (Cc * x ^ (2 : ℝ) * L ^ 2 / T) * 3 :=
        add_le_add hfarBottom (by simpa [L] using hcentralBottom.2)
      _ = K * L ^ 2 / T := by dsimp [K]; ring
  calc
    _ ≤ ‖∫ σ : ℝ in a..2,
            explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))‖ +
          ‖∫ σ : ℝ in a..2,
            explicitFormulaIntegrand x ((σ : ℂ) + I * T)‖ := norm_sub_le _ _
    _ ≤ K * L ^ 2 / T + K * L ^ 2 / T := add_le_add hbottom htop
    _ = C * L ^ 2 / T := by dsimp [C, K]; ring

/-- Uniform selected-height estimate for the complete bottom-minus-top
horizontal contribution.  For every `x ≥ 2`, the same absolute constant works;
the only remaining dependence on the Perron sample is the displayed `x^2`. -/
theorem
    exists_uniform_goodHeight_Icc_norm_horizontal_complete_explicitFormulaContour_difference_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧ ∀ {x : ℝ}, 2 ≤ x →
          ∀ {a : ℝ}, a ≤ -1 →
          ‖(∫ σ : ℝ in a..2,
                explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))) -
            (∫ σ : ℝ in a..2,
                explicitFormulaIntegrand x ((σ : ℂ) + I * T))‖ ≤
            C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T := by
  rcases exists_goodHeight_Icc_norm_logDeriv_central_band_le_log_sq with
    ⟨Cc, hCc, hcentralChoose⟩
  rcases exists_uniform_norm_integral_farLeft_explicit_le_log_div with
    ⟨Cf, hCf, hfar⟩
  let C : ℝ := 2 * (Cf + 3 * Cc)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hcentralChoose A hA with ⟨T, hTmem, hgood, hlog⟩
  have hTpos : 0 < T := by linarith [hTmem.1]
  have hTabs : |T| = T := abs_of_pos hTpos
  have hTlarge : 1 ≤ |T| := by rw [hTabs]; linarith [hTmem.1]
  let L : ℝ := 1 + Real.log (A + 6)
  have hlogA : 0 ≤ Real.log (A + 6) :=
    Real.log_nonneg (by linarith)
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hlogT : Real.log (1 + T) ≤ Real.log (A + 6) :=
    Real.log_le_log (by linarith) (by linarith [hTmem.2])
  have hheight : 1 + Real.log (1 + T) ≤ L ^ 2 := by
    have hlin : 1 + Real.log (1 + T) ≤ L := by dsimp [L]; linarith
    have hsq : L ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
    exact hlin.trans hsq
  refine ⟨T, hTmem, hgood, ?_⟩
  intro x hx a ha
  have hx1 : 1 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hxpow : 0 ≤ x ^ (2 : ℝ) := Real.rpow_nonneg hxpos.le _
  have honepow : 1 ≤ x ^ (2 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hcentralPoint : ∀ t : ℝ, |t| = T →
      IntervalIntegrable
        (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * t))
        volume (-1) 2 ∧
      ‖∫ σ : ℝ in (-1)..2,
          explicitFormulaIntegrand x ((σ : ℂ) + I * t)‖ ≤
        (Cc * x ^ (2 : ℝ) * L ^ 2 / T) * 3 := by
    intro t ht_abs
    have htne : t ≠ 0 := by
      intro ht
      subst t
      simp at ht_abs
      linarith
    have hK : 0 ≤ Cc * L ^ 2 := mul_nonneg hCc (sq_nonneg _)
    have hpoint : ∀ σ ∈ Set.uIoc (-1 : ℝ) 2,
        ‖explicitFormulaIntegrand x ((σ : ℂ) + I * t)‖ ≤
          Cc * x ^ (2 : ℝ) * L ^ 2 / T := by
      intro σ hσ
      rw [Set.uIoc_of_le (by norm_num)] at hσ
      have hld := hlog t ht_abs σ hσ.1.le hσ.2
      have hbase := norm_explicitFormulaIntegrand_horizontal_le_of_logDeriv_le
        hx1 hσ.2 (abs_pos.mpr htne) hK hld
      rw [ht_abs] at hbase
      convert hbase using 1 <;> dsimp [L] <;> ring
    have hintegrable : IntervalIntegrable
        (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * t))
        volume (-1) 2 := by
      apply ContinuousOn.intervalIntegrable
      intro σ hσ
      rw [Set.uIcc_of_le (by norm_num)] at hσ
      have hzeta := riemannZeta_ne_zero_on_goodHeight_horizontal
        (T := T) (t := t) (σ := σ) hTpos ht_abs hgood
      have hs0 : (σ : ℂ) + I * t ≠ 0 := by
        intro hs
        apply htne
        have him := congrArg Complex.im hs
        simpa using him
      have hs1 : (σ : ℂ) + I * t ≠ 1 := by
        intro hs
        apply htne
        have him := congrArg Complex.im hs
        simpa using him
      have han : ContinuousAt (explicitFormulaIntegrand x) ((σ : ℂ) + I * t) :=
        (analyticAt_explicitFormulaIntegrand_of_ne_zero_of_ne_one_of_zeta_ne_zero
          hxpos hs0 hs1 hzeta).continuousAt
      have hmap : ContinuousAt (fun r : ℝ => ((r : ℂ) + I * t)) σ := by
        fun_prop
      change ContinuousWithinAt
        (explicitFormulaIntegrand x ∘ fun r : ℝ => ((r : ℂ) + I * t)) _ σ
      exact (ContinuousAt.comp
        (f := fun r : ℝ => ((r : ℂ) + I * t))
        (x := σ) (g := explicitFormulaIntegrand x) han hmap).continuousWithinAt
    refine ⟨hintegrable, ?_⟩
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * t))
      (a := (-1 : ℝ)) (b := 2)
      (C := Cc * x ^ (2 : ℝ) * L ^ 2 / T) hpoint
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 - (-1))] at hbound
    convert hbound using 1 <;> ring
  have hfarTop0 := hfar hx ha hTlarge
  have hfarBottom0 := hfar hx ha (by simpa using hTlarge : 1 ≤ |-T|)
  have hfarTop :
      ‖∫ σ : ℝ in a..(-1),
          explicitFormulaIntegrand x ((σ : ℂ) + I * T)‖ ≤
        Cf * x ^ (2 : ℝ) * L ^ 2 / T := by
    have hbase :
        ‖∫ σ : ℝ in a..(-1),
            explicitFormulaIntegrand x ((σ : ℂ) + I * T)‖ ≤
          Cf * (1 + Real.log (1 + T)) / T := by
      simpa [mul_comm, hTabs] using hfarTop0.2
    apply hbase.trans
    apply div_le_div_of_nonneg_right _ hTpos.le
    have hcoeff : Cf ≤ Cf * x ^ (2 : ℝ) := by
      nlinarith [mul_nonneg hCf (sub_nonneg.mpr honepow)]
    calc
      Cf * (1 + Real.log (1 + T)) ≤ Cf * L ^ 2 :=
        mul_le_mul_of_nonneg_left hheight hCf
      _ ≤ Cf * x ^ (2 : ℝ) * L ^ 2 := by
        nlinarith [sq_nonneg L, mul_nonneg (sub_nonneg.mpr hcoeff) (sq_nonneg L)]
  have hfarBottom :
      ‖∫ σ : ℝ in a..(-1),
          explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))‖ ≤
        Cf * x ^ (2 : ℝ) * L ^ 2 / T := by
    have hbase :
        ‖∫ σ : ℝ in a..(-1),
            explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))‖ ≤
          Cf * (1 + Real.log (1 + T)) / T := by
      simpa [mul_comm, hTabs] using hfarBottom0.2
    apply hbase.trans
    apply div_le_div_of_nonneg_right _ hTpos.le
    have hcoeff : Cf ≤ Cf * x ^ (2 : ℝ) := by
      nlinarith [mul_nonneg hCf (sub_nonneg.mpr honepow)]
    calc
      Cf * (1 + Real.log (1 + T)) ≤ Cf * L ^ 2 :=
        mul_le_mul_of_nonneg_left hheight hCf
      _ ≤ Cf * x ^ (2 : ℝ) * L ^ 2 := by
        nlinarith [sq_nonneg L, mul_nonneg (sub_nonneg.mpr hcoeff) (sq_nonneg L)]
  have hcentralTop := hcentralPoint T hTabs
  have hcentralBottom := hcentralPoint (-T) (by simpa [hTabs])
  have hfarTopInt : IntervalIntegrable
      (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * T))
      volume a (-1) := by simpa [mul_comm] using hfarTop0.1
  have hfarBottomInt : IntervalIntegrable
      (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * (-T)))
      volume a (-1) := by simpa [mul_comm] using hfarBottom0.1
  have hcentralBottomInt : IntervalIntegrable
      (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * (-T)))
      volume (-1) 2 := by simpa using hcentralBottom.1
  have hcentralBottomBound :
      ‖∫ σ : ℝ in (-1)..2,
          explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))‖ ≤
        (Cc * x ^ (2 : ℝ) * L ^ 2 / T) * 3 := by
    simpa using hcentralBottom.2
  have hjoinTop :
      (∫ σ : ℝ in a..2,
          explicitFormulaIntegrand x ((σ : ℂ) + I * T)) =
        (∫ σ : ℝ in a..(-1),
          explicitFormulaIntegrand x ((σ : ℂ) + I * T)) +
        ∫ σ : ℝ in (-1)..2,
          explicitFormulaIntegrand x ((σ : ℂ) + I * T) :=
    (intervalIntegral.integral_add_adjacent_intervals hfarTopInt hcentralTop.1).symm
  have hjoinBottom :
      (∫ σ : ℝ in a..2,
          explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))) =
        (∫ σ : ℝ in a..(-1),
          explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))) +
        ∫ σ : ℝ in (-1)..2,
          explicitFormulaIntegrand x ((σ : ℂ) + I * (-T)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      hfarBottomInt hcentralBottomInt).symm
  let K : ℝ := (Cf + 3 * Cc) * x ^ (2 : ℝ)
  have htop :
      ‖∫ σ : ℝ in a..2,
          explicitFormulaIntegrand x ((σ : ℂ) + I * T)‖ ≤ K * L ^ 2 / T := by
    rw [hjoinTop]
    calc
      _ ≤ ‖∫ σ : ℝ in a..(-1),
              explicitFormulaIntegrand x ((σ : ℂ) + I * T)‖ +
            ‖∫ σ : ℝ in (-1)..2,
              explicitFormulaIntegrand x ((σ : ℂ) + I * T)‖ := norm_add_le _ _
      _ ≤ Cf * x ^ (2 : ℝ) * L ^ 2 / T +
          (Cc * x ^ (2 : ℝ) * L ^ 2 / T) * 3 :=
        add_le_add hfarTop hcentralTop.2
      _ = K * L ^ 2 / T := by dsimp [K]; ring
  have hbottom :
      ‖∫ σ : ℝ in a..2,
          explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))‖ ≤ K * L ^ 2 / T := by
    rw [hjoinBottom]
    calc
      _ ≤ ‖∫ σ : ℝ in a..(-1),
              explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))‖ +
            ‖∫ σ : ℝ in (-1)..2,
              explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))‖ := norm_add_le _ _
      _ ≤ Cf * x ^ (2 : ℝ) * L ^ 2 / T +
          (Cc * x ^ (2 : ℝ) * L ^ 2 / T) * 3 :=
        add_le_add hfarBottom hcentralBottomBound
      _ = K * L ^ 2 / T := by dsimp [K]; ring
  calc
    _ ≤ ‖∫ σ : ℝ in a..2,
            explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))‖ +
          ‖∫ σ : ℝ in a..2,
            explicitFormulaIntegrand x ((σ : ℂ) + I * T)‖ := norm_sub_le _ _
    _ ≤ K * L ^ 2 / T + K * L ^ 2 / T := add_le_add hbottom htop
    _ = C * x ^ (2 : ℝ) * L ^ 2 / T := by dsimp [C, K]; ring

/-- There is a cofinal sequence of good heights along which both complete
central horizontal contour integrals tend to zero. -/
theorem exists_tendsto_horizontal_central_explicitFormulaIntegrand_both_zero
    {x : ℝ} (hx : 1 ≤ x) :
    ∃ T : ℕ → ℝ,
      (∀ n : ℕ,
        T n ∈ Set.Icc ((n : ℝ) + 4) ((n : ℝ) + 5) ∧
          ExplicitFormulaAux.goodHeight (T n) ∧
          IntervalIntegrable
            (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * T n))
            volume (-1) 2 ∧
          IntervalIntegrable
            (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * (-(T n))))
            volume (-1) 2) ∧
      Tendsto T atTop atTop ∧
      Tendsto
        (fun n : ℕ => ∫ σ : ℝ in (-1)..2,
          explicitFormulaIntegrand x ((σ : ℂ) + I * T n))
        atTop (𝓝 0) ∧
      Tendsto
        (fun n : ℕ => ∫ σ : ℝ in (-1)..2,
          explicitFormulaIntegrand x ((σ : ℂ) + I * (-(T n))))
        atTop (𝓝 0) := by
  classical
  rcases exists_goodHeight_Icc_norm_horizontal_central_explicitFormulaContour_le hx with
    ⟨C, hC, hchoose⟩
  have hA (n : ℕ) : 4 ≤ (n : ℝ) + 4 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  let T : ℕ → ℝ := fun n => Classical.choose (hchoose ((n : ℝ) + 4) (hA n))
  have hspec (n : ℕ) :
      T n ∈ Set.Icc ((n : ℝ) + 4) ((n : ℝ) + 5) ∧
        ExplicitFormulaAux.goodHeight (T n) ∧
          ∀ t : ℝ, |t| = T n →
            IntervalIntegrable
              (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * t))
              volume (-1) 2 ∧
            ‖∫ σ : ℝ in (-1)..2,
                explicitFormulaIntegrand x ((σ : ℂ) + I * t)‖ ≤
              (C * x ^ (2 : ℝ) *
                (1 + Real.log (((n : ℝ) + 4) + 6)) ^ 2 / T n) * 3 := by
    dsimp [T]
    convert Classical.choose_spec (hchoose ((n : ℝ) + 4) (hA n)) using 1 <;> ring
  have hTtop : Tendsto T atTop atTop := by
    have hbase : Tendsto (fun n : ℕ => (n : ℝ) + 4) atTop atTop :=
      tendsto_atTop_add_const_right atTop 4 tendsto_natCast_atTop_atTop
    exact tendsto_atTop_mono' atTop
      (Eventually.of_forall fun n => (hspec n).1.1) hbase
  have hpow (k : ℕ) : Tendsto
      (fun n : ℕ =>
        Real.log ((n : ℝ) + 10) ^ k / ((n : ℝ) + 4))
      atTop (𝓝 0) := by
    have hshift : Tendsto (fun y : ℝ => y + 10) atTop atTop :=
      tendsto_atTop_add_const_right atTop 10 tendsto_id
    have hreal :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-6) k one_ne_zero).comp hshift
    have hnat := hreal.comp tendsto_natCast_atTop_atTop
    refine hnat.congr' (Eventually.of_forall fun n => ?_)
    dsimp [Function.comp_def]
    congr 1
    ring
  have hratio : Tendsto
      (fun n : ℕ =>
        (1 + Real.log ((n : ℝ) + 10)) ^ 2 / ((n : ℝ) + 4))
      atTop (𝓝 0) := by
    have hsum := ((hpow 2).add ((hpow 1).const_mul 2)).add (hpow 0)
    convert hsum using 1
    · funext n
      simp only [pow_one, pow_zero]
      ring
    · norm_num
  have hmajor : Tendsto
      (fun n : ℕ =>
        (C * x ^ (2 : ℝ) *
          (1 + Real.log ((n : ℝ) + 10)) ^ 2 / ((n : ℝ) + 4)) * 3)
      atTop (𝓝 0) := by
    have h := hratio.const_mul (3 * C * x ^ (2 : ℝ))
    convert h using 1
    · funext n
      ring
    · norm_num
  have hsigned (ε : ℝ) (hε : |ε| = 1) : Tendsto
      (fun n : ℕ => ∫ σ : ℝ in (-1)..2,
        explicitFormulaIntegrand x ((σ : ℂ) + I * (ε * T n)))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero'
      (Eventually.of_forall fun n => norm_nonneg _)
      (Eventually.of_forall fun n => ?_) hmajor
    have hTpos : 0 < T n := by linarith [(hspec n).1.1]
    have ht_abs : |ε * T n| = T n := by
      rw [abs_mul, hε, one_mul, abs_of_pos hTpos]
    have hcontour := ((hspec n).2.2 (ε * T n) ht_abs).2
    rw [show (n : ℝ) + 4 + 6 = (n : ℝ) + 10 by ring] at hcontour
    have hnum : 0 ≤ C * x ^ (2 : ℝ) *
        (1 + Real.log ((n : ℝ) + 10)) ^ 2 := by positivity
    have hden : (n : ℝ) + 4 ≤ T n := (hspec n).1.1
    have hdiv :
        (C * x ^ (2 : ℝ) *
          (1 + Real.log ((n : ℝ) + 10)) ^ 2) / T n ≤
        (C * x ^ (2 : ℝ) *
          (1 + Real.log ((n : ℝ) + 10)) ^ 2) / ((n : ℝ) + 4) :=
      div_le_div_of_nonneg_left hnum (by positivity) hden
    have hfinal := hcontour.trans
      (mul_le_mul_of_nonneg_right hdiv (by norm_num : (0 : ℝ) ≤ 3))
    have hmul : ((ε * T n : ℝ) : ℂ) = (ε : ℂ) * (T n : ℂ) := by
      norm_cast
    rw [hmul] at hfinal
    exact hfinal
  refine ⟨T, ?_, hTtop, ?_, ?_⟩
  · intro n
    have hTpos : 0 < T n := by linarith [(hspec n).1.1]
    have htop_abs : |T n| = T n := abs_of_pos hTpos
    have hbottom_abs : |-(T n)| = T n := by simp [abs_of_pos hTpos]
    have hbottom_integrable : IntervalIntegrable
        (fun σ : ℝ => explicitFormulaIntegrand x
          ((σ : ℂ) + I * (-(T n)))) volume (-1) 2 := by
      simpa only [ofReal_neg] using
        ((hspec n).2.2 (-(T n)) hbottom_abs).1
    exact ⟨(hspec n).1, (hspec n).2.1,
      ((hspec n).2.2 (T n) htop_abs).1,
      hbottom_integrable⟩
  · simpa using hsigned 1 (by norm_num)
  · simpa using hsigned (-1) (by norm_num)

end ExplicitFormulaResidues
end PrimeNumberTheorem
