import PrimeNumberTheorem.MWKFCubicAFEDiagonalMellinKernel
import PrimeNumberTheorem.MWKFCubicAFEDyadicTimeIntegral

open Complex Filter MeasureTheory
open scoped Interval

namespace PrimeNumberTheorem.MWKFCubic

/-!
# The actual diagonal as a finite-height Mellin integral

Both the diagonal-scale/vertical-integral interchange and the physical-time
interchange are proved by actual summable envelopes. No contour shift or
zero-mode identity is assumed.
-/

noncomputable def cubicAFEDiagonalOuterWeight
    (W : CubicTestWeight) (T : ℝ) (d e : ℕ) (t : ℝ) : ℂ :=
  (cubicMollifierCoefficient T d : ℂ) * (cubicMollifierCoefficient T e : ℂ) * 2 * (W (t / T) : ℂ)

noncomputable def cubicAFEDiagonalMellinKernel (d e : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  cubicAFEScalar t z * ((1 / (Nat.lcm d e : ℂ)) *
    (1 / (((d / Nat.gcd d e) * (e / Nat.gcd d e) : ℕ) : ℂ)^z) * riemannZeta (1 + 2 * z))

private theorem diagonal_product_pos {d e : ℕ} (hd : 0 < d) (he : 0 < e) (k : ℕ) :
    0 < (k + 1)^2 * (d / Nat.gcd d e) * (e / Nat.gcd d e) := by
  rw [← cubicAFEPositiveIndexProduct_diagonalRay hd he k]
  unfold cubicAFEPositiveIndexProduct
  positivity

private theorem continuous_diagonalMonomial_vertical
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) (k : ℕ) (X : ℝ) :
    Continuous (fun v : ℝ ↦ cubicAFEDiagonalMellinMonomial d e k (cubicAFEVerticalPoint X v)) := by
  let K := (k + 1)^2 * (d / Nat.gcd d e) * (e / Nat.gcd d e)
  have hK : (K : ℂ) ≠ 0 := by exact_mod_cast (diagonal_product_pos hd he k).ne'
  let : NeZero (K : ℂ) := ⟨hK⟩
  have hz : Continuous (cubicAFEVerticalPoint X) := by unfold cubicAFEVerticalPoint; fun_prop
  have hp := (continuous_const_cpow (K : ℂ)).comp hz
  exact continuous_const.mul (continuous_const.div₀ hp (fun _ ↦ cpow_ne_zero_iff.mpr (Or.inl hK)))

private theorem norm_diagonalMonomial_vertical
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) (k : ℕ) (X v : ℝ) :
    ‖cubicAFEDiagonalMellinMonomial d e k (cubicAFEVerticalPoint X v)‖ =
      ‖cubicAFEDiagonalMellinMonomial d e k (X : ℂ)‖ := by
  unfold cubicAFEDiagonalMellinMonomial
  simp only [norm_mul, norm_div, norm_one]
  have hK := diagonal_product_pos hd he k
  have hcast (n : ℕ) : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
  rw [hcast ((k + 1)^2 * (d / Nat.gcd d e) * (e / Nat.gcd d e)),
    norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hK),
    norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hK)]
  simp [cubicAFEVerticalPoint]

theorem cubicAFECombinedSummandFinite_diagonalRay_eq_mellin
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (t : ℝ) (k : ℕ) :
    cubicAFECombinedSummandFinite W T X V d e t (cubicAFEDiagonalRay d e k) =
      cubicAFEDiagonalOuterWeight W T d e t * (1 / (2 * Real.pi) : ℂ) *
        ∫ v : ℝ in -V..V, cubicAFEScalar t (cubicAFEVerticalPoint X v) *
          cubicAFEDiagonalMellinMonomial d e k (cubicAFEVerticalPoint X v) := by
  rw [cubicAFECombinedSummandFinite_diagonalRay W T X V hd he t k]
  unfold cubicAFEProductWeightFinite cubicAFEDiagonalMellinMonomial cubicAFEDiagonalOuterWeight
  have heq : (fun v : ℝ ↦ cubicAFEScalar t (cubicAFEVerticalPoint X v) *
      (((Real.sqrt (((k + 1)^2 * (d / Nat.gcd d e) * (e / Nat.gcd d e) : ℕ) : ℝ) : ℂ)⁻¹ *
        (Real.sqrt ((d : ℝ) * e) : ℂ)⁻¹) *
        (1 / (((k + 1)^2 * (d / Nat.gcd d e) * (e / Nat.gcd d e) : ℕ) : ℂ) ^ cubicAFEVerticalPoint X v))) =
      fun v : ℝ ↦
        (((Real.sqrt (((k + 1)^2 * (d / Nat.gcd d e) * (e / Nat.gcd d e) : ℕ) : ℝ) : ℂ)⁻¹ *
          (Real.sqrt ((d : ℝ) * e) : ℂ)⁻¹) *
            (cubicAFEScalar t (cubicAFEVerticalPoint X v) *
              (1 / (((k + 1)^2 * (d / Nat.gcd d e) * (e / Nat.gcd d e) : ℕ) : ℂ) ^ cubicAFEVerticalPoint X v))) := by
    funext v
    ring
  rw [heq, intervalIntegral.integral_const_mul]
  ring

theorem hasSum_intervalIntegral_cubicAFEDiagonalMellin
    (t : ℝ) {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    HasSum (fun k : ℕ ↦ ∫ v : ℝ in -V..V,
      cubicAFEScalar t (cubicAFEVerticalPoint X v) *
        cubicAFEDiagonalMellinMonomial d e k (cubicAFEVerticalPoint X v))
      (∫ v : ℝ in -V..V, cubicAFEDiagonalMellinKernel d e t (cubicAFEVerticalPoint X v)) := by
  let a (k : ℕ) := ‖cubicAFEDiagonalMellinMonomial d e k (X : ℂ)‖
  have ha : Summable a := summable_norm_iff.mpr
    (hasSum_cubicAFEDiagonalMellinMonomial hd he (by simpa using (show 0 < X by linarith))).summable
  have hS := continuous_cubicAFEScalar_vertical t X hX
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (bound := fun k v ↦ ‖cubicAFEScalar t (cubicAFEVerticalPoint X v)‖ * a k)
  · intro k
    exact (hS.mul (continuous_diagonalMonomial_vertical hd he k X)).aestronglyMeasurable
  · intro k
    filter_upwards with v
    intro _
    rw [norm_mul, norm_diagonalMonomial_vertical hd he]
  · filter_upwards with v
    intro _
    exact ha.mul_left _
  · have hc : Continuous (fun v : ℝ ↦ ‖cubicAFEScalar t (cubicAFEVerticalPoint X v)‖ * ∑' k, a k) :=
      hS.norm.mul continuous_const
    simpa only [tsum_mul_left] using hc.intervalIntegrable (-V) V
  · filter_upwards with v
    intro _
    have hz : 0 < (cubicAFEVerticalPoint X v).re := by simp [cubicAFEVerticalPoint]; linarith
    exact (hasSum_cubicAFEDiagonalMellinMonomial hd he hz).mul_left
      (cubicAFEScalar t (cubicAFEVerticalPoint X v))

private theorem hasSum_integral_diagonalRay
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    HasSum (fun k : ℕ ↦ ∫ t : ℝ,
      cubicAFECombinedSummandFinite W T X V d e t (cubicAFEDiagonalRay d e k))
      (∫ t : ℝ, ∑' k : ℕ, cubicAFECombinedSummandFinite W T X V d e t (cubicAFEDiagonalRay d e k)) := by
  let a (k : ℕ) := ‖cubicAFEDirichletTerm 0 (X : ℂ) (cubicAFEDiagonalRay d e k)‖
  let C (t : ℝ) := cubicAFEWeightEnvelope X V t * ‖cubicAFEPairOuterWeight W T d e t‖
  have ha : Summable a := (summable_norm_cubicAFEDirichletTerm 0 hX).comp_injective
    (cubicAFEDiagonalRay_injective hd he)
  have hC : Continuous C := (continuous_cubicAFEWeightEnvelope hX V).mul
    (continuous_cubicAFEPairOuterWeight W T hd.ne' he.ne').norm
  have hCi : Integrable C := hC.integrable_of_hasCompactSupport
    (hasCompactSupport_cubicAFEPairOuterWeight W hT d e).norm.mul_left
  apply hasSum_integral_of_dominated_convergence (bound := fun k t ↦ C t * a k)
  · intro k
    exact (integrable_cubicAFECombinedSummandFinite W hT hX V hd.ne' he.ne' _).aestronglyMeasurable
  · intro k
    filter_upwards with t
    rw [cubicAFECombinedSummandFinite_eq_outerWeight, norm_mul]
    calc
      _ ≤ (cubicAFEWeightEnvelope X V t * a k) * ‖cubicAFEPairOuterWeight W T d e t‖ :=
        mul_le_mul_of_nonneg_right (norm_cubicAFEWeightFinite_le_envelope t X V _) (norm_nonneg _)
      _ = _ := by dsimp [C]; ring
  · filter_upwards with t
    exact ha.mul_left _
  · simpa only [tsum_mul_left] using hCi.mul_const (∑' k, a k)
  · filter_upwards with t
    exact ((summable_cubicAFECombinedSummandFinite W T hX V d e t).comp_injective
      (cubicAFEDiagonalRay_injective hd he)).hasSum

theorem cubicAFEDiagonalMomentFinite_eq_mellin
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    cubicAFEDiagonalMomentFinite W T X V =
      ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
        ∫ t : ℝ, cubicAFEDiagonalOuterWeight W T d e t * (1 / (2 * Real.pi) : ℂ) *
          ∫ v : ℝ in -V..V, cubicAFEDiagonalMellinKernel d e t (cubicAFEVerticalPoint X v) := by
  rw [cubicAFEDiagonalMomentFinite_eq_ray]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hdpos := (Finset.mem_Icc.mp hd).1
  have hepos := (Finset.mem_Icc.mp he).1
  rw [(hasSum_integral_diagonalRay W hT hX V hdpos hepos).tsum_eq]
  apply integral_congr_ae
  filter_upwards with t
  simp_rw [cubicAFECombinedSummandFinite_diagonalRay_eq_mellin W T X V hdpos hepos t]
  rw [tsum_mul_left, (hasSum_intervalIntegral_cubicAFEDiagonalMellin t hX V hdpos hepos).tsum_eq]

end PrimeNumberTheorem.MWKFCubic
