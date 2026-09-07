import PrimeNumberTheorem.MWKFCubicAFEQuadraticEndpoint
import PrimeNumberTheorem.MWKFCubicAFEDyadicCompletion

open Complex Filter MeasureTheory Set
open scoped Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Fixed-time, nonzero-shift physical endpoint completion

The kernel retains the original Mobius coefficients, factor two, square-root
normalizations, full logarithmic phase and test weight. Only its Mellin
weight is taken to the proved infinite-height limit. For each nonzero shift
it is integrable on the entire two-positive-index domain. Actual lower-scale
completion then tends to its uncut integral on that domain. No physical-time
integral, shift sum or separate finite-height mode limit is interchanged.
-/

noncomputable def cubicAFEProgressionPhysicalSummandVertical
    (W : CubicTestWeight) (T X : ℝ) (d e : ℕ) (δ : ℤ) (t x : ℝ) : ℂ :=
  (cubicMollifierCoefficient T d : ℂ) * (cubicMollifierCoefficient T e : ℂ) * 2 *
    (((Real.sqrt (cubicAFEProgressionRealProduct d e δ x) : ℂ)⁻¹ *
      (Real.sqrt (d * e) : ℂ)⁻¹) *
      Complex.exp ((Complex.I * (Real.log (1 + (δ : ℝ) /
        (x * ((d / Nat.gcd d e : ℕ) : ℝ))) : ℂ)) * t) *
      cubicAFERealProductWeightVertical t X (cubicAFEProgressionRealProduct d e δ x)) *
    (W (t / T) : ℂ)

theorem tendsto_cubicAFEProgressionPhysicalSummand_height
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (he : 0 < e) (δ : ℤ) (t : ℝ) {x : ℝ}
    (hx : x ∈ cubicAFEProgressionDomain d e δ) :
    Tendsto (fun V : ℝ ↦ cubicAFEProgressionPhysicalSummand W T X V d e δ t x)
      atTop (nhds (cubicAFEProgressionPhysicalSummandVertical W T X d e δ t x)) := by
  have h := tendsto_cubicAFERealProductWeightFinite t (X := X) (by linarith) (by linarith)
    (cubicAFEProgressionRealProduct_pos he hx)
  exact ((h.const_mul _).const_mul _).mul_const _

private theorem reduced_positive {d e : ℕ} (hd : 0 < d) : 0 < d / Nat.gcd d e := by
  have h := (gcd_extraction (Nat.gcd_pos_of_pos_left e hd).ne').1
  apply Nat.pos_of_ne_zero
  intro hz
  rw [hz, mul_zero] at h
  exact hd.ne' h

theorem integrableOn_cubicAFEProgressionPhysicalSummandVertical
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) {δ : ℤ} (hδ : δ ≠ 0) (t : ℝ) :
    IntegrableOn (cubicAFEProgressionPhysicalSummandVertical W T X d e δ t)
      (cubicAFEProgressionDomain d e δ) := by
  let r : ℝ := ((d / Nat.gcd d e : ℕ) : ℝ)
  let s : ℝ := ((e / Nat.gcd d e : ℕ) : ℝ)
  let P := cubicAFEProgressionRealProduct d e δ
  let D := cubicAFEProgressionDomain d e δ
  let F : ℝ → ℂ := fun u ↦ ((u ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
    cubicAFERealProductWeightVertical t X u
  let E : ℝ → ℂ := fun x ↦ Complex.exp ((I * (Real.log (1 + (δ : ℝ) / (x * r)) : ℂ)) * t)
  let C : ℂ := (cubicMollifierCoefficient T d : ℂ) * (cubicMollifierCoefficient T e : ℂ) * 2 *
    (Real.sqrt (d * e) : ℂ)⁻¹ * (W (t / T) : ℂ)
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast (reduced_positive (e := e) hd)
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast (show 0 < e / Nat.gcd d e by
      simpa only [Nat.gcd_comm] using (reduced_positive (e := d) he))
  have hδr : (δ : ℝ) ≠ 0 := by exact_mod_cast hδ
  have hquad := integrableOn_cubicAFERealProductWeightVertical_quadratic t hX hr hs hδr
  have hproduct (x : ℝ) : x * ((δ : ℝ) + r * x) / s = P x := by
    dsimp [P, r, s, cubicAFEProgressionRealProduct, cubicAFEProgressionRealSecond]
    ring
  have hdomain : {x : ℝ | 0 < x ∧ 0 < (δ : ℝ) + r * x} = D := by
    ext x
    simp only [D, cubicAFEProgressionDomain, r, mul_comm]
  have hiF : IntegrableOn (fun x ↦ F (P x)) D := by
    simpa only [hproduct, hdomain] using hquad
  have hmE : Measurable E := by dsimp [E]; fun_prop
  have hnE (x : ℝ) : ‖E x‖ ≤ (1 : ℝ) := by
    dsimp [E]
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hi : IntegrableOn (fun x ↦ C * (E x * F (P x))) D :=
    (hiF.bdd_mul hmE.stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall hnE)).const_mul C
  apply hi.congr_fun ?_ (isOpen_cubicAFEProgressionDomain d e δ).measurableSet
  intro x hx
  have hP : 0 < P x := cubicAFEProgressionRealProduct_pos he hx
  have hroot : ((P x ^ (-1 / 2 : ℝ) : ℝ) : ℂ) = (Real.sqrt (P x) : ℂ)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hP.le,
      ← Real.sqrt_eq_rpow, Complex.ofReal_inv]
  dsimp only [C, E, F]
  rw [hroot]
  unfold cubicAFEProgressionPhysicalSummandVertical
  dsimp only [P, r]
  ring

/-- Completion tends to the actual uncut spatial integral, for fixed time
and a fixed nonzero shift. The integral is over the physical domain. -/
theorem tendsto_cubicAFECompletedPhysicalIntegral
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) {δ : ℤ} (hδ : δ ≠ 0) (t : ℝ) :
    Tendsto (fun J : ℕ ↦ ∫ x in cubicAFEProgressionDomain d e δ,
      (cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) : ℂ) *
        cubicAFEProgressionPhysicalSummandVertical W T X d e δ t x)
      atTop (nhds (∫ x in cubicAFEProgressionDomain d e δ,
        cubicAFEProgressionPhysicalSummandVertical W T X d e δ t x)) := by
  let K := cubicAFEProgressionPhysicalSummandVertical W T X d e δ t
  let B : ℕ → ℝ → ℂ := fun J x ↦
    (cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) : ℂ)
  have hiK := integrableOn_cubicAFEProgressionPhysicalSummandVertical W T hX hd he hδ t
  have hs : (0 : ℝ) < ((e / Nat.gcd d e : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < e / Nat.gcd d e by
      simpa only [Nat.gcd_comm] using (reduced_positive (e := d) he))
  have hB (J : ℕ) : Continuous (B J) := by
    have hc := contDiff_cubicAFEDyadicLowerWeight.continuous
    dsimp [B, cubicAFEDyadicCompletionWeight, cubicAFEProgressionRealSecond]
    fun_prop
  have hBnorm (J : ℕ) (x : ℝ) : ‖B J x‖ ≤ (1 : ℝ) := by
    have hn : 0 ≤ cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) :=
      mul_nonneg (cubicAFEDyadicLowerWeight_nonneg _) (cubicAFEDyadicLowerWeight_nonneg _)
    have hl : cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) ≤ 1 := by
      simpa only [cubicAFEDyadicCompletionWeight, mul_one] using mul_le_mul (cubicAFEDyadicLowerWeight_le_one _)
        (cubicAFEDyadicLowerWeight_le_one _) (cubicAFEDyadicLowerWeight_nonneg _) zero_le_one
    simpa only [B, Complex.norm_real, Real.norm_of_nonneg hn] using hl
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖K x‖)
    (fun J ↦ (hB J).aestronglyMeasurable.mul hiK.aestronglyMeasurable) hiK.norm
  · intro J
    filter_upwards [] with x
    change ‖B J x * K x‖ ≤ ‖K x‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hBnorm J x)
  · filter_upwards [ae_restrict_mem (isOpen_cubicAFEProgressionDomain d e δ).measurableSet] with x hx
    have hy : 0 < cubicAFEProgressionRealSecond d e δ x := div_pos hx.2 hs
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_cubicAFEDyadicCompletionWeight_eq_one hx.1 hy] with J hJ
    simp [B, hJ]

end PrimeNumberTheorem.MWKFCubic
