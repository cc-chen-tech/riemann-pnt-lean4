import PrimeNumberTheorem.VKEdgePiOverTwoFarZeroFilter

open Complex Filter Polynomial Set Topology
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- A fixed linear height coefficient dominating the selected zeta rectangle
and every displacement from its center. -/
def localizedFarZeroLinearCoefficient (v : ℝ) : ℝ :=
  20 + 2 * |v|

theorem localizedFarZeroLinearCoefficient_pos (v : ℝ) :
    0 < localizedFarZeroLinearCoefficient v := by
  unfold localizedFarZeroLinearCoefficient
  nlinarith [abs_nonneg v]

/--
Outside vertical distance five, the Gaussian attached to a nontrivial zeta
zero has the uniform exponential saving `exp (-8m)`.
-/
theorem norm_localizedGaussianWeight_far_le
    (A : ℂ[X]) {u v m : ℝ} {rho : ℂ}
    (hu : 0 < u) (hu1 : u < 1) (hm : 0 ≤ m)
    (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (hfar : 5 ≤ |rho.im - v|) :
    ‖localizedGaussianWeight A ((u : ℂ) + I * v) m rho‖ ≤
      ‖A.eval (rho - ((u : ℂ) + I * v))‖ *
        Real.exp (-8 * m) := by
  rw [norm_localizedGaussianWeight]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hreLower : -1 ≤ rho.re - u := by
    linarith [hrho.2.1]
  have hreUpper : rho.re - u ≤ 1 := by
    linarith [hrho.2.2]
  have hreSq :
      (rho.re - u) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hreLower)
      (sub_nonneg.mpr hreUpper)]
  have himSq :
      25 ≤ (rho.im - v) ^ 2 := by
    have habsSq : (5 : ℝ) ^ 2 ≤ |rho.im - v| ^ 2 := by
      exact pow_le_pow_left₀ (by norm_num) hfar 2
    norm_num [sq_abs] at habsSq ⊢
    exact habsSq
  norm_num [Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  nlinarith

theorem ConcreteLocalizedContourSlice.mem_nontrivialZerosFinset_linearHeight
    {A : ℂ[X]} {u v m : ℝ}
    (slice : ConcreteLocalizedContourSlice A u v m)
    {rho : ℂ} (hrho : rho ∈ slice.zeros) :
    rho ∈ nontrivialZerosFinset (12 * m + |v| + 1) := by
  have hzero := slice.isNontrivialZero_of_mem hrho
  have himLower := (slice.zeros_spec rho hrho).2.2.2.1
  have himUpper := (slice.zeros_spec rho hrho).2.2.2.2
  apply mem_nontrivialZerosFinset.mpr
  refine ⟨hzero, ?_⟩
  have hT := slice.height_mem.2
  rw [abs_le]
  constructor <;> linarith

theorem norm_sub_center_le_linearHeight
    {u v m : ℝ} {rho : ℂ}
    (hu : 0 < u) (hu1 : u < 1) (hm : 1 ≤ m)
    (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (him : |rho.im| ≤ 12 * m + |v| + 1) :
    ‖rho - ((u : ℂ) + I * v)‖ ≤
      localizedFarZeroLinearCoefficient v * m := by
  let z : ℂ := rho - ((u : ℂ) + I * v)
  have hre : |z.re| ≤ 1 := by
    dsimp [z]
    norm_num [Complex.sub_re, Complex.add_re, Complex.mul_re]
    rw [abs_le]
    constructor <;> linarith [hrho.2.1, hrho.2.2]
  have himz : |z.im| ≤ 12 * m + 2 * |v| + 1 := by
    dsimp [z]
    norm_num [Complex.sub_im, Complex.add_im, Complex.mul_im]
    calc
      |rho.im - v| ≤ |rho.im| + |v| := abs_sub _ _
      _ ≤ 12 * m + 2 * |v| + 1 := by linarith
  calc
    ‖rho - ((u : ℂ) + I * v)‖ =
        ‖z‖ := rfl
    _ ≤ |z.re| + |z.im| :=
      Complex.norm_le_abs_re_add_abs_im z
    _ ≤ 12 * m + 2 * |v| + 2 := by linarith
    _ ≤ localizedFarZeroLinearCoefficient v * m := by
      unfold localizedFarZeroLinearCoefficient
      nlinarith [mul_nonneg (abs_nonneg v) (sub_nonneg.mpr hm)]

/--
The selected far-zero sum is bounded by the global multiplicity count times
one common polynomial-Gaussian envelope.
-/
theorem norm_localizedFarZeroResidueSum_le_globalMultiplicity
    (A : ℂ[X]) {u v m B : ℝ}
    (slice : ConcreteLocalizedContourSlice A u v m)
    (hu : 0 < u) (hu1 : u < 1) (hm : 1 ≤ m)
    (hB : 5 ≤ B) :
    ‖localizedFarZeroResidueSum A
        ((u : ℂ) + I * v) m B slice.zeros‖ ≤
      ExplicitFormulaAux.globalZeroMultiplicity
          (12 * m + |v| + 1) *
        ((∑ k ∈ A.support, ‖A.coeff k‖) *
          (localizedFarZeroLinearCoefficient v * m) ^ A.natDegree *
          Real.exp (-8 * m)) := by
  let H : ℝ := 12 * m + |v| + 1
  let K : ℝ := localizedFarZeroLinearCoefficient v
  let S : ℝ := ∑ k ∈ A.support, ‖A.coeff k‖
  let farZeros : Finset ℂ :=
    slice.zeros.filter
      (fun rho => B < |rho.im - (((u : ℂ) + I * v).im)|)
  let common : ℝ :=
    S * (K * m) ^ A.natDegree * Real.exp (-8 * m)
  have hK : 0 < K := localizedFarZeroLinearCoefficient_pos v
  have hKm : 1 ≤ K * m := by
    dsimp [K, localizedFarZeroLinearCoefficient]
    nlinarith [abs_nonneg v]
  have hcommon : 0 ≤ common := by
    dsimp [common, S]
    positivity
  have hsubset :
      farZeros ⊆ nontrivialZerosFinset H := by
    intro rho hrho
    have hrhoZeros := (Finset.mem_filter.mp hrho).1
    dsimp [H]
    exact slice.mem_nontrivialZerosFinset_linearHeight hrhoZeros
  have hmult :
      (∑ rho ∈ farZeros,
          (analyticOrderNatAt riemannZeta rho : ℝ)) ≤
        ExplicitFormulaAux.globalZeroMultiplicity H := by
    unfold ExplicitFormulaAux.globalZeroMultiplicity
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun rho _hrho _hnot => Nat.cast_nonneg _)
  have hterm (rho : ℂ) (hrho : rho ∈ farZeros) :
      ‖(analyticOrderNatAt riemannZeta rho : ℂ) *
          localizedGaussianWeight A
            ((u : ℂ) + I * v) m rho‖ ≤
        (analyticOrderNatAt riemannZeta rho : ℝ) * common := by
    have hrhoZeros := (Finset.mem_filter.mp hrho).1
    have hfarB := (Finset.mem_filter.mp hrho).2
    have hrhoNT := slice.isNontrivialZero_of_mem hrhoZeros
    have hrhoH :=
      mem_nontrivialZerosFinset.mp
        (slice.mem_nontrivialZerosFinset_linearHeight hrhoZeros)
    have hcenter :
        ‖rho - ((u : ℂ) + I * v)‖ ≤ K * m := by
      dsimp [K]
      exact norm_sub_center_le_linearHeight
        hu hu1 hm hrhoNT hrhoH.2
    have hpoly :
        ‖A.eval (rho - ((u : ℂ) + I * v))‖ ≤
          S * (K * m) ^ A.natDegree := by
      calc
        _ ≤ S * max 1 ‖rho - ((u : ℂ) + I * v)‖ ^
              A.natDegree := by
          dsimp [S]
          exact norm_polynomial_eval_le_coeffL1_mul_max_pow A _
        _ ≤ S * (K * m) ^ A.natDegree := by
          gcongr
          rw [max_le_iff]
          exact ⟨hKm, hcenter⟩
    have hweight :
        ‖localizedGaussianWeight A
            ((u : ℂ) + I * v) m rho‖ ≤ common := by
      calc
        _ ≤ ‖A.eval (rho - ((u : ℂ) + I * v))‖ *
              Real.exp (-8 * m) :=
          norm_localizedGaussianWeight_far_le A hu hu1
            (zero_le_one.trans hm) hrhoNT (by
              simpa using (hB.trans_lt hfarB).le)
        _ ≤ common := by
          dsimp [common]
          gcongr
    rw [norm_mul]
    simpa using
      mul_le_mul_of_nonneg_left hweight
        (show 0 ≤
          (analyticOrderNatAt riemannZeta rho : ℝ) by positivity)
  unfold localizedFarZeroResidueSum
  change ‖∑ rho ∈ farZeros,
      (analyticOrderNatAt riemannZeta rho : ℂ) *
        localizedGaussianWeight A
          ((u : ℂ) + I * v) m rho‖ ≤ _
  change _ ≤ ExplicitFormulaAux.globalZeroMultiplicity H * common
  calc
    _ ≤ ∑ rho ∈ farZeros,
        ‖(analyticOrderNatAt riemannZeta rho : ℂ) *
          localizedGaussianWeight A
            ((u : ℂ) + I * v) m rho‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈ farZeros,
        (analyticOrderNatAt riemannZeta rho : ℝ) * common :=
      Finset.sum_le_sum hterm
    _ = (∑ rho ∈ farZeros,
          (analyticOrderNatAt riemannZeta rho : ℝ)) * common := by
      rw [Finset.sum_mul]
    _ ≤ ExplicitFormulaAux.globalZeroMultiplicity H * common :=
      mul_le_mul_of_nonneg_right hmult hcommon

/-- Fixed coefficient in the final far-zero decay envelope. -/
def localizedFarZeroDecayConstant
    (A : ℂ[X]) (v C : ℝ) : ℝ :=
  2 * C * (∑ k ∈ A.support, ‖A.coeff k‖) *
    localizedFarZeroLinearCoefficient v ^ (A.natDegree + 2)

theorem localizedFarZeroDecayConstant_nonneg
    (A : ℂ[X]) {v C : ℝ} (hC : 0 ≤ C) :
    0 ≤ localizedFarZeroDecayConstant A v C := by
  unfold localizedFarZeroDecayConstant
  positivity [localizedFarZeroLinearCoefficient_pos v]

private theorem log_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ x := by
  calc
    Real.log x ≤ x - 1 :=
      Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hx)
    _ ≤ x := by linarith

/--
After inserting the global `O(T log T)` zero count, the selected far-zero sum
is bounded by a fixed polynomial times `exp (-8m)`.
-/
theorem norm_localizedFarZeroResidueSum_le_decayEnvelope
    (A : ℂ[X]) {u v m B C : ℝ}
    (slice : ConcreteLocalizedContourSlice A u v m)
    (hu : 0 < u) (hu1 : u < 1) (hm : 1 ≤ m)
    (hB : 5 ≤ B) (hC : 0 ≤ C)
    (hcount :
      ExplicitFormulaAux.globalZeroMultiplicity
          (12 * m + |v| + 1) ≤
        C * (12 * m + |v| + 1) *
          (1 + Real.log (12 * m + |v| + 1 + 6))) :
    ‖localizedFarZeroResidueSum A
        ((u : ℂ) + I * v) m B slice.zeros‖ ≤
      localizedFarZeroDecayConstant A v C *
        m ^ (A.natDegree + 2) * Real.exp (-8 * m) := by
  let H : ℝ := 12 * m + |v| + 1
  let K : ℝ := localizedFarZeroLinearCoefficient v
  let S : ℝ := ∑ k ∈ A.support, ‖A.coeff k‖
  have hK : 0 < K := localizedFarZeroLinearCoefficient_pos v
  have hKm : 1 ≤ K * m := by
    dsimp [K, localizedFarZeroLinearCoefficient]
    nlinarith [abs_nonneg v]
  have hvScale : |v| ≤ |v| * m := by
    nlinarith [mul_nonneg (abs_nonneg v) (sub_nonneg.mpr hm)]
  have hH : H ≤ K * m := by
    dsimp [H, K, localizedFarZeroLinearCoefficient]
    ring_nf
    nlinarith [mul_nonneg (abs_nonneg v) (zero_le_one.trans hm)]
  have hHsix : H + 6 ≤ K * m := by
    dsimp [H, K, localizedFarZeroLinearCoefficient]
    ring_nf
    nlinarith [mul_nonneg (abs_nonneg v) (zero_le_one.trans hm)]
  have hlogNonneg : 0 ≤ Real.log (H + 6) := by
    apply Real.log_nonneg
    dsimp [H]
    nlinarith [abs_nonneg v]
  have hlog : Real.log (H + 6) ≤ K * m :=
    (log_le_self_of_one_le (by
      dsimp [H]
      nlinarith [abs_nonneg v])).trans hHsix
  have hcountEnvelope :
      ExplicitFormulaAux.globalZeroMultiplicity H ≤
        2 * C * (K * m) ^ 2 := by
    calc
      _ ≤ C * H * (1 + Real.log (H + 6)) := by
        simpa [H, add_assoc] using hcount
      _ ≤ C * (K * m) * (2 * (K * m)) := by
        gcongr
        nlinarith
      _ = 2 * C * (K * m) ^ 2 := by ring
  have hbase :=
    norm_localizedFarZeroResidueSum_le_globalMultiplicity
      A slice hu hu1 hm hB
  calc
    _ ≤ ExplicitFormulaAux.globalZeroMultiplicity H *
        (S * (K * m) ^ A.natDegree *
          Real.exp (-8 * m)) := by
      simpa [H, K, S] using hbase
    _ ≤ (2 * C * (K * m) ^ 2) *
        (S * (K * m) ^ A.natDegree *
          Real.exp (-8 * m)) := by
      gcongr
    _ = localizedFarZeroDecayConstant A v C *
          m ^ (A.natDegree + 2) * Real.exp (-8 * m) := by
      unfold localizedFarZeroDecayConstant
      dsimp [K, S]
      rw [mul_pow]
      ring

theorem tendsto_localizedFarZeroDecayEnvelope
    (A : ℂ[X]) (v C : ℝ) :
    Tendsto
      (fun m : ℝ =>
        localizedFarZeroDecayConstant A v C *
          m ^ (A.natDegree + 2) * Real.exp (-8 * m))
      atTop (𝓝 0) := by
  have hbase :
      Tendsto
        (fun m : ℝ =>
          m ^ (A.natDegree + 2) * Real.exp (-8 * m))
        atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        ((A.natDegree + 2 : ℕ) : ℝ) 8 (by norm_num)
  simpa [mul_assoc] using
    (tendsto_const_nhds.mul hbase :
      Tendsto
        (fun m : ℝ =>
          localizedFarZeroDecayConstant A v C *
            (m ^ (A.natDegree + 2) * Real.exp (-8 * m)))
        atTop (𝓝 (localizedFarZeroDecayConstant A v C * 0)))

/--
For every fixed vertical band `B ≥ 5`, the selected far-zero sum for the
fixed local pole filter tends to zero.
-/
theorem tendsto_selectedLocalizedFarZeroResidueSum
    {u v B : ℝ} (hu : 0 < u) (hu1 : u < 1) (hB : 5 ≤ B) :
    Tendsto (selectedLocalizedFarZeroResidueSum u v B)
      atTop (𝓝 0) := by
  let w : ℂ := (u : ℂ) + I * v
  let A : ℂ[X] := localizedNearZeroFilter w B
  rcases ExplicitFormulaAux.exists_globalZeroMultiplicity_le_mul_log with
    ⟨C, hC, hcount⟩
  let upper : ℝ → ℝ := fun m =>
    localizedFarZeroDecayConstant A v C *
      m ^ (A.natDegree + 2) * Real.exp (-8 * m)
  have hupper : Tendsto upper atTop (𝓝 0) := by
    exact tendsto_localizedFarZeroDecayEnvelope A v C
  have hbound :
      ∀ᶠ m : ℝ in atTop,
        ‖selectedLocalizedFarZeroResidueSum u v B m‖ ≤ upper m := by
    filter_upwards [
      eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop (A.natDegree : ℝ)] with m hm hdegree
    have hvalid : localizedContourScaleValid A u m :=
      ⟨hu, hu1, hm, hdegree⟩
    let slice : ConcreteLocalizedContourSlice A u v m :=
      selectedConcreteLocalizedContourSlice A u v m hvalid
    rw [selectedLocalizedFarZeroResidueSum, dif_pos hvalid]
    change ‖localizedFarZeroResidueSum A w m B slice.zeros‖ ≤ upper m
    apply norm_localizedFarZeroResidueSum_le_decayEnvelope
      A slice hu hu1 hm hB hC
    apply hcount
    nlinarith [abs_nonneg v]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero'
    (Eventually.of_forall fun _ => norm_nonneg _)
    hbound hupper

/--
The selected weighted zero sum for the fixed near-zero filter converges to
the target analytic multiplicity.
-/
theorem tendsto_selectedLocalizedZeroResidueSum_nearZeroFilter
    {u v B : ℝ} (hu : 0 < u) (hu1 : u < 1) (hB : 5 ≤ B)
    (hzero : riemannZeta ((u : ℂ) + I * v) = 0) :
    Tendsto
      (selectedLocalizedZeroResidueSum
        (localizedNearZeroFilter ((u : ℂ) + I * v) B) u v)
      atTop
      (𝓝 (analyticOrderNatAt riemannZeta
        ((u : ℂ) + I * v) : ℂ)) := by
  let A : ℂ[X] :=
    localizedNearZeroFilter ((u : ℂ) + I * v) B
  have hfar :=
    tendsto_selectedLocalizedFarZeroResidueSum
      (v := v) (B := B) hu hu1 hB
  have hsum :
      Tendsto
        (fun m =>
          (analyticOrderNatAt riemannZeta
              ((u : ℂ) + I * v) : ℂ) +
            selectedLocalizedFarZeroResidueSum u v B m)
        atTop
        (𝓝 ((analyticOrderNatAt riemannZeta
          ((u : ℂ) + I * v) : ℂ) + 0)) :=
    tendsto_const_nhds.add hfar
  have hsum' :
      Tendsto
        (fun m =>
          (analyticOrderNatAt riemannZeta
              ((u : ℂ) + I * v) : ℂ) +
            selectedLocalizedFarZeroResidueSum u v B m)
        atTop
        (𝓝 (analyticOrderNatAt riemannZeta
          ((u : ℂ) + I * v) : ℂ)) := by
    simpa using hsum
  apply hsum'.congr'
  filter_upwards [
    eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (A.natDegree : ℝ)] with m hm hdegree
  have hvalid : localizedContourScaleValid A u m :=
    ⟨hu, hu1, hm, hdegree⟩
  symm
  simpa [A] using
    selectedLocalizedZeroResidueSum_nearZeroFilter_eq_target_add_far
      (show 0 ≤ B by linarith) hvalid hzero

/-- At a nonzero center, the selected weighted zero sum for the fixed local
filter converges to zero. -/
theorem tendsto_selectedLocalizedZeroResidueSum_nearZeroFilter_of_ne_zero
    {u v B : ℝ} (hu : 0 < u) (hu1 : u < 1) (hB : 5 ≤ B)
    (hne : riemannZeta ((u : ℂ) + I * v) ≠ 0) :
    Tendsto
      (selectedLocalizedZeroResidueSum
        (localizedNearZeroFilter ((u : ℂ) + I * v) B) u v)
      atTop (𝓝 0) := by
  let A : ℂ[X] :=
    localizedNearZeroFilter ((u : ℂ) + I * v) B
  have hfar :=
    tendsto_selectedLocalizedFarZeroResidueSum
      (v := v) (B := B) hu hu1 hB
  apply hfar.congr'
  filter_upwards [
    eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (A.natDegree : ℝ)] with m hm hdegree
  have hvalid : localizedContourScaleValid A u m :=
    ⟨hu, hu1, hm, hdegree⟩
  simpa [A] using
    selectedLocalizedZeroResidueSum_nearZeroFilter_eq_far_of_ne_zero
      hvalid hne

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
