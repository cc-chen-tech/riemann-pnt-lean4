import PrimeNumberTheorem.MWKFCubicAFEDyadicReassembly

open Complex Set MeasureTheory

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Actual dyadic Poisson boxes under the physical time integral

A single box contains only finitely many contributing progression integers.
This uniform-in-time finite support proves the original-series/time-integral
interchange without assuming a Fourier majorant. The complete frequency sum
stays inside the time integral; interchanging that frequency sum is a separate
analytic step and is not asserted here.
-/

noncomputable def cubicAFEProgressionDyadicIndices (d e : ℕ) (δ : ℤ) (j : ℕ) :
    Finset (cubicAFEProgression d e δ) := by
  classical
  exact (Finset.range (2 * 2^j + 1)).subtype (fun m ↦ m ∈ cubicAFEProgression d e δ)

theorem mem_cubicAFEProgressionDyadicIndices {d e : ℕ} {δ : ℤ} {j : ℕ}
    (m : cubicAFEProgression d e δ) :
    m ∈ cubicAFEProgressionDyadicIndices d e δ j ↔ m.val ≤ 2 * 2^j := by
  classical
  simp [cubicAFEProgressionDyadicIndices]

theorem cubicAFEProgressionDyadicCutoff_zero_of_not_mem_indices {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (j k : ℕ) (m : cubicAFEProgression d e δ)
    (hm : m ∉ cubicAFEProgressionDyadicIndices d e δ j) :
    cubicAFEProgressionDyadicCutoff (d := d) he δ j k m.val = 0 := by
  by_contra hn
  have hb := (cubicAFEProgressionDyadicCutoff_scales he hn).1.2
  apply hm
  apply (mem_cubicAFEProgressionDyadicIndices m).mpr
  exact_mod_cast hb

theorem integrable_cubicAFECombinedSummandFinite
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) (p : ℕ × ℕ) :
    Integrable (fun t : ℝ ↦ cubicAFECombinedSummandFinite W T X V d e t p) := by
  simp_rw [cubicAFECombinedSummandFinite_eq_outerWeight]
  exact ((continuous_cubicAFEWeightFinite_time hX V p).mul
    (continuous_cubicAFEPairOuterWeight W T hd he)).integrable_of_hasCompactSupport
      (hasCompactSupport_cubicAFEPairOuterWeight W hT d e).mul_left

theorem tsum_cubicAFEDyadicProgression_eq_finsetSum
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (jk : ℕ × ℕ) (t : ℝ) :
    (∑' m : cubicAFEProgression d e δ,
      (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 m.val : ℂ) *
        cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m.val)) =
      ∑ m ∈ cubicAFEProgressionDyadicIndices d e δ jk.1,
        (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 m.val : ℂ) *
          cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m.val) := by
  apply tsum_eq_sum
  intro m hm
  rw [cubicAFEProgressionDyadicCutoff_zero_of_not_mem_indices he δ jk.1 jk.2 m hm,
    Complex.ofReal_zero, zero_mul]

theorem integral_tsum_cubicAFEDyadicProgression
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : d ≠ 0) (he : 0 < e) (δ : ℤ) (jk : ℕ × ℕ) :
    (∫ t : ℝ, ∑' m : cubicAFEProgression d e δ,
      (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 m.val : ℂ) *
        cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m.val)) =
      ∑' m : cubicAFEProgression d e δ, ∫ t : ℝ,
        (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 m.val : ℂ) *
          cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m.val) := by
  simp_rw [tsum_cubicAFEDyadicProgression_eq_finsetSum W T X V he δ jk]
  rw [integral_finsetSum _ (fun m _ ↦
    (integrable_cubicAFECombinedSummandFinite W hT hX V hd he.ne' _).const_mul _)]
  symm
  apply tsum_eq_sum
  intro m hm
  simp only [cubicAFEProgressionDyadicCutoff_zero_of_not_mem_indices he δ jk.1 jk.2 m hm,
    Complex.ofReal_zero, zero_mul, integral_zero]

/-- The whole Poisson box, not merely each original coefficient, is an
integrable function of physical time. -/
theorem integrable_cubicAFEDyadicPoissonTerm
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (jk : ℕ × ℕ) :
    Integrable (fun t : ℝ ↦ cubicAFEDyadicPoissonTerm (d := d) W T X V he δ jk t) := by
  simp_rw [cubicAFEDyadicPoissonTerm_eq_cutoffSum W T X V hd he δ jk _ hX,
    tsum_cubicAFEDyadicProgression_eq_finsetSum W T X V he δ jk]
  exact integrable_finsetSum _ (fun m _ ↦
    (integrable_cubicAFECombinedSummandFinite W hT hX V hd.ne' he.ne' _).const_mul _)

theorem integral_cubicAFEDyadicPoissonTerm_eq
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (jk : ℕ × ℕ) :
    (∫ t : ℝ, cubicAFEDyadicPoissonTerm (d := d) W T X V he δ jk t) =
      ∑' m : cubicAFEProgression d e δ, ∫ t : ℝ,
        (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 m.val : ℂ) *
          cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m.val) := by
  simp_rw [cubicAFEDyadicPoissonTerm_eq_cutoffSum W T X V hd he δ jk _ hX]
  exact integral_tsum_cubicAFEDyadicProgression W hT hX V hd.ne' he δ jk

/-- Each original time-integrated shifted progression is the sum of the
actual integrated Poisson boxes. The frequency sum is inside each integral. -/
theorem cubicAFEProgressionIntegral_eq_dyadicPoisson
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) :
    (∑' m : cubicAFEProgression d e δ, ∫ t : ℝ,
      cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m.val)) =
      ∑' jk : ℕ × ℕ, ∫ t : ℝ, cubicAFEDyadicPoissonTerm (d := d) W T X V he δ jk t := by
  rw [cubicAFEProgressionIntegral_eq_dyadic W hT hX V hd.ne' he δ]
  apply tsum_congr
  intro jk
  exact (integral_cubicAFEDyadicPoissonTerm_eq W hT hX V hd he δ jk).symm

theorem summable_integral_cubicAFEDyadicPoissonTerm
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) :
    Summable (fun jk : ℕ × ℕ ↦ ∫ t : ℝ,
      cubicAFEDyadicPoissonTerm (d := d) W T X V he δ jk t) := by
  apply (summable_cubicAFEProgressionDyadicIntegral W hT hX V hd.ne' he δ).congr
  intro jk
  exact (integral_cubicAFEDyadicPoissonTerm_eq W hT hX V hd he δ jk).symm

end PrimeNumberTheorem.MWKFCubic
