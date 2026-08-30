import PrimeNumberTheorem.MWKFCubicAFECompletedBoundary
import PrimeNumberTheorem.MWKFCubicAFEZeroModeReassembly

open Complex MeasureTheory Set
open scoped FourierTransform

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Finite physical correction and separate completed-mode reassembly

At fixed finite J and Mellin height V, the added real-domain correction is
a finite sum of actual smooth compact kernels. Its zero mode and nonzero
modes cancel after finite aggregation. The separate completed dyadic mode
series are summable. No limit as J or V tends to infinity is exchanged.
-/

private theorem hasSum_completed_family {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] (J L : ℕ) (f : ℕ × ℕ → E) (a : E)
    (hs : HasSum (fun jk : ℕ × ℕ ↦ f (J + jk.1, J + jk.2)) a)
    (hz : ∀ jk : ℕ × ℕ, jk.1 < J ∨ jk.2 < J →
      jk ∉ cubicAFECompletedLowerScaleBoxes J L → f jk = 0) :
    HasSum f ((∑ jk ∈ cubicAFECompletedLowerScaleBoxes J L, f jk) + a) := by
  classical
  let F := cubicAFECompletedLowerScaleBoxes J L
  let e (jk : ℕ × ℕ) := (J + jk.1, J + jk.2)
  let g (jk : ℕ × ℕ) := if jk ∈ F then 0 else f jk
  have hi : Function.Injective e := by
    intro jk mn h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext (Nat.add_left_cancel h1) (Nat.add_left_cancel h2)
  have hnot (jk : ℕ × ℕ) : e jk ∉ F := by
    simp [F, e, cubicAFECompletedLowerScaleBoxes]
  have hgout (jk : ℕ × ℕ) (hout : jk ∉ range e) : g jk = 0 := by
    have hl : jk.1 < J ∨ jk.2 < J := by
      by_contra hn
      have h1 : J ≤ jk.1 := by omega
      have h2 : J ≤ jk.2 := by omega
      exact hout ⟨(jk.1 - J, jk.2 - J),
        Prod.ext (Nat.add_sub_of_le h1) (Nat.add_sub_of_le h2)⟩
    by_cases hf : jk ∈ F
    · simp only [g, if_pos hf]
    · simpa only [g, if_neg hf] using hz jk hl hf
  have hsg : HasSum g a := by
    apply (hi.hasSum_iff hgout).mp
    simpa only [Function.comp_def, g, if_neg (hnot _)] using hs
  have hfin : HasSum (fun jk ↦ if jk ∈ F then f jk else 0) (∑ jk ∈ F, f jk) := by
    have hh : HasSum (fun jk ↦ if jk ∈ F then f jk else 0)
        (∑ jk ∈ F, if jk ∈ F then f jk else 0) :=
      hasSum_sum_of_ne_finset_zero (fun jk hjk ↦ if_neg hjk)
    simpa only [Finset.sum_ite_mem, Finset.inter_self] using hh
  apply (hfin.add hsg).congr_fun
  intro jk
  by_cases hf : jk ∈ F <;> simp only [g, hf, ↓reduceIte, zero_add, add_zero]

theorem cubicAFEDyadicCompletionCorrection_eq_finiteSum
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (δ : ℤ) (J L : ℕ)
    (hL : 2 * (2 : ℝ)^J * cubicAFECompletedBoundarySize d e δ < (2 : ℝ)^L)
    (t x : ℝ) :
    cubicAFEDyadicCompletionCorrection W T X V d e δ J t x =
      ∑ jk ∈ cubicAFECompletedLowerScaleBoxes J L,
        cubicAFEProgressionCutoffSummand W T X V
          (cubicAFEProgressionCompletedCutoff (d := d) he δ J jk.1 jk.2) t x := by
  let f (jk : ℕ × ℕ) := cubicAFEProgressionCompletedCutoff (d := d) he δ J jk.1 jk.2 x
  have hs : HasSum (fun jk : ℕ × ℕ ↦ f (J + jk.1, J + jk.2))
      (cubicAFEDyadicCompletionWeight 0 x (cubicAFEProgressionRealSecond d e δ x)) := by
    simp only [f, cubicAFEProgressionCompletedCutoff_shift, cubicAFEDyadicCompletionWeight_zero]
    exact hasSum_cubicAFEProgressionDyadicCutoff_allReal he δ x
  have hh := hasSum_completed_family J L f _ hs (fun jk hjk hout ↦
    cubicAFEProgressionCompletedCutoff_zero_outside_lowerBoxes hd he hL hjk hout x)
  have ha : HasSum f (cubicAFEDyadicCompletionWeight J x
      (cubicAFEProgressionRealSecond d e δ x)) :=
    hasSum_cubicAFEDyadicCompletionWeight J x _
  have hdiff : cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) -
      cubicAFEDyadicCompletionWeight 0 x (cubicAFEProgressionRealSecond d e δ x) =
      ∑ jk ∈ cubicAFECompletedLowerScaleBoxes J L, f jk :=
    sub_eq_iff_eq_add.mpr (ha.unique hh)
  unfold cubicAFEDyadicCompletionCorrection
  rw [hdiff, Complex.ofReal_sum, Finset.sum_mul]
  rfl

private theorem completedCoefficient_zero_outside_lowerBoxes
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    {δ : ℤ} {J L : ℕ}
    (hL : 2 * (2 : ℝ)^J * cubicAFECompletedBoundarySize d e δ < (2 : ℝ)^L)
    {jk : ℕ × ℕ} (hjk : jk.1 < J ∨ jk.2 < J)
    (hout : jk ∉ cubicAFECompletedLowerScaleBoxes J L) (h : ℤ) :
    cubicAFECompletedFrequencyCoefficient (d := d) W T X V he δ J jk h = 0 := by
  have hc (t : ℝ) : cubicAFEProgressionCutoffSummand W T X V
      (cubicAFEProgressionCompletedCutoff (d := d) he δ J jk.1 jk.2) t = 0 := by
    funext x
    simp only [cubicAFEProgressionCutoffSummand,
      cubicAFEProgressionCompletedCutoff_zero_outside_lowerBoxes hd he hL hjk hout x,
      Complex.ofReal_zero, zero_mul, Pi.zero_apply]
  simp only [cubicAFECompletedFrequencyCoefficient, hc, Real.fourier_real_eq_integral_exp_smul,
    Pi.zero_apply, smul_zero, integral_zero, zero_mul]

private theorem completedKernel_integrable
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (J : ℕ) (jk : ℕ × ℕ) :
    Integrable (Function.uncurry (cubicAFEProgressionCutoffSummand W T X V
      (cubicAFEProgressionCompletedCutoff (d := d) he δ J jk.1 jk.2))) :=
  (continuous_cubicAFEProgressionCutoffSummand_joint W T X V hd he _ hX).integrable_of_hasCompactSupport
    (hasCompactSupport_cubicAFEProgressionCutoffSummand_joint W hT X V _)

theorem integrable_cubicAFEDyadicCompletionCorrection
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (J : ℕ) :
    Integrable (Function.uncurry (cubicAFEDyadicCompletionCorrection W T X V d e δ J)) := by
  obtain ⟨L, hL⟩ := exists_cubicAFECompletedLowerScale_bound d e δ J
  have hh : Function.uncurry (cubicAFEDyadicCompletionCorrection W T X V d e δ J) =
      fun p : ℝ × ℝ ↦ ∑ jk ∈ cubicAFECompletedLowerScaleBoxes J L,
        cubicAFEProgressionCutoffSummand W T X V
          (cubicAFEProgressionCompletedCutoff (d := d) he δ J jk.1 jk.2) p.1 p.2 := by
    funext p
    exact cubicAFEDyadicCompletionCorrection_eq_finiteSum W T X V hd he δ J L hL p.1 p.2
  rw [hh]
  exact integrable_finsetSum _ (fun jk _ ↦ completedKernel_integrable W hT hX V hd he δ J jk)

/-- The finite real-domain correction has exactly the added physical zero modes.
The time/space exchange and finite integration are justified by actual joint integrability. -/
theorem integral_cubicAFEDyadicCompletionCorrection_eq_zeroModes
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (J L : ℕ)
    (hL : 2 * (2 : ℝ)^J * cubicAFECompletedBoundarySize d e δ < (2 : ℝ)^L) :
    (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) *
      (∫ t : ℝ, ∫ x : ℝ, cubicAFEDyadicCompletionCorrection W T X V d e δ J t x) =
      ∑ jk ∈ cubicAFECompletedLowerScaleBoxes J L,
        cubicAFECompletedZeroModeBox (d := d) W T X V he δ J jk := by
  have hc := integrable_cubicAFEDyadicCompletionCorrection W hT hX V hd he δ J
  have hi : (∫ p : ℝ × ℝ, cubicAFEDyadicCompletionCorrection W T X V d e δ J p.1 p.2) =
      ∫ t : ℝ, ∫ x : ℝ, cubicAFEDyadicCompletionCorrection W T X V d e δ J t x :=
    integral_prod _ hc
  rw [← hi]
  simp_rw [cubicAFEDyadicCompletionCorrection_eq_finiteSum W T X V hd he δ J L hL]
  rw [integral_finsetSum (f := fun jk (p : ℝ × ℝ) ↦
    cubicAFEProgressionCutoffSummand W T X V
      (cubicAFEProgressionCompletedCutoff (d := d) he δ J jk.1 jk.2) p.1 p.2)
    (cubicAFECompletedLowerScaleBoxes J L)
    (fun jk _ ↦ completedKernel_integrable W hT hX V hd he δ J jk), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro jk _
  have hj : (∫ p : ℝ × ℝ, cubicAFEProgressionCutoffSummand W T X V
      (cubicAFEProgressionCompletedCutoff (d := d) he δ J jk.1 jk.2) p.1 p.2) =
      ∫ t : ℝ, ∫ x : ℝ, cubicAFEProgressionCutoffSummand W T X V
        (cubicAFEProgressionCompletedCutoff (d := d) he δ J jk.1 jk.2) t x :=
    integral_prod _ (completedKernel_integrable W hT hX V hd he δ J jk)
  rw [cubicAFECompletedZeroModeBox, cubicAFECompletedFrequencyCoefficient_zero, hj]

theorem hasSum_cubicAFECompletedZeroModeBox
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (J L : ℕ)
    (hL : 2 * (2 : ℝ)^J * cubicAFECompletedBoundarySize d e δ < (2 : ℝ)^L) :
    HasSum (cubicAFECompletedZeroModeBox (d := d) W T X V he δ J)
      ((∑ jk ∈ cubicAFECompletedLowerScaleBoxes J L,
        cubicAFECompletedZeroModeBox (d := d) W T X V he δ J jk) +
      ∑' jk : ℕ × ℕ, cubicAFEZeroModeBoxFinite (d := d) W T X V he δ jk) := by
  apply hasSum_completed_family J L
  · simpa only [cubicAFECompletedZeroModeBox, cubicAFECompletedFrequencyCoefficient_shift,
      cubicAFEZeroModeBoxFinite] using (hasSum_cubicAFEZeroModeBoxFinite W hT hX V hd he δ).summable.hasSum
  · intro jk hjk hout
    simp only [cubicAFECompletedZeroModeBox,
      completedCoefficient_zero_outside_lowerBoxes W T X V hd he hL hjk hout, mul_zero]

theorem hasSum_cubicAFECompletedNonzeroModeBox
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (J L : ℕ)
    (hL : 2 * (2 : ℝ)^J * cubicAFECompletedBoundarySize d e δ < (2 : ℝ)^L) :
    HasSum (cubicAFECompletedNonzeroModeBox (d := d) W T X V he δ J)
      ((∑ jk ∈ cubicAFECompletedLowerScaleBoxes J L,
        cubicAFECompletedNonzeroModeBox (d := d) W T X V he δ J jk) +
      ∑' jk : ℕ × ℕ, cubicAFENonzeroModeBoxFinite (d := d) W T X V he δ jk) := by
  apply hasSum_completed_family J L
  · simpa only [cubicAFECompletedNonzeroModeBox, cubicAFECompletedFrequencyCoefficient_shift,
      cubicAFENonzeroModeBoxFinite] using (summable_cubicAFENonzeroModeBoxFinite W hT hX V hd he δ).hasSum
  · intro jk hjk hout
    simp only [cubicAFECompletedNonzeroModeBox,
      completedCoefficient_zero_outside_lowerBoxes W T X V hd he hL hjk hout, tsum_zero, mul_zero]

theorem cubicAFECompletedBoundary_zero_add_nonzero
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (J L : ℕ) :
    (∑ jk ∈ cubicAFECompletedLowerScaleBoxes J L,
      cubicAFECompletedZeroModeBox (d := d) W T X V he δ J jk) +
    (∑ jk ∈ cubicAFECompletedLowerScaleBoxes J L,
      cubicAFECompletedNonzeroModeBox (d := d) W T X V he δ J jk) = 0 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro jk hjk
  rw [← cubicAFECompletedFrequencyBox_eq_zero_add_nonzero W hT hX V hd he δ J jk]
  exact cubicAFECompletedFrequencyBox_lower_scale W hT hX V hd he δ (Finset.mem_filter.mp hjk).2

/-- Separate mode sums exist at each finite completion depth and their
recombined value agrees with the original nonnegative-scale decomposition. -/
theorem tsum_cubicAFECompletedModes_eq_original
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (J : ℕ) :
    (∑' jk : ℕ × ℕ, cubicAFECompletedZeroModeBox (d := d) W T X V he δ J jk) +
      (∑' jk : ℕ × ℕ, cubicAFECompletedNonzeroModeBox (d := d) W T X V he δ J jk) =
    (∑' jk : ℕ × ℕ, cubicAFEZeroModeBoxFinite (d := d) W T X V he δ jk) +
      (∑' jk : ℕ × ℕ, cubicAFENonzeroModeBoxFinite (d := d) W T X V he δ jk) := by
  obtain ⟨L, hL⟩ := exists_cubicAFECompletedLowerScale_bound d e δ J
  rw [(hasSum_cubicAFECompletedZeroModeBox W hT hX V hd he δ J L hL).tsum_eq,
    (hasSum_cubicAFECompletedNonzeroModeBox W hT hX V hd he δ J L hL).tsum_eq]
  have hh := cubicAFECompletedBoundary_zero_add_nonzero W hT hX V hd he δ J L
  linear_combination hh

end PrimeNumberTheorem.MWKFCubic
