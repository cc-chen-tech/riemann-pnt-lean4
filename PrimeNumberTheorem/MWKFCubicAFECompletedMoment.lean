import PrimeNumberTheorem.MWKFCubicAFECompletedReassembly

open Complex Filter MeasureTheory
open scoped Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# The actual finite-height moment at any finite lower-scale completion

The completed zero mode is its literal physical integral. The moment uses
the zero/nonzero pair inside each shift before the outer shift sum. The
recombined height limit allows arbitrary finite completion depth at each V;
it does not establish separate height or lower-endpoint limits.
-/

noncomputable def cubicAFECompletedBoundaryPhysicalKernel
    (W : CubicTestWeight) (T X V : ℝ) (d e : ℕ) (δ : ℤ) (J : ℕ) (t x : ℝ) : ℂ :=
  (cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) : ℂ) *
    cubicAFEProgressionPhysicalSummand W T X V d e δ t x

theorem cubicAFECompletedBoundaryPhysicalKernel_eq_boundary_add_correction
    (W : CubicTestWeight) (T X V : ℝ) (d e : ℕ) (δ : ℤ) (J : ℕ) (t x : ℝ) :
    cubicAFECompletedBoundaryPhysicalKernel W T X V d e δ J t x =
      cubicAFEBoundaryPhysicalKernel W T X V d e δ t x +
        cubicAFEDyadicCompletionCorrection W T X V d e δ J t x :=
  cubicAFEDyadicCompletionKernel_eq_boundary_add_correction W T X V d e δ J t x

theorem integrable_cubicAFECompletedBoundaryPhysicalKernel
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (J : ℕ) :
    Integrable (Function.uncurry (cubicAFECompletedBoundaryPhysicalKernel W T X V d e δ J)) := by
  apply ((integrable_cubicAFEBoundaryPhysicalKernel W hT hX V hd he δ).add
    (integrable_cubicAFEDyadicCompletionCorrection W hT hX V hd he δ J)).congr
  filter_upwards [] with p
  exact (cubicAFECompletedBoundaryPhysicalKernel_eq_boundary_add_correction
    W T X V d e δ J p.1 p.2).symm

private theorem completed_physical_integral_add
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (J : ℕ) :
    (∫ t : ℝ, ∫ x : ℝ, cubicAFECompletedBoundaryPhysicalKernel W T X V d e δ J t x) =
      (∫ t : ℝ, ∫ x : ℝ, cubicAFEBoundaryPhysicalKernel W T X V d e δ t x) +
      (∫ t : ℝ, ∫ x : ℝ, cubicAFEDyadicCompletionCorrection W T X V d e δ J t x) := by
  have hn := integrable_cubicAFECompletedBoundaryPhysicalKernel W hT hX V hd he δ J
  have ho := integrable_cubicAFEBoundaryPhysicalKernel W hT hX V hd he δ
  have hc := integrable_cubicAFEDyadicCompletionCorrection W hT hX V hd he δ J
  calc
    _ = ∫ p : ℝ × ℝ, cubicAFECompletedBoundaryPhysicalKernel W T X V d e δ J p.1 p.2 :=
      (integral_prod _ hn).symm
    _ = (∫ p : ℝ × ℝ, cubicAFEBoundaryPhysicalKernel W T X V d e δ p.1 p.2) +
        (∫ p : ℝ × ℝ, cubicAFEDyadicCompletionCorrection W T X V d e δ J p.1 p.2) := by
      simp_rw [cubicAFECompletedBoundaryPhysicalKernel_eq_boundary_add_correction]
      exact integral_add ho hc
    _ = _ := congrArg₂ (· + ·) (integral_prod _ ho) (integral_prod _ hc)

/-- All completed dyadic zero modes sum to their actual physical double integral,
including both lower-boundary weights. No uncut endpoint integral is substituted. -/
theorem hasSum_cubicAFECompletedZeroModeBox_physical
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (J : ℕ) :
    HasSum (cubicAFECompletedZeroModeBox (d := d) W T X V he δ J)
      ((((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∫ t : ℝ, ∫ x : ℝ,
        cubicAFECompletedBoundaryPhysicalKernel W T X V d e δ J t x) := by
  obtain ⟨L, hL⟩ := exists_cubicAFECompletedLowerScale_bound d e δ J
  have hs := hasSum_cubicAFECompletedZeroModeBox W hT hX V hd he δ J L hL
  have hc := integral_cubicAFEDyadicCompletionCorrection_eq_zeroModes W hT hX V hd he δ J L hL
  rw [← hc, (hasSum_cubicAFEZeroModeBoxFinite W hT hX V hd he δ).tsum_eq] at hs
  rw [completed_physical_integral_add W hT hX V hd he δ J, mul_add, add_comm]
  exact hs

noncomputable def cubicAFECompletedMomentFinite (W : CubicTestWeight) (T X V : ℝ) (J : ℕ) : ℂ :=
  ∑ d ∈ (cubicMollifierSupport T).attach,
    ∑ e ∈ (cubicMollifierSupport T).attach,
      ∑' δ : {δ : ℤ // δ ≠ 0},
        ((∑' jk : ℕ × ℕ, cubicAFECompletedZeroModeBox (d := d.val) W T X V
          (show 0 < e.val from (Finset.mem_Icc.mp e.property).1) δ.val J jk) +
        (∑' jk : ℕ × ℕ, cubicAFECompletedNonzeroModeBox (d := d.val) W T X V
          (show 0 < e.val from (Finset.mem_Icc.mp e.property).1) δ.val J jk))

/-- The shift series of recombined completed pairs is summable; this makes no
claim about absolute summability of each completed mode separately over shifts. -/
theorem summable_shift_cubicAFECompletedModes
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (J : ℕ) :
    Summable (fun δ : {δ : ℤ // δ ≠ 0} ↦
      (∑' jk : ℕ × ℕ, cubicAFECompletedZeroModeBox (d := d) W T X V he δ.val J jk) +
      (∑' jk : ℕ × ℕ, cubicAFECompletedNonzeroModeBox (d := d) W T X V he δ.val J jk)) := by
  apply (summable_shift_cubicAFEFrequencyBoxFinite W hT hX V hd he).congr
  intro δ
  rw [tsum_cubicAFECompletedModes_eq_original W hT hX V hd he δ.val J,
    tsum_cubicAFEFrequencyBoxFinite_eq_zero_add_nonzero W hT hX V hd he δ.val]

theorem cubicAFECompletedMomentFinite_eq_frequency
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) (J : ℕ) :
    cubicAFECompletedMomentFinite W T X V J = cubicAFEFrequencyMomentFinite W T X V := by
  unfold cubicAFECompletedMomentFinite cubicAFEFrequencyMomentFinite
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  apply tsum_congr
  intro δ
  rw [tsum_cubicAFECompletedModes_eq_original W hT hX V
    (Finset.mem_Icc.mp d.property).1 (Finset.mem_Icc.mp e.property).1 δ.val J,
    tsum_cubicAFEFrequencyBoxFinite_eq_zero_add_nonzero W hT hX V
      (Finset.mem_Icc.mp d.property).1 (Finset.mem_Icc.mp e.property).1 δ.val]

theorem cubicAFEMollifiedMomentFinite_eq_diagonal_add_completed
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) (J : ℕ) :
    cubicAFEMollifiedMomentFinite W T X V = cubicAFEDiagonalMomentFinite W T X V +
      cubicAFECompletedMomentFinite W T X V J := by
  rw [cubicAFECompletedMomentFinite_eq_frequency W hT hX V J]
  exact cubicAFEMollifiedMomentFinite_eq_diagonal_add_frequency W hT hX V

/-- Even a varying finite completion depth is allowed in the recombined limit;
there is no assertion that any individual zero/nonzero limit exists. -/
theorem tendsto_cubicAFEDiagonal_add_completed
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (J : ℝ → ℕ) :
    Tendsto (fun V : ℝ ↦ cubicAFEDiagonalMomentFinite W T X V +
      cubicAFECompletedMomentFinite W T X V (J V))
      atTop (nhds (cubicMollifiedSecondMoment W T : ℂ)) := by
  apply (tendsto_cubicAFEMollifiedMomentFinite W hT hX).congr'
  exact Eventually.of_forall (fun V ↦
    cubicAFEMollifiedMomentFinite_eq_diagonal_add_completed W hT hX V (J V))

end PrimeNumberTheorem.MWKFCubic
