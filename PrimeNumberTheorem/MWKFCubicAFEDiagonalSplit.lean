import PrimeNumberTheorem.MWKFCubicAFEOuterIntegral
import PrimeNumberTheorem.MWKFCubicStructural

open Filter MeasureTheory
open scoped BigOperators

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Exact diagonal and off-diagonal parts of the integrated finite-height AFE

Every split below is performed on an already summable family of physical
integrals.  The diagonal is reindexed by a bijection, without discarding the
Möbius weights.  The infinite-height limit is asserted for the sum of the two
pieces only; separate convergence and asymptotic estimates are not asserted.
-/

/-- The diagonal for the actual combined AFE--mollifier phase. -/
def cubicAFEDiagonal (d e : ℕ) : Set (ℕ × ℕ) :=
  {p | (p.2 + 1) * e = (p.1 + 1) * d}

/-- Zero-based indices on the diagonal: the first positive index is
`(k+1)*(e/gcd(d,e))`, and the second is `(k+1)*(d/gcd(d,e))`. -/
def cubicAFEDiagonalRay (d e k : ℕ) : ℕ × ℕ :=
  ((k + 1) * (e / Nat.gcd d e) - 1,
    (k + 1) * (d / Nat.gcd d e) - 1)

private theorem residual_moduli_pos {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    0 < d / Nat.gcd d e ∧ 0 < e / Nat.gcd d e := by
  have hq := Nat.gcd_pos_of_pos_left e hd
  obtain ⟨hdq, heq, _⟩ := gcd_extraction (Nat.ne_of_gt hq)
  constructor
  · apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, mul_zero] at hdq
    exact hd.ne' hdq
  · apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, mul_zero] at heq
    exact he.ne' heq

theorem cubicAFEDiagonalRay_succ {d e : ℕ} (hd : 0 < d) (he : 0 < e) (k : ℕ) :
    (cubicAFEDiagonalRay d e k).1 + 1 = (k + 1) * (e / Nat.gcd d e) ∧
    (cubicAFEDiagonalRay d e k).2 + 1 = (k + 1) * (d / Nat.gcd d e) := by
  obtain ⟨hr, hs⟩ := residual_moduli_pos hd he
  have hkr := Nat.mul_pos (Nat.succ_pos k) hr
  have hks := Nat.mul_pos (Nat.succ_pos k) hs
  exact ⟨Nat.sub_add_cancel hks, Nat.sub_add_cancel hkr⟩

theorem cubicAFEDiagonalRay_mem {d e : ℕ} (hd : 0 < d) (he : 0 < e) (k : ℕ) :
    cubicAFEDiagonalRay d e k ∈ cubicAFEDiagonal d e := by
  obtain ⟨hs, hr⟩ := cubicAFEDiagonalRay_succ hd he k
  apply (diagonal_eq_iff_exists_scale hd he).mpr
  exact ⟨k + 1, hr, hs⟩

theorem cubicAFEDiagonalRay_injective {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    Function.Injective (cubicAFEDiagonalRay d e) := by
  intro k l h
  have hs := (residual_moduli_pos hd he).2
  have hc := congrArg (fun p : ℕ × ℕ ↦ p.1 + 1) h
  rw [(cubicAFEDiagonalRay_succ hd he k).1,
    (cubicAFEDiagonalRay_succ hd he l).1] at hc
  have hkl := Nat.mul_right_cancel hs hc
  omega

theorem cubicAFEDiagonalRay_surjective {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    ∀ p ∈ cubicAFEDiagonal d e, ∃ k : ℕ, cubicAFEDiagonalRay d e k = p := by
  intro p hp
  obtain ⟨l, hlr, hls⟩ := (diagonal_eq_iff_exists_scale hd he).mp hp
  have hl : 0 < l := by
    by_contra h
    have hz : l = 0 := by omega
    simp [hz] at hlr
  refine ⟨l - 1, ?_⟩
  have hl1 : l - 1 + 1 = l := by omega
  apply Prod.ext
  · change (l - 1 + 1) * (e / Nat.gcd d e) - 1 = p.1
    rw [hl1, ← hls]
    omega
  · change (l - 1 + 1) * (d / Nat.gcd d e) - 1 = p.2
    rw [hl1, ← hlr]
    omega

/-- A genuine bijective reindexing.  This equality does not assume either
side summable; their convergence status agrees under the same bijection. -/
theorem tsum_cubicAFEDiagonal_eq_ray {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (f : ℕ × ℕ → ℂ) :
    (∑' p : cubicAFEDiagonal d e, f p) =
      ∑' k : ℕ, f (cubicAFEDiagonalRay d e k) := by
  let r : ℕ → cubicAFEDiagonal d e :=
    fun k ↦ ⟨cubicAFEDiagonalRay d e k, cubicAFEDiagonalRay_mem hd he k⟩
  have hr : Function.Bijective r := by
    constructor
    · intro k l h
      exact cubicAFEDiagonalRay_injective hd he (congrArg Subtype.val h)
    · intro p
      obtain ⟨k, hk⟩ := cubicAFEDiagonalRay_surjective hd he p.val p.property
      exact ⟨k, Subtype.ext hk⟩
  exact ((Equiv.ofBijective r hr).tsum_eq (fun p ↦ f p.val)).symm

theorem cubicAFEPositiveIndexProduct_diagonalRay {d e : ℕ}
    (hd : 0 < d) (he : 0 < e) (k : ℕ) :
    cubicAFEPositiveIndexProduct (cubicAFEDiagonalRay d e k) =
      (k + 1) ^ 2 * (d / Nat.gcd d e) * (e / Nat.gcd d e) := by
  unfold cubicAFEPositiveIndexProduct
  rw [(cubicAFEDiagonalRay_succ hd he k).1,
    (cubicAFEDiagonalRay_succ hd he k).2]
  ring

/-- Complete phase-free integrand on the reindexed diagonal, with both
signed mollifier coefficients, the factor two, and the product Mellin weight. -/
theorem cubicAFECombinedSummandFinite_diagonalRay
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ}
    (hd : 0 < d) (he : 0 < e) (t : ℝ) (k : ℕ) :
    cubicAFECombinedSummandFinite W T X V d e t (cubicAFEDiagonalRay d e k) =
      (cubicMollifierCoefficient T d : ℂ) *
        (cubicMollifierCoefficient T e : ℂ) * 2 *
        (((Real.sqrt (((k + 1) ^ 2 * (d / Nat.gcd d e) *
          (e / Nat.gcd d e) : ℕ) : ℝ)) : ℂ)⁻¹ *
          ((Real.sqrt (d * e) : ℝ) : ℂ)⁻¹ *
          cubicAFEProductWeightFinite t X V
            ((k + 1) ^ 2 * (d / Nat.gcd d e) * (e / Nat.gcd d e))) *
        (W (t / T) : ℂ) := by
  rw [cubicAFECombinedSummandFinite_eq_on_diagonal W T X V hd he t
    (cubicAFEDiagonalRay d e k) (cubicAFEDiagonalRay_mem hd he k),
    cubicAFEPositiveIndexProduct_diagonalRay hd he k]

/-- The diagonal contribution, defined using the actual integrated summands. -/
noncomputable def cubicAFEDiagonalMomentFinite
    (W : CubicTestWeight) (T X V : ℝ) : ℂ :=
  ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
    ∑' p : cubicAFEDiagonal d e, ∫ t : ℝ,
      cubicAFECombinedSummandFinite W T X V d e t p

/-- All nonzero shifts, still with the exact finite-height physical kernel. -/
noncomputable def cubicAFEOffDiagonalMomentFinite
    (W : CubicTestWeight) (T X V : ℝ) : ℂ :=
  ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
    ∑' p : ↑((cubicAFEDiagonal d e)ᶜ), ∫ t : ℝ,
      cubicAFECombinedSummandFinite W T X V d e t p

/-- Both integrated subseries are summable; the split is not an operation
on formal, potentially divergent sums. -/
theorem summable_integral_cubicAFE_diagonal_and_offDiagonal
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) :
    Summable (fun p : cubicAFEDiagonal d e ↦ ∫ t : ℝ,
      cubicAFECombinedSummandFinite W T X V d e t p) ∧
    Summable (fun p : ↑((cubicAFEDiagonal d e)ᶜ) ↦ ∫ t : ℝ,
      cubicAFECombinedSummandFinite W T X V d e t p) := by
  have h := (hasSum_integral_cubicAFECombinedSummandFinite W hT hX V hd he).summable
  exact ⟨h.subtype _, h.subtype _⟩

theorem cubicAFEMollifiedMomentFinite_eq_diagonal_add_offDiagonal
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) :
    cubicAFEMollifiedMomentFinite W T X V =
      cubicAFEDiagonalMomentFinite W T X V +
        cubicAFEOffDiagonalMomentFinite W T X V := by
  rw [cubicAFEMollifiedMomentFinite_eq_tripleIntegral W hT hX V]
  unfold cubicAFEDiagonalMomentFinite cubicAFEOffDiagonalMomentFinite
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have hd0 : d ≠ 0 := by
    have h := (Finset.mem_Icc.mp hd).1
    omega
  have he0 : e ≠ 0 := by
    have h := (Finset.mem_Icc.mp he).1
    omega
  have hsumm := (hasSum_integral_cubicAFECombinedSummandFinite W hT hX V hd0 he0).summable
  exact (hsumm.tsum_subtype_add_tsum_subtype_compl (cubicAFEDiagonal d e)).symm

theorem cubicAFEDiagonalMomentFinite_eq_ray (W : CubicTestWeight) (T X V : ℝ) :
    cubicAFEDiagonalMomentFinite W T X V =
      ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
        ∑' k : ℕ, ∫ t : ℝ,
          cubicAFECombinedSummandFinite W T X V d e t (cubicAFEDiagonalRay d e k) := by
  unfold cubicAFEDiagonalMomentFinite
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
  have hepos : 0 < e := (Finset.mem_Icc.mp he).1
  exact tsum_cubicAFEDiagonal_eq_ray hdpos hepos
    (fun p ↦ ∫ t : ℝ, cubicAFECombinedSummandFinite W T X V d e t p)

/-- Only the recombined expression is taken to infinite height here. -/
theorem tendsto_cubicAFEDiagonal_add_offDiagonal
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) :
    Tendsto (fun V : ℝ ↦ cubicAFEDiagonalMomentFinite W T X V +
      cubicAFEOffDiagonalMomentFinite W T X V)
      atTop (nhds (cubicMollifiedSecondMoment W T : ℂ)) := by
  apply (tendsto_cubicAFEMollifiedMomentFinite W hT hX).congr'
  exact Eventually.of_forall (fun V ↦
    cubicAFEMollifiedMomentFinite_eq_diagonal_add_offDiagonal W hT hX V)

end PrimeNumberTheorem.MWKFCubic
