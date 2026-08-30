import PrimeNumberTheorem.MWKFCubicAFECompletedPoisson

open Set Filter
open scoped Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Finite support of all added lower-scale boxes

For fixed J,d,e,delta put B=|delta|+r+s+1. In a nonzero lower box,
both real indices are at most B. Thus any L with 2*2^J*B < 2^L
contains every nonzero lower box in [0,L)^2. This is a geometric
finite-support bound, not a uniform analytic estimate as J tends to infinity.
-/

private theorem reduced_indices_one_le {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    (1 : ℝ) ≤ ((d / Nat.gcd d e : ℕ) : ℝ) ∧
      (1 : ℝ) ≤ ((e / Nat.gcd d e : ℕ) : ℝ) := by
  have hq := Nat.gcd_pos_of_pos_left e hd
  have hg := gcd_extraction hq.ne'
  have hr : 0 < d / Nat.gcd d e := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hh := hg.1
    rw [hz, mul_zero] at hh
    exact hd.ne' hh
  have hs : 0 < e / Nat.gcd d e := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hh := hg.2.1
    rw [hz, mul_zero] at hh
    exact he.ne' hh
  exact ⟨by exact_mod_cast hr, by exact_mod_cast hs⟩

noncomputable def cubicAFECompletedBoundarySize (d e : ℕ) (δ : ℤ) : ℝ :=
  |(δ : ℝ)| + ((d / Nat.gcd d e : ℕ) : ℝ) + ((e / Nat.gcd d e : ℕ) : ℝ) + 1

private theorem lower_scale_real_indices_le {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    {δ : ℤ} {J j k : ℕ} {x : ℝ} (hjk : j < J ∨ k < J)
    (hx : cubicAFEProgressionCompletedCutoff (d := d) he δ J j k x ≠ 0) :
    x ≤ cubicAFECompletedBoundarySize d e δ ∧
      cubicAFEProgressionRealSecond d e δ x ≤ cubicAFECompletedBoundarySize d e δ := by
  let r : ℝ := ((d / Nat.gcd d e : ℕ) : ℝ)
  let s : ℝ := ((e / Nat.gcd d e : ℕ) : ℝ)
  let y := cubicAFEProgressionRealSecond d e δ x
  have hr : 1 ≤ r := (reduced_indices_one_le hd he).1
  have hs : 1 ≤ s := (reduced_indices_one_le hd he).2
  have hspos : 0 < s := by linarith
  have hdom := (cubicAFEProgressionCompletedCutoff (d := d) he δ J j k).support_subset
    (subset_tsupport _ hx)
  have hxpos : 0 < x := hdom.1
  have hypos : 0 < y := div_pos hdom.2 hspos
  have hrel : s * y = (δ : ℝ) + x * r := by
    change s * (((δ : ℝ) + x * r) / s) = _
    exact mul_div_cancel₀ _ hspos.ne'
  have hb := tsupport_cubicAFEProgressionCompletedCutoff_subset he δ J j k (subset_tsupport _ hx)
  have hp : (0 : ℝ) < 2^J := by positivity
  have ha : (δ : ℝ) ≤ |(δ : ℝ)| := le_abs_self _
  have hna : -(δ : ℝ) ≤ |(δ : ℝ)| := neg_le_abs _
  change x ≤ |(δ : ℝ)| + r + s + 1 ∧ y ≤ |(δ : ℝ)| + r + s + 1
  rcases hjk with hj | hk
  · have hpow : 2 * (2 : ℝ)^j ≤ 2^J := by
      simpa only [pow_succ, mul_comm] using
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj)
    have hx1 : x ≤ 1 := hb.1.2.trans ((div_le_one hp).mpr hpow)
    have hy : y ≤ |(δ : ℝ)| + r := by nlinarith
    constructor <;> linarith [abs_nonneg (δ : ℝ)]
  · have hpow : 2 * (2 : ℝ)^k ≤ 2^J := by
      simpa only [pow_succ, mul_comm] using
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk)
    have hy1 : y ≤ 1 := hb.2.2.trans ((div_le_one hp).mpr hpow)
    have hxx : x ≤ |(δ : ℝ)| + s := by nlinarith
    constructor <;> linarith [abs_nonneg (δ : ℝ)]

theorem cubicAFECompletedLowerScale_index_bound {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    {δ : ℤ} {J j k L : ℕ}
    (hL : 2 * (2 : ℝ)^J * cubicAFECompletedBoundarySize d e δ < (2 : ℝ)^L)
    (hjk : j < J ∨ k < J) {x : ℝ}
    (hx : cubicAFEProgressionCompletedCutoff (d := d) he δ J j k x ≠ 0) : j < L ∧ k < L := by
  have hb := tsupport_cubicAFEProgressionCompletedCutoff_subset he δ J j k (subset_tsupport _ hx)
  have hu := lower_scale_real_indices_le hd he hjk hx
  have hp : (0 : ℝ) < 2^J := by positivity
  have hjbound : (2 : ℝ)^j ≤ 2 * 2^J * cubicAFECompletedBoundarySize d e δ := by
    have hh := (div_le_iff₀ hp).mp hb.1.1
    have hmul := mul_le_mul_of_nonneg_left hu.1 hp.le
    nlinarith
  have hkbound : (2 : ℝ)^k ≤ 2 * 2^J * cubicAFECompletedBoundarySize d e δ := by
    have hh := (div_le_iff₀ hp).mp hb.2.1
    have hmul := mul_le_mul_of_nonneg_left hu.2 hp.le
    nlinarith
  constructor
  · by_contra h
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (le_of_not_gt h)
    exact (not_lt_of_ge (hh.trans hjbound)) hL
  · by_contra h
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (le_of_not_gt h)
    exact (not_lt_of_ge (hh.trans hkbound)) hL

theorem exists_cubicAFECompletedLowerScale_bound (d e : ℕ) (δ : ℤ) (J : ℕ) :
    ∃ L : ℕ, 2 * (2 : ℝ)^J * cubicAFECompletedBoundarySize d e δ < (2 : ℝ)^L := by
  exact ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually
    (eventually_gt_atTop (2 * (2 : ℝ)^J * cubicAFECompletedBoundarySize d e δ))).exists

def cubicAFECompletedLowerScaleBoxes (J L : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range L) ×ˢ (Finset.range L)).filter (fun jk ↦ jk.1 < J ∨ jk.2 < J)

theorem cubicAFEProgressionCompletedCutoff_zero_outside_lowerBoxes
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) {δ : ℤ} {J L : ℕ}
    (hL : 2 * (2 : ℝ)^J * cubicAFECompletedBoundarySize d e δ < (2 : ℝ)^L)
    {jk : ℕ × ℕ} (hjk : jk.1 < J ∨ jk.2 < J)
    (hout : jk ∉ cubicAFECompletedLowerScaleBoxes J L) (x : ℝ) :
    cubicAFEProgressionCompletedCutoff (d := d) he δ J jk.1 jk.2 x = 0 := by
  by_contra hx
  have hb := cubicAFECompletedLowerScale_index_bound hd he hL hjk hx
  apply hout
  simpa only [cubicAFECompletedLowerScaleBoxes, Finset.mem_filter,
    Finset.mem_product, Finset.mem_range] using ⟨hb, hjk⟩

end PrimeNumberTheorem.MWKFCubic
