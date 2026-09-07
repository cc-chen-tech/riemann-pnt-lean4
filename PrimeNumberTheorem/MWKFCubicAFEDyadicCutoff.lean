import PrimeNumberTheorem.MWKFCubicAFEProgressionPoisson
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Normed.Ring.InfiniteSum

open Set Filter
open scoped ContDiff Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Actual dyadic cutoffs for both positive indices

The window is a difference of two explicit smooth lowpasses. Its closed
support lies in `[2^j/2, 2*2^j]`, and the nonnegative windows sum to one at every
real `x >= 1`. Applying them to `x` and the exact second index produces
admissible compact cutoffs of the physical progression, including negative
shifts. No partition-of-unity or cutoff-existence hypothesis is assumed.
-/

noncomputable def cubicAFEDyadicWindow (j : ℕ) (x : ℝ) : ℝ :=
  Real.smoothTransition (2 - x / (2 : ℝ)^j) -
    Real.smoothTransition (2 - 2 * x / (2 : ℝ)^j)

theorem contDiff_cubicAFEDyadicWindow (j : ℕ) :
    ContDiff ℝ ∞ (cubicAFEDyadicWindow j) := by
  unfold cubicAFEDyadicWindow
  fun_prop

theorem cubicAFEDyadicWindow_zero_of_le_half (j : ℕ) {x : ℝ}
    (hx : x ≤ (2 : ℝ)^j / 2) : cubicAFEDyadicWindow j x = 0 := by
  have hp : (0 : ℝ) < 2^j := pow_pos (by norm_num) _
  have h1 : x / (2 : ℝ)^j ≤ 1 := (div_le_one hp).mpr (by linarith)
  have h2 : 2 * x / (2 : ℝ)^j ≤ 1 := (div_le_one hp).mpr (by linarith)
  simp only [cubicAFEDyadicWindow,
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 - x / (2 : ℝ)^j),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 - 2 * x / (2 : ℝ)^j),
    sub_self]

theorem cubicAFEDyadicWindow_zero_of_two_mul_le (j : ℕ) {x : ℝ}
    (hx : 2 * (2 : ℝ)^j ≤ x) : cubicAFEDyadicWindow j x = 0 := by
  have hp : (0 : ℝ) < 2^j := pow_pos (by norm_num) _
  have h1 : 2 ≤ x / (2 : ℝ)^j := (le_div_iff₀ hp).mpr hx
  have h2 : 2 ≤ 2 * x / (2 : ℝ)^j := (le_div_iff₀ hp).mpr (by linarith)
  simp only [cubicAFEDyadicWindow,
    Real.smoothTransition.zero_of_nonpos (by linarith : 2 - x / (2 : ℝ)^j ≤ 0),
    Real.smoothTransition.zero_of_nonpos (by linarith : 2 - 2 * x / (2 : ℝ)^j ≤ 0),
    sub_self]

theorem cubicAFEDyadicWindow_nonneg (j : ℕ) (x : ℝ) : 0 ≤ cubicAFEDyadicWindow j x := by
  by_cases hx : x ≤ 0
  · rw [cubicAFEDyadicWindow_zero_of_le_half j (hx.trans (by positivity))]
  · apply sub_nonneg.mpr
    apply Real.smoothTransition.monotone
    have hp : (0 : ℝ) < 2^j := pow_pos (by norm_num) _
    have hh : x / (2 : ℝ)^j ≤ 2 * x / (2 : ℝ)^j :=
      (div_le_div_iff_of_pos_right hp).mpr (by linarith)
    linarith

theorem cubicAFEDyadicWindow_le_one (j : ℕ) (x : ℝ) : cubicAFEDyadicWindow j x ≤ 1 := by
  exact sub_le_iff_le_add.mpr ((Real.smoothTransition.le_one _).trans
    (le_add_of_nonneg_right (Real.smoothTransition.nonneg _)))

theorem tsupport_cubicAFEDyadicWindow_subset (j : ℕ) :
    tsupport (cubicAFEDyadicWindow j) ⊆ Icc ((2 : ℝ)^j / 2) (2 * (2 : ℝ)^j) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra h
    exact hx (cubicAFEDyadicWindow_zero_of_le_half j (le_of_not_ge h))
  · by_contra h
    exact hx (cubicAFEDyadicWindow_zero_of_two_mul_le j (le_of_not_ge h))

theorem hasCompactSupport_cubicAFEDyadicWindow (j : ℕ) :
    HasCompactSupport (cubicAFEDyadicWindow j) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (tsupport_cubicAFEDyadicWindow_subset j)

/-- Finite telescoping identity, valid on all real inputs, with the lower
boundary term exposed rather than silently dropped. -/
theorem sum_cubicAFEDyadicWindow_range (J : ℕ) (x : ℝ) :
    (∑ j ∈ Finset.range (J + 1), cubicAFEDyadicWindow j x) =
      Real.smoothTransition (2 - x / (2 : ℝ)^J) - Real.smoothTransition (2 - 2 * x) := by
  induction J with
  | zero => simp [cubicAFEDyadicWindow]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    have hscale : 2 * x / (2 : ℝ)^(J + 1) = x / (2 : ℝ)^J := by
      rw [pow_succ]
      field_simp
    simp only [cubicAFEDyadicWindow, hscale]
    ring

/-- The actual dyadic partition for positive integer-sized real inputs. -/
theorem hasSum_cubicAFEDyadicWindow {x : ℝ} (hx : 1 ≤ x) :
    HasSum (fun j : ℕ ↦ cubicAFEDyadicWindow j x) 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun j ↦ cubicAFEDyadicWindow_nonneg j x) 1).mpr
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually
    (eventually_ge_atTop x)] with J hJ
  rw [sum_cubicAFEDyadicWindow_range]
  have hp : (0 : ℝ) < 2^J := pow_pos (by norm_num) _
  have hquot : x / (2 : ℝ)^J ≤ 1 := (div_le_one hp).mpr hJ
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith)]
  norm_num

theorem hasSum_cubicAFEDyadicWindow_product {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    HasSum (fun jk : ℕ × ℕ ↦ cubicAFEDyadicWindow jk.1 x * cubicAFEDyadicWindow jk.2 y) 1 := by
  have ha := hasSum_cubicAFEDyadicWindow hx
  have hb := hasSum_cubicAFEDyadicWindow hy
  have hsum : Summable (fun jk : ℕ × ℕ ↦
      cubicAFEDyadicWindow jk.1 x * cubicAFEDyadicWindow jk.2 y) :=
    Summable.mul_of_nonneg ha.summable hb.summable
      (fun j ↦ cubicAFEDyadicWindow_nonneg j x) (fun k ↦ cubicAFEDyadicWindow_nonneg k y)
  have hab : HasSum (fun jk : ℕ × ℕ ↦
      cubicAFEDyadicWindow jk.1 x * cubicAFEDyadicWindow jk.2 y) (1 * 1 : ℝ) :=
    HasSum.mul (f := fun j : ℕ ↦ cubicAFEDyadicWindow j x)
      (g := fun k : ℕ ↦ cubicAFEDyadicWindow k y) (s := (1 : ℝ)) (t := (1 : ℝ)) ha hb hsum
  simpa only [one_mul] using hab

private theorem reduced_second_pos {d e : ℕ} (he : 0 < e) :
    (0 : ℝ) < ((e / Nat.gcd d e : ℕ) : ℝ) := by
  have hq : 0 < Nat.gcd d e := by simpa only [Nat.gcd_comm] using Nat.gcd_pos_of_pos_left d he
  have hs : 0 < e / Nat.gcd d e := by
    have heq := (gcd_extraction hq.ne').2.1
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, mul_zero] at heq
    exact he.ne' heq
  exact_mod_cast hs

/-- Two actual dyadic scales, on the first and exact real second index. -/
noncomputable def cubicAFEProgressionDyadicCutoff {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (j k : ℕ) : CubicProgressionCutoff d e δ where
  toFun x := cubicAFEDyadicWindow j x *
    cubicAFEDyadicWindow k (cubicAFEProgressionRealSecond d e δ x)
  smooth := (contDiff_cubicAFEDyadicWindow j).mul
    ((contDiff_cubicAFEDyadicWindow k).comp (by unfold cubicAFEProgressionRealSecond; fun_prop))
  compact := (hasCompactSupport_cubicAFEDyadicWindow j).mul_right
  support_subset := by
    have hclosed : IsClosed (Icc ((2 : ℝ)^j / 2) (2 * (2 : ℝ)^j) ∩
        (cubicAFEProgressionRealSecond d e δ) ⁻¹' Icc ((2 : ℝ)^k / 2) (2 * (2 : ℝ)^k)) :=
      isClosed_Icc.inter (isClosed_Icc.preimage (by unfold cubicAFEProgressionRealSecond; fun_prop))
    have hbound : tsupport (fun x ↦ cubicAFEDyadicWindow j x *
        cubicAFEDyadicWindow k (cubicAFEProgressionRealSecond d e δ x)) ⊆
        Icc ((2 : ℝ)^j / 2) (2 * (2 : ℝ)^j) ∩
          (cubicAFEProgressionRealSecond d e δ) ⁻¹' Icc ((2 : ℝ)^k / 2) (2 * (2 : ℝ)^k) := by
      apply closure_minimal _ hclosed
      intro x hx
      have hh := mul_ne_zero_iff.mp hx
      exact ⟨tsupport_cubicAFEDyadicWindow_subset j (subset_tsupport _ hh.1),
        tsupport_cubicAFEDyadicWindow_subset k (subset_tsupport _ hh.2)⟩
    intro x hx
    have hb := hbound hx
    have hxpos : 0 < x := (by positivity : (0 : ℝ) < 2^j / 2).trans_le hb.1.1
    have hnpos : 0 < cubicAFEProgressionRealSecond d e δ x :=
      (by positivity : (0 : ℝ) < 2^k / 2).trans_le hb.2.1
    exact ⟨hxpos, (div_pos_iff_of_pos_right (reduced_second_pos (d := d) he)).mp hnpos⟩

theorem cubicAFEProgressionDyadicCutoff_eq_discrete {d e : ℕ} (he : 0 < e)
    {δ : ℤ} {m : ℕ} (hm : m ∈ cubicAFEProgression d e δ) (j k : ℕ) :
    cubicAFEProgressionDyadicCutoff (d := d) he δ j k m = cubicAFEDyadicWindow j m *
      cubicAFEDyadicWindow k ((cubicAFEProgressionPair d e δ m).2 + 1 : ℕ) := by
  change cubicAFEDyadicWindow j m * cubicAFEDyadicWindow k
    (cubicAFEProgressionRealSecond d e δ m) = _
  rw [show cubicAFEProgressionRealSecond d e δ m =
    (((cubicAFEProgressionPair d e δ m).2 + 1 : ℕ) : ℝ) from
      (cubicAFEProgressionPair_second_cast he hm).symm]

/-- Absolute summability and value one for the actual two-index partition
at every admissible progression integer. -/
theorem hasSum_cubicAFEProgressionDyadicCutoff {d e : ℕ} (he : 0 < e)
    {δ : ℤ} {m : ℕ} (hm : m ∈ cubicAFEProgression d e δ) :
    HasSum (fun jk : ℕ × ℕ ↦ cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 m) 1 := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hm.1)
  have hn1 : (1 : ℝ) ≤ (((cubicAFEProgressionPair d e δ m).2 + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.succ_pos (cubicAFEProgressionPair d e δ m).2))
  apply (hasSum_cubicAFEDyadicWindow_product hm1 hn1).congr_fun
  intro jk
  exact cubicAFEProgressionDyadicCutoff_eq_discrete he hm jk.1 jk.2

end PrimeNumberTheorem.MWKFCubic
