import PrimeNumberTheorem.MWKFCubicAFEDyadicCompletion

open Set
open scoped ContDiff

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Actual dyadic cutoffs including finitely many lower scales

The completed scales are `2^(j-J)` and `2^(k-J)`, with natural j,k,J.
The old boxes embed by adding J to both indices. Every additional box
vanishes on the entire positive integer progression; it need not vanish
on the positive real domain. No integral limit in J is asserted.
-/

theorem cubicAFEDyadicWindow_shift (J j : ℕ) (x : ℝ) :
    cubicAFEDyadicWindow (J + j) ((2 : ℝ)^J * x) = cubicAFEDyadicWindow j x := by
  unfold cubicAFEDyadicWindow
  rw [pow_add]
  have hp : (2 : ℝ)^J ≠ 0 := by positivity
  have h1 : (2 : ℝ)^J * x / (2^J * 2^j) = x / 2^j := by field_simp
  have h2 : 2 * ((2 : ℝ)^J * x) / (2^J * 2^j) = 2 * x / 2^j := by field_simp
  rw [h1, h2]

theorem cubicAFEDyadicWindow_zero_of_lower_scale {j J : ℕ} (hj : j < J)
    {x : ℝ} (hx : 1 ≤ x) : cubicAFEDyadicWindow j ((2 : ℝ)^J * x) = 0 := by
  apply cubicAFEDyadicWindow_zero_of_two_mul_le
  have hp : (2 : ℝ)^(j + 1) ≤ 2^J := pow_le_pow_right₀ (by norm_num) hj
  rw [pow_succ, mul_comm] at hp
  exact hp.trans (le_mul_of_one_le_right (by positivity) hx)

private theorem completed_support_bound (d e : ℕ) (δ : ℤ) (J j k : ℕ) :
    tsupport (fun x : ℝ ↦ cubicAFEDyadicWindow j ((2 : ℝ)^J * x) *
      cubicAFEDyadicWindow k ((2 : ℝ)^J * cubicAFEProgressionRealSecond d e δ x)) ⊆
    {x : ℝ | (2 : ℝ)^J * x ∈ Icc ((2 : ℝ)^j / 2) (2 * (2 : ℝ)^j) ∧
      (2 : ℝ)^J * cubicAFEProgressionRealSecond d e δ x ∈
        Icc ((2 : ℝ)^k / 2) (2 * (2 : ℝ)^k)} := by
  have hc1 : Continuous (fun x : ℝ ↦ (2 : ℝ)^J * x) := by fun_prop
  have hc2 : Continuous (fun x : ℝ ↦
      (2 : ℝ)^J * cubicAFEProgressionRealSecond d e δ x) := by
    unfold cubicAFEProgressionRealSecond
    fun_prop
  apply closure_minimal _ ((isClosed_Icc.preimage hc1).inter (isClosed_Icc.preimage hc2))
  intro x hx
  have hh := mul_ne_zero_iff.mp hx
  exact ⟨tsupport_cubicAFEDyadicWindow_subset j (subset_tsupport _ hh.1),
    tsupport_cubicAFEDyadicWindow_subset k (subset_tsupport _ hh.2)⟩

private theorem reduced_second_pos {d e : ℕ} (he : 0 < e) :
    (0 : ℝ) < ((e / Nat.gcd d e : ℕ) : ℝ) := by
  have hq : 0 < Nat.gcd d e := by simpa only [Nat.gcd_comm] using Nat.gcd_pos_of_pos_left d he
  have hs : 0 < e / Nat.gcd d e := by
    apply Nat.pos_of_ne_zero
    intro hz
    have heq := (gcd_extraction hq.ne').2.1
    rw [hz, mul_zero] at heq
    exact he.ne' heq
  exact_mod_cast hs

noncomputable def cubicAFEProgressionCompletedCutoff {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (J j k : ℕ) : CubicProgressionCutoff d e δ where
  toFun x := cubicAFEDyadicWindow j ((2 : ℝ)^J * x) *
    cubicAFEDyadicWindow k ((2 : ℝ)^J * cubicAFEProgressionRealSecond d e δ x)
  smooth := ((contDiff_cubicAFEDyadicWindow j).comp (by fun_prop)).mul
    ((contDiff_cubicAFEDyadicWindow k).comp (by unfold cubicAFEProgressionRealSecond; fun_prop))
  compact := by
    have hc : HasCompactSupport (fun x : ℝ ↦ cubicAFEDyadicWindow j ((2 : ℝ)^J * x)) := by
      simpa only [smul_eq_mul] using
        (hasCompactSupport_cubicAFEDyadicWindow j).comp_smul (by positivity : (2 : ℝ)^J ≠ 0)
    exact hc.mul_right
  support_subset := by
    intro x hx
    have hb := completed_support_bound d e δ J j k hx
    have hp : (0 : ℝ) < 2^J := by positivity
    have hxpos : 0 < x := (mul_pos_iff_of_pos_left hp).mp
      ((by positivity : (0 : ℝ) < 2^j / 2).trans_le hb.1.1)
    have hypos : 0 < cubicAFEProgressionRealSecond d e δ x :=
      (mul_pos_iff_of_pos_left hp).mp
        ((by positivity : (0 : ℝ) < 2^k / 2).trans_le hb.2.1)
    exact ⟨hxpos, (div_pos_iff_of_pos_right (reduced_second_pos (d := d) he)).mp hypos⟩

/-- Both physical scales, including their endpoint constants, on closed support. -/
theorem tsupport_cubicAFEProgressionCompletedCutoff_subset {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (J j k : ℕ) :
    tsupport (cubicAFEProgressionCompletedCutoff (d := d) he δ J j k).toFun ⊆
      {x : ℝ | x ∈ Icc (((2 : ℝ)^j / 2) / 2^J) ((2 * (2 : ℝ)^j) / 2^J) ∧
        cubicAFEProgressionRealSecond d e δ x ∈
          Icc (((2 : ℝ)^k / 2) / 2^J) ((2 * (2 : ℝ)^k) / 2^J)} := by
  intro x hx
  have hb := completed_support_bound d e δ J j k hx
  have hp : (0 : ℝ) < 2^J := by positivity
  constructor
  · exact ⟨(div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hb.1.1),
      (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hb.1.2)⟩
  · exact ⟨(div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hb.2.1),
      (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hb.2.2)⟩

theorem cubicAFEProgressionCompletedCutoff_shift {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (J j k : ℕ) (x : ℝ) :
    cubicAFEProgressionCompletedCutoff (d := d) he δ J (J + j) (J + k) x =
      cubicAFEProgressionDyadicCutoff (d := d) he δ j k x := by
  change cubicAFEDyadicWindow (J + j) ((2 : ℝ)^J * x) *
    cubicAFEDyadicWindow (J + k) ((2 : ℝ)^J * cubicAFEProgressionRealSecond d e δ x) = _
  simp only [cubicAFEDyadicWindow_shift]
  rfl

private theorem progression_second_one_le {d e : ℕ} (he : 0 < e)
    {δ : ℤ} {m : ℕ} (hm : m ∈ cubicAFEProgression d e δ) :
    1 ≤ cubicAFEProgressionRealSecond d e δ m := by
  change 1 ≤ ((δ : ℝ) + (m : ℝ) * ((d / Nat.gcd d e : ℕ) : ℝ)) /
    ((e / Nat.gcd d e : ℕ) : ℝ)
  rw [← cubicAFEProgressionPair_second_cast he hm]
  exact_mod_cast Nat.succ_pos (cubicAFEProgressionPair d e δ m).2

theorem hasSum_cubicAFEProgressionCompletedCutoff {d e : ℕ} (he : 0 < e)
    {δ : ℤ} {m : ℕ} (hm : m ∈ cubicAFEProgression d e δ) (J : ℕ) :
    HasSum (fun jk : ℕ × ℕ ↦ cubicAFEProgressionCompletedCutoff (d := d) he δ J jk.1 jk.2 m) 1 := by
  have hx : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
  have hs := hasSum_cubicAFEDyadicCompletionWeight J m (cubicAFEProgressionRealSecond d e δ m)
  rw [cubicAFEDyadicCompletionWeight_eq_one_of_one_le J hx (progression_second_one_le he hm)] at hs
  exact hs

theorem cubicAFEProgressionCompletedCutoff_zero_on_progression {d e : ℕ} (he : 0 < e)
    {δ : ℤ} {m : ℕ} (hm : m ∈ cubicAFEProgression d e δ) {J j k : ℕ}
    (hjk : j < J ∨ k < J) : cubicAFEProgressionCompletedCutoff (d := d) he δ J j k m = 0 := by
  change cubicAFEDyadicWindow j ((2 : ℝ)^J * (m : ℝ)) *
    cubicAFEDyadicWindow k ((2 : ℝ)^J * cubicAFEProgressionRealSecond d e δ m) = 0
  rcases hjk with hj | hk
  · rw [cubicAFEDyadicWindow_zero_of_lower_scale hj (by exact_mod_cast hm.1), zero_mul]
  · rw [cubicAFEDyadicWindow_zero_of_lower_scale hk (progression_second_one_le he hm), mul_zero]

end PrimeNumberTheorem.MWKFCubic
