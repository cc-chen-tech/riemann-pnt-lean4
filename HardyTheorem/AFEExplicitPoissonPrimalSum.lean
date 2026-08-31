import HardyTheorem.AFEExplicitPoissonIdentity

/-! The primal Dirichlet finite sum for the exact width-one Poisson cutoff. -/

open Complex

namespace HardyTheorem.AFE

private theorem int_Icc_cpow_sum_eq_nat (s : ℂ) (a b : ℕ) :
    (∑ n ∈ Finset.Icc (a : ℤ) b, (n : ℂ) ^ (-s)) =
      ∑ n ∈ Finset.Icc a b, (n : ℂ) ^ (-s) := by
  symm
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ℤ))
  · intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨ha, hb⟩
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩
  · intro n hn m hm h
    exact_mod_cast h
  · intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨ha, hb⟩
    have hn0 : 0 ≤ n := (Int.natCast_nonneg a).trans ha
    refine ⟨n.toNat, Finset.mem_Icc.mpr ⟨?_, ?_⟩, Int.toNat_of_nonneg hn0⟩
    · exact_mod_cast (show (a : ℤ) ≤ (n.toNat : ℤ) by
        rw [Int.toNat_of_nonneg hn0]; exact ha)
    · exact_mod_cast (show (n.toNat : ℤ) ≤ (b : ℤ) by
        rw [Int.toNat_of_nonneg hn0]; exact hb)
  · intro n hn
    simp

private theorem nat_Icc_sum_sub_eq {K N : ℕ} (hK : 1 ≤ K) (hN : K + 1 ≤ N)
    (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, f n) - (∑ n ∈ Finset.Icc 1 K, f n) =
      ∑ n ∈ Finset.Icc (K + 1) N, f n := by
  have hsplit : Finset.Icc 1 N = Finset.Icc 1 K ∪ Finset.Icc (K + 1) N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 K) (Finset.Icc (K + 1) N) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    simp only [Finset.mem_Icc] at hn hm
    omega
  rw [hsplit, Finset.sum_union hdisj]
  ring

/-- No Fourier identity is assumed: Schwartz Poisson summation and the exact
integer support of the width-one transitions yield the actual primal sum. -/
theorem dirichlet_sum_sub_eq_explicitPoisson_tsum
    (sigma t : ℝ) {K N : ℕ} (hK : 1 ≤ K) (hN : K + 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((sigma : ℂ) + I * t))) -
        (∑ n ∈ Finset.Icc 1 K, (n : ℂ) ^ (-((sigma : ℂ) + I * t))) =
      ∑' k : ℤ, explicitPoissonMode sigma ((K : ℝ) + 1) N t k := by
  let s : ℂ := (sigma : ℂ) + I * t
  rw [nat_Icc_sum_sub_eq hK hN]
  have hx : 1 < ((K + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < K + 1 by omega)
  have hxN : ((K + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
  calc
    _ = ∑ n ∈ Finset.Icc ((K + 1 : ℕ) : ℤ) N, (n : ℂ) ^ (-s) :=
      (int_Icc_cpow_sum_eq_nat s (K + 1) N).symm
    _ = ∑' k : ℤ, explicitWeightedPoissonCutoff s (K + 1 : ℕ) N k :=
      (explicitWeightedPoissonCutoff_tsum_eq_core s (by omega) hN).symm
    _ = _ := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        explicitWeightedPoissonCutoff_tsum_eq_mode_tsum sigma t hx hxN

/-- The pole subtraction commutes with the primal finite-sum identity.  This
is valid algebraically even at `s = 1`; analytic use will exclude that case. -/
theorem dirichlet_sum_sub_pole_eq_explicitPoisson_tsum
    (sigma t : ℝ) {K N : ℕ} (hK : 1 ≤ K) (hN : K + 1 ≤ N) :
    let s : ℂ := (sigma : ℂ) + I * t
    ((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - (N : ℂ) ^ (1 - s) / (1 - s)) -
        (∑ n ∈ Finset.Icc 1 K, (n : ℂ) ^ (-s)) =
      (∑' k : ℤ, explicitPoissonMode sigma ((K : ℝ) + 1) N t k) -
        (N : ℂ) ^ (1 - s) / (1 - s) := by
  dsimp only
  rw [sub_right_comm, dirichlet_sum_sub_eq_explicitPoisson_tsum sigma t hK hN]

end HardyTheorem.AFE
