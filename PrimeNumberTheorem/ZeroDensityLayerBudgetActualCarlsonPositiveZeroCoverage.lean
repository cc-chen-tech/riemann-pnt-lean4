import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonPositiveZeroTail

/-!
# Coverage of actual positive zeta zeros by Carlson shells

The Carlson index was built from a finite base range and dyadic height shells.
This file proves that the construction really covers every positive
nontrivial zeta zero to the right of the fixed strip boundary.
-/

namespace PrimeNumberTheorem

open scoped BigOperators Topology
open Filter Complex

noncomputable section

theorem exists_dyadic_shell_of_one_lt {t : ℝ} (ht : 1 < t) :
    ∃ n : ℕ, (2 : ℝ) ^ n < t ∧ t ≤ (2 : ℝ) ^ (n + 1) := by
  have hpow :
      Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hexists : ∃ k : ℕ, t ≤ (2 : ℝ) ^ k :=
    (hpow.eventually (eventually_ge_atTop t)).exists
  let k := Nat.find hexists
  have hkspec : t ≤ (2 : ℝ) ^ k := by
    change t ≤ (2 : ℝ) ^ Nat.find hexists
    exact Nat.find_spec hexists
  have hkne : k ≠ 0 := by
    intro hk
    have htone : t ≤ 1 := by simpa [hk] using hkspec
    linarith
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hkne
  have hnfind : n < Nat.find hexists := by
    change n < k
    rw [hn]
    exact Nat.lt_succ_self n
  have hnnot : ¬t ≤ (2 : ℝ) ^ n :=
    Nat.find_min hexists hnfind
  refine ⟨n, lt_of_not_ge hnnot, ?_⟩
  simpa [hn, Nat.succ_eq_add_one] using hkspec

/-- The actual high-strip positive zeta zeros, without a height truncation. -/
def ActualCarlsonHighPositiveZero (sigma : ℝ) :=
  {rho : ℂ //
    RiemannHypothesis.IsNontrivialZero rho ∧
      0 < rho.im ∧ sigma < rho.re}

theorem exists_actualCarlsonPositiveZeroIndex {sigma : ℝ}
    (rho : ActualCarlsonHighPositiveZero sigma) :
    ∃ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZero index = rho.1 := by
  rcases rho.property with ⟨hz, him, hre⟩
  by_cases hbase : rho.1.im ≤ 1
  · refine ⟨Sum.inl ⟨rho.1,
      ZeroDensity.mem_zeroDensityZerosFinset.mpr
        ⟨hz, him, hbase, hre⟩⟩, rfl⟩
  · obtain ⟨n, hnlow, hnupper⟩ :=
      exists_dyadic_shell_of_one_lt (lt_of_not_ge hbase)
    have hshell : rho.1 ∈ actualCarlsonDyadicZeroShell sigma n := by
      apply Finset.mem_sdiff.mpr
      constructor
      · exact ZeroDensity.mem_zeroDensityZerosFinset.mpr
          ⟨hz, him, hnupper, hre⟩
      · intro hlower
        have himle :
            rho.1.im ≤ (2 : ℝ) ^ n :=
          (ZeroDensity.mem_zeroDensityZerosFinset.mp hlower).2.2.1
        linarith
    exact ⟨Sum.inr ⟨n, ⟨rho.1, hshell⟩⟩, rfl⟩

/-- A chosen Carlson-shell index for an actual high-strip positive zero. -/
def actualCarlsonPositiveZeroIndexOf {sigma : ℝ}
    (rho : ActualCarlsonHighPositiveZero sigma) :
    ActualCarlsonPositiveZeroIndex sigma :=
  Classical.choose (exists_actualCarlsonPositiveZeroIndex rho)

theorem actualCarlsonPositiveZero_indexOf {sigma : ℝ}
    (rho : ActualCarlsonHighPositiveZero sigma) :
    actualCarlsonPositiveZero (actualCarlsonPositiveZeroIndexOf rho) =
      rho.1 :=
  Classical.choose_spec (exists_actualCarlsonPositiveZeroIndex rho)

theorem actualCarlsonPositiveZeroIndexOf_injective {sigma : ℝ} :
    Function.Injective
      (@actualCarlsonPositiveZeroIndexOf sigma) := by
  intro rho₁ rho₂ heq
  apply Subtype.ext
  rw [← actualCarlsonPositiveZero_indexOf rho₁,
    ← actualCarlsonPositiveZero_indexOf rho₂, heq]

end

end PrimeNumberTheorem
