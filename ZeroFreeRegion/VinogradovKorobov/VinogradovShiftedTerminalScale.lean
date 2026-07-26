import ZeroFreeRegion.VinogradovKorobov.VinogradovShiftedTerminal
import Mathlib.Data.Nat.MaxPowDiv

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Positive natural representative of the shifted center difference
`xi - (eta - p^b)`. -/
def vinogradovShiftedCenterDifferenceNat
    {a : ℕ} (p b : ℕ) (z : Fin (p ^ a) × Fin (p ^ b)) : ℕ :=
  z.1.val + 1 + p ^ b - (z.2.val + 1)

theorem vinogradovShiftedCenterDifferenceNat_pos
    {a : ℕ} (p b : ℕ) (z : Fin (p ^ a) × Fin (p ^ b)) :
    0 < vinogradovShiftedCenterDifferenceNat p b z := by
  unfold vinogradovShiftedCenterDifferenceNat
  omega

theorem intCast_vinogradovShiftedCenterDifferenceNat
    {a : ℕ} (p b : ℕ) (z : Fin (p ^ a) × Fin (p ^ b)) :
    (vinogradovShiftedCenterDifferenceNat p b z : ℤ) =
      vinogradovCenterValue z.1 -
        (vinogradovCenterValue z.2 - (p : ℤ) ^ b) := by
  have hy : z.2.val + 1 ≤ p ^ b := by omega
  unfold vinogradovShiftedCenterDifferenceNat vinogradovCenterValue
  rw [Nat.cast_sub (by omega : z.2.val + 1 ≤ z.1.val + 1 + p ^ b)]
  push_cast
  ring

/-- The shifted difference is still divisible by `p^b` on the terminal
center layer. -/
theorem primePower_dvd_vinogradovShiftedCenterDifferenceNat_of_terminal
    (p a b : ℕ) [Fact p.Prime] (z : Fin (p ^ a) × Fin (p ^ b))
    (hz : z ∈ vinogradovCenterPairCongruentSet p a b b) :
    p ^ b ∣ vinogradovShiftedCenterDifferenceNat p b z := by
  have hunshifted :
      (p : ℤ) ^ b ∣
        vinogradovCenterValue z.1 - vinogradovCenterValue z.2 :=
    (primePower_dvd_vinogradovCenterDifference_iff_cast_eq
      p a b b z.1 z.2).2
        ((mem_vinogradovCenterPairCongruentSet_iff p a b b z).1 hz)
  have hshifted :
      (p : ℤ) ^ b ∣
        vinogradovCenterValue z.1 -
          (vinogradovCenterValue z.2 - (p : ℤ) ^ b) := by
    have hself : (p : ℤ) ^ b ∣ (p : ℤ) ^ b := dvd_refl _
    convert hunshifted.add hself using 1 <;> ring
  rw [← intCast_vinogradovShiftedCenterDifferenceNat p b z] at hshifted
  exact_mod_cast hshifted

/-- For `b ≤ a`, every shifted center difference lies below `p^(a+1)`.
This upper bound is uniform and does not need terminal congruence. -/
theorem vinogradovShiftedCenterDifferenceNat_lt_nextPower
    {a : ℕ} (p b : ℕ) [Fact p.Prime] (hba : b ≤ a)
    (z : Fin (p ^ a) × Fin (p ^ b)) :
    vinogradovShiftedCenterDifferenceNat p b z < p ^ (a + 1) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpow : p ^ b ≤ p ^ a := Nat.pow_le_pow_right hp hba
  calc
    vinogradovShiftedCenterDifferenceNat p b z <
        p ^ a + p ^ b := by
      unfold vinogradovShiftedCenterDifferenceNat
      omega
    _ ≤ p ^ a + p ^ a := Nat.add_le_add_left hpow _
    _ = 2 * p ^ a := by omega
    _ ≤ p * p ^ a :=
      Nat.mul_le_mul_right (p ^ a) (Fact.out : p.Prime).two_le
    _ = p ^ (a + 1) := by simp [pow_succ, Nat.mul_comm]

/-- On the terminal center layer, the shifted difference has `p`-adic order
between the old tail scale `b` and the main scale `a`. -/
theorem padicValNat_vinogradovShiftedCenterDifferenceNat_mem_Icc
    (p a b : ℕ) [Fact p.Prime] (hba : b ≤ a)
    (z : Fin (p ^ a) × Fin (p ^ b))
    (hz : z ∈ vinogradovCenterPairCongruentSet p a b b) :
    b ≤ padicValNat p (vinogradovShiftedCenterDifferenceNat p b z) ∧
      padicValNat p (vinogradovShiftedCenterDifferenceNat p b z) ≤ a := by
  let D := vinogradovShiftedCenterDifferenceNat p b z
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hDpos : 0 < D := vinogradovShiftedCenterDifferenceNat_pos p b z
  have hDne : D ≠ 0 := hDpos.ne'
  change b ≤ padicValNat p D ∧ padicValNat p D ≤ a
  have hlower :
      b ≤ padicValNat p D :=
    (Nat.pow_dvd_iff_le_padicValNat hp1.ne' hDne).1 (by
      simpa [D] using
        primePower_dvd_vinogradovShiftedCenterDifferenceNat_of_terminal
          p a b z hz)
  refine ⟨hlower, ?_⟩
  by_contra hnot
  have hnext : a + 1 ≤ padicValNat p D := by omega
  have hdvd : p ^ (a + 1) ∣ D :=
    (Nat.pow_dvd_iff_le_padicValNat hp1.ne' hDne).2 hnext
  have hle : p ^ (a + 1) ≤ D := Nat.le_of_dvd hDpos hdvd
  have hlt : D < p ^ (a + 1) :=
    vinogradovShiftedCenterDifferenceNat_lt_nextPower p b hba z
  omega

/-- Canonical exact-scale factorization of a shifted terminal center
difference. -/
theorem exists_coprime_shifted_terminal_center_factor
    (p a b : ℕ) [Fact p.Prime] (z : Fin (p ^ a) × Fin (p ^ b)) :
    ∃ omega : ℤ,
      vinogradovCenterValue z.1 -
          (vinogradovCenterValue z.2 - (p : ℤ) ^ b) =
        omega *
          (p : ℤ) ^
            padicValNat p (vinogradovShiftedCenterDifferenceNat p b z) ∧
      IsCoprime (p : ℤ) omega := by
  let D := vinogradovShiftedCenterDifferenceNat p b z
  let omegaNat := D.divMaxPow p
  refine ⟨(omegaNat : ℤ), ?_, ?_⟩
  · have hfactor :
        p ^ padicValNat p D * omegaNat = D :=
      Nat.pow_padicValNat_mul_divMaxPow p D
    have hfactor' :
        D = omegaNat * p ^ padicValNat p D := by
      simpa [Nat.mul_comm] using hfactor.symm
    rw [← intCast_vinogradovShiftedCenterDifferenceNat p b z]
    exact_mod_cast (by simpa [D] using hfactor')
  · apply ((Nat.prime_iff_prime_int.mp
      (Fact.out : p.Prime)).coprime_iff_not_dvd).2
    intro hdvd
    have hdvdNat : p ∣ omegaNat := by exact_mod_cast hdvd
    exact (Nat.not_dvd_divMaxPow
      (Fact.out : p.Prime).one_lt
      (vinogradovShiftedCenterDifferenceNat_pos p b z).ne') hdvdNat

/-- Terminal center pairs whose shifted difference has exact `p`-adic order
`gamma`. -/
noncomputable def vinogradovShiftedTerminalExactScaleSet
    (p a b gamma : ℕ) : Finset (Fin (p ^ a) × Fin (p ^ b)) := by
  classical
  exact (vinogradovCenterPairCongruentSet p a b b).filter fun z ↦
    padicValNat p (vinogradovShiftedCenterDifferenceNat p b z) = gamma

theorem mem_vinogradovShiftedTerminalExactScaleSet_iff
    (p a b gamma : ℕ) (z : Fin (p ^ a) × Fin (p ^ b)) :
    z ∈ vinogradovShiftedTerminalExactScaleSet p a b gamma ↔
      z ∈ vinogradovCenterPairCongruentSet p a b b ∧
        padicValNat p (vinogradovShiftedCenterDifferenceNat p b z) =
          gamma := by
  classical
  simp [vinogradovShiftedTerminalExactScaleSet]

/-- The terminal layer is the disjoint sum of its shifted exact scales
`b ≤ gamma ≤ a`. -/
theorem sum_vinogradovCenterPairCongruentSet_eq_shiftedTerminalExactScales
    {M : Type*} [AddCommMonoid M]
    (p a b : ℕ) [Fact p.Prime] (hba : b ≤ a)
    (f : (Fin (p ^ a) × Fin (p ^ b)) → M) :
    (∑ z ∈ vinogradovCenterPairCongruentSet p a b b, f z) =
      ∑ gamma ∈ Finset.Icc b a,
        ∑ z ∈ vinogradovShiftedTerminalExactScaleSet p a b gamma, f z := by
  classical
  have hmaps :
      ∀ z ∈ vinogradovCenterPairCongruentSet p a b b,
        padicValNat p (vinogradovShiftedCenterDifferenceNat p b z) ∈
          Finset.Icc b a := by
    intro z hz
    exact Finset.mem_Icc.2
      (padicValNat_vinogradovShiftedCenterDifferenceNat_mem_Icc
        p a b hba z hz)
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to hmaps f
  simpa only [vinogradovShiftedTerminalExactScaleSet,
    Finset.filter_filter, and_comm] using hfiber.symm

/-- Shifted mixed-moment sum on one higher terminal exact scale. -/
noncomputable def normalizedVinogradovShiftedTerminalExactScaleMixedMomentSum
    (p a b k r t Y gamma : ℕ) [Fact p.Prime] : ℝ := by
  letI : NeZero (p ^ ((k - r + 1) * b)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  exact ∑ z ∈ vinogradovShiftedTerminalExactScaleSet p a b gamma,
    ‖normalizedVinogradovMixedModConditionedMoment
      p ((k - r + 1) * b) a b k r t (p ^ b * Y) Y
        (vinogradovCenterValue z.1)
        (vinogradovCenterValue z.2 - (p : ℤ) ^ b)‖

/-- Exact higher-scale decomposition of the shifted terminal mixed-moment
sum. -/
theorem
    normalizedVinogradovShiftedTerminalMixedMomentSum_eq_higherExactScales
    (p a b k r t Y : ℕ) [Fact p.Prime] (hba : b ≤ a) :
    normalizedVinogradovShiftedTerminalMixedMomentSum
        p a b k r t Y =
      ∑ gamma ∈ Finset.Icc b a,
        normalizedVinogradovShiftedTerminalExactScaleMixedMomentSum
          p a b k r t Y gamma := by
  letI : NeZero (p ^ ((k - r + 1) * b)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  unfold normalizedVinogradovShiftedTerminalMixedMomentSum
  exact
    sum_vinogradovCenterPairCongruentSet_eq_shiftedTerminalExactScales
      p a b hba (fun z ↦
        ‖normalizedVinogradovMixedModConditionedMoment
          p ((k - r + 1) * b) a b k r t (p ^ b * Y) Y
            (vinogradovCenterValue z.1)
            (vinogradovCenterValue z.2 - (p : ℤ) ^ b)‖)

/-- Every higher terminal exact scale feeds the same far-scale ordinary
moment recurrence as the nonterminal layers. -/
theorem
    normalizedVinogradovShiftedTerminalExactScaleMixedMomentSum_le_farScaleMoment
    (p a b k r t Y gamma : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b)
    (hgammaa : gamma ≤ a)
    (hbudget : gamma * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (hscale :
      p ^ b * Y ≤
        p ^ a * p ^ vinogradovFarScale k r a b gamma) :
    normalizedVinogradovShiftedTerminalExactScaleMixedMomentSum
        p a b k r t Y gamma ≤
      (vinogradovShiftedTerminalExactScaleSet p a b gamma).card *
        (‖normalizedVinogradovMomentMod
          (p ^ vinogradovFarScale k r a b gamma) r r
            (p ^ vinogradovFarScale k r a b gamma)‖ *
          (Y ^ (2 * t) : ℝ)) := by
  letI : NeZero (p ^ ((k - r + 1) * b)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  unfold normalizedVinogradovShiftedTerminalExactScaleMixedMomentSum
  calc
    (∑ z ∈ vinogradovShiftedTerminalExactScaleSet p a b gamma,
      ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * b) a b k r t (p ^ b * Y) Y
          (vinogradovCenterValue z.1)
          (vinogradovCenterValue z.2 - (p : ℤ) ^ b)‖) ≤
        ∑ _z ∈ vinogradovShiftedTerminalExactScaleSet p a b gamma,
          ‖normalizedVinogradovMomentMod
            (p ^ vinogradovFarScale k r a b gamma) r r
              (p ^ vinogradovFarScale k r a b gamma)‖ *
            (Y ^ (2 * t) : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      have hmem :=
        (mem_vinogradovShiftedTerminalExactScaleSet_iff
          p a b gamma z).1 hz
      rcases exists_coprime_shifted_terminal_center_factor
        p a b z with ⟨omega, hcenter, homega⟩
      rw [hmem.2] at hcenter
      exact norm_normalizedVinogradovMixedModConditionedMoment_le_farScaleMoment
        p a b k r t (p ^ b * Y) Y gamma
          (vinogradovCenterValue z.1)
          (vinogradovCenterValue z.2 - (p : ℤ) ^ b) omega
          hrk hkp hb hgammaa hbudget htail hcenter homega hscale
    _ = (vinogradovShiftedTerminalExactScaleSet p a b gamma).card *
        (‖normalizedVinogradovMomentMod
          (p ^ vinogradovFarScale k r a b gamma) r r
            (p ^ vinogradovFarScale k r a b gamma)‖ *
          (Y ^ (2 * t) : ℝ)) := by
      simp

/-- The whole shifted terminal layer is controlled by higher exact-scale
far moments, with no ambient tuple bound. -/
theorem
    normalizedVinogradovShiftedTerminalMixedMomentSum_le_higherExactScales
    (p a b k r t Y : ℕ) [Fact p.Prime]
    (hba : b ≤ a) (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b)
    (hbudget : ∀ gamma ∈ Finset.Icc b a,
      gamma * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (hscale : ∀ gamma ∈ Finset.Icc b a,
      p ^ b * Y ≤
        p ^ a * p ^ vinogradovFarScale k r a b gamma) :
    normalizedVinogradovShiftedTerminalMixedMomentSum
        p a b k r t Y ≤
      ∑ gamma ∈ Finset.Icc b a,
        (vinogradovShiftedTerminalExactScaleSet p a b gamma).card *
          (‖normalizedVinogradovMomentMod
            (p ^ vinogradovFarScale k r a b gamma) r r
              (p ^ vinogradovFarScale k r a b gamma)‖ *
            (Y ^ (2 * t) : ℝ)) := by
  rw [
    normalizedVinogradovShiftedTerminalMixedMomentSum_eq_higherExactScales
      p a b k r t Y hba]
  apply Finset.sum_le_sum
  intro gamma hgamma
  exact
    normalizedVinogradovShiftedTerminalExactScaleMixedMomentSum_le_farScaleMoment
      p a b k r t Y gamma hrk hkp hb
        (Finset.mem_Icc.1 hgamma).2 (hbudget gamma hgamma) htail
        (hscale gamma hgamma)

/-- The existing far-scale elimination budget cannot control every terminal
exact scale when the main center scale is strictly larger than the tail scale.
Already the first terminal scale `gamma = b` would force `a * r ≤ b`. -/
theorem not_terminal_elimination_budget_of_main_scale_gt_tail_scale
    (a b k r : ℕ) (hr : 0 < r) (hba : b < a) :
    ¬ ∀ gamma ∈ Finset.Icc b a,
      gamma * (k - r) + a * r ≤ (k - r + 1) * b := by
  intro hbudget
  have hbmem : b ∈ Finset.Icc b a := Finset.mem_Icc.2 ⟨le_rfl, hba.le⟩
  have hbudgetb := hbudget b hbmem
  have hbudgetb' :
      (k - r) * b + a * r ≤ (k - r) * b + b := by
    simpa only [Nat.add_mul, one_mul, Nat.mul_comm b (k - r)] using hbudgetb
  have harb : a * r ≤ b := Nat.le_of_add_le_add_left hbudgetb'
  have har : a ≤ a * r := by
    calc
      a = a * 1 := by simp
      _ ≤ a * r := Nat.mul_le_mul_left a hr
  exact (Nat.not_le_of_lt hba) (har.trans harb)

end

end ZeroFreeRegion.VinogradovKorobov
