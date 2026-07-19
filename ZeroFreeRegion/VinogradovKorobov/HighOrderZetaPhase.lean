import ZeroFreeRegion.VinogradovKorobov.HighOrderLogDifference
import ZeroFreeRegion.VinogradovKorobov.HigherLogDifference
import ZeroFreeRegion.VinogradovKorobov.SignedFirstDerivative

namespace ZeroFreeRegion.VinogradovKorobov

/-- Cast a list of natural A-process shifts to real shifts. -/
def natShiftsToReal (shifts : List ℕ) : List ℝ :=
  shifts.map Nat.cast

@[simp] lemma natShiftsToReal_nil : natShiftsToReal [] = [] := rfl

@[simp] lemma natShiftsToReal_cons (h : ℕ) (shifts : List ℕ) :
    natShiftsToReal (h :: shifts) = (h : ℝ) :: natShiftsToReal shifts := by
  simp [natShiftsToReal]

@[simp] lemma length_natShiftsToReal (shifts : List ℕ) :
    (natShiftsToReal shifts).length = shifts.length := by
  simp [natShiftsToReal]

lemma natShiftsToReal_nonneg (shifts : List ℕ) :
    ∀ h ∈ natShiftsToReal shifts, 0 ≤ h := by
  induction shifts with
  | nil => simp
  | cons h shifts ih =>
      intro k hk
      simp only [natShiftsToReal_cons, List.mem_cons] at hk
      rcases hk with rfl | hk
      · positivity
      · exact ih k hk

lemma prod_natShiftsToReal_pos
    (shifts : List ℕ) (hshifts : ∀ h ∈ shifts, 0 < h) :
    0 < (natShiftsToReal shifts).prod := by
  induction shifts with
  | nil => simp
  | cons h shifts ih =>
      simp only [natShiftsToReal_cons, List.prod_cons]
      exact mul_pos (Nat.cast_pos.mpr (hshifts h (by simp)))
        (ih (fun k hk ↦ hshifts k (by simp [hk])))

/-- Natural-number iterated zeta phases agree with the real-variable
difference construction after casting all shifts. -/
lemma iterated_shiftedZetaPhase_eq_real
    (t : ℝ) (m n : ℕ) (shifts : List ℕ) :
    iteratedPhaseDifference shifts (shiftedZetaPhase t m) n =
      realIteratedPhaseDifference (natShiftsToReal shifts)
        (fun x ↦ -t * Real.log ((m : ℝ) + x)) n := by
  induction shifts generalizing n with
  | nil =>
      simp [shiftedZetaPhase]
  | cons h shifts ih =>
      simp only [iteratedPhaseDifference_cons,
        realIteratedPhaseDifference_cons, realPhaseDifference,
        phaseDifference, natShiftsToReal_cons]
      rw [ih n, ih (n + h)]
      push_cast
      rfl

/-- The forward decrement of an arbitrary iterated zeta phase is the
positive logarithmic difference with one additional unit shift. -/
lemma iterated_shiftedZetaPhase_decrement_eq
    (t : ℝ) (m n : ℕ) (shifts : List ℕ) :
    iteratedPhaseDifference shifts (shiftedZetaPhase t m) n -
        iteratedPhaseDifference shifts (shiftedZetaPhase t m) (n + 1) =
      t * (-realIteratedPhaseDifference
        ((1 : ℝ) :: natShiftsToReal shifts) Real.log
          ((m + n : ℕ) : ℝ)) := by
  rw [← show iteratedPhaseDifference (1 :: shifts) (shiftedZetaPhase t m) n =
      iteratedPhaseDifference shifts (shiftedZetaPhase t m) n -
        iteratedPhaseDifference shifts (shiftedZetaPhase t m) (n + 1) by
    simp [phaseDifference]]
  rw [iterated_shiftedZetaPhase_eq_real]
  simp only [natShiftsToReal_cons, Nat.cast_one]
  rw [show (fun x ↦ -t * Real.log ((m : ℝ) + x)) =
      fun x ↦ (-t) * (fun y ↦ Real.log ((m : ℝ) + y)) x by rfl,
    realIteratedPhaseDifference_const_mul,
    realIteratedPhaseDifference_comp_add]
  push_cast
  ring

/-- Explicit arbitrary-depth scale bounds for the adjacent decrement at a
recursive A-process leaf. -/
theorem iterated_shiftedZetaPhase_decrement_bounds
    (t : ℝ) (m n : ℕ) (shifts : List ℕ)
    (ht : 0 ≤ t) (hm : 0 < m) :
    t * ((shifts.length.factorial : ℝ) *
        ((1 : ℝ) :: natShiftsToReal shifts).prod *
        ((((m + n : ℕ) : ℝ) +
          ((1 : ℝ) :: natShiftsToReal shifts).sum) ^
            ((1 : ℝ) :: natShiftsToReal shifts).length)⁻¹) ≤
      iteratedPhaseDifference shifts (shiftedZetaPhase t m) n -
        iteratedPhaseDifference shifts (shiftedZetaPhase t m) (n + 1) ∧
    iteratedPhaseDifference shifts (shiftedZetaPhase t m) n -
        iteratedPhaseDifference shifts (shiftedZetaPhase t m) (n + 1) ≤
      t * ((shifts.length.factorial : ℝ) *
        ((1 : ℝ) :: natShiftsToReal shifts).prod *
        (((m + n : ℕ) : ℝ) ^
          ((1 : ℝ) :: natShiftsToReal shifts).length)⁻¹) := by
  have hmnr : 0 < ((m + n : ℕ) : ℝ) := by
    exact Nat.cast_pos.mpr (by omega)
  have hlog := neg_realIteratedLogDifference_bounds
    (1 : ℝ) (natShiftsToReal shifts) (by norm_num)
    (natShiftsToReal_nonneg shifts) hmnr
  have hlog' :
      (shifts.length.factorial : ℝ) *
          ((1 : ℝ) :: natShiftsToReal shifts).prod *
          ((((m + n : ℕ) : ℝ) +
            ((1 : ℝ) :: natShiftsToReal shifts).sum) ^
              ((1 : ℝ) :: natShiftsToReal shifts).length)⁻¹ ≤
        -realIteratedPhaseDifference
          ((1 : ℝ) :: natShiftsToReal shifts) Real.log
            ((m + n : ℕ) : ℝ) ∧
      -realIteratedPhaseDifference
          ((1 : ℝ) :: natShiftsToReal shifts) Real.log
            ((m + n : ℕ) : ℝ) ≤
        (shifts.length.factorial : ℝ) *
          ((1 : ℝ) :: natShiftsToReal shifts).prod *
          (((m + n : ℕ) : ℝ) ^
            ((1 : ℝ) :: natShiftsToReal shifts).length)⁻¹ := by
    simpa using hlog
  rw [iterated_shiftedZetaPhase_decrement_eq]
  constructor
  · exact mul_le_mul_of_nonneg_left hlog'.1 ht
  · exact mul_le_mul_of_nonneg_left hlog'.2 ht

/-- Adjacent decrements of every iterated zeta phase decrease with the
integer position. -/
theorem antitone_iterated_shiftedZetaPhase_decrement
    (t : ℝ) (m : ℕ) (shifts : List ℕ) (ht : 0 ≤ t) (hm : 0 < m) :
    Antitone (fun n ↦
      iteratedPhaseDifference shifts (shiftedZetaPhase t m) n -
        iteratedPhaseDifference shifts (shiftedZetaPhase t m) (n + 1)) := by
  have hlogAnti := antitoneOn_neg_realIteratedLogDifference
    (1 : ℝ) (natShiftsToReal shifts) (by norm_num)
    (natShiftsToReal_nonneg shifts)
  intro a b hab
  change (iteratedPhaseDifference shifts (shiftedZetaPhase t m) b -
      iteratedPhaseDifference shifts (shiftedZetaPhase t m) (b + 1)) ≤
    (iteratedPhaseDifference shifts (shiftedZetaPhase t m) a -
      iteratedPhaseDifference shifts (shiftedZetaPhase t m) (a + 1))
  rw [iterated_shiftedZetaPhase_decrement_eq,
    iterated_shiftedZetaPhase_decrement_eq]
  apply mul_le_mul_of_nonneg_left _ ht
  have haPos : ((m + a : ℕ) : ℝ) ∈ Set.Ioi 0 := by
    change 0 < ((m + a : ℕ) : ℝ)
    exact_mod_cast (show 0 < m + a by omega)
  have hbPos : ((m + b : ℕ) : ℝ) ∈ Set.Ioi 0 := by
    change 0 < ((m + b : ℕ) : ℝ)
    exact_mod_cast (show 0 < m + b by omega)
  have habR : ((m + a : ℕ) : ℝ) ≤ ((m + b : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_left hab m
  exact hlogAnti haPos hbPos habR

/-- Arbitrary-depth Kusmin--Landau terminal estimate for a recursive
A-process leaf. -/
theorem iterated_shiftedZetaPhase_kusminLandau_range
    (t : ℝ) (m R : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m) (hR : 1 ≤ R)
    (hshifts : ∀ h ∈ shifts, 0 < h)
    (hturn :
      (iteratedPhaseDifference shifts (shiftedZetaPhase t m) 0 -
          iteratedPhaseDifference shifts (shiftedZetaPhase t m) 1) ≤
        2 * Real.pi -
          (iteratedPhaseDifference shifts (shiftedZetaPhase t m) (R - 1) -
            iteratedPhaseDifference shifts (shiftedZetaPhase t m) R)) :
    ‖∑ n ∈ Finset.range R,
        phaseTerm (iteratedPhaseDifference shifts (shiftedZetaPhase t m)) n‖ ≤
      2 * Real.pi /
        (iteratedPhaseDifference shifts (shiftedZetaPhase t m) (R - 1) -
          iteratedPhaseDifference shifts (shiftedZetaPhase t m) R) := by
  let d : ℕ → ℝ := fun n ↦
    iteratedPhaseDifference shifts (shiftedZetaPhase t m) n -
      iteratedPhaseDifference shifts (shiftedZetaPhase t m) (n + 1)
  have hdAnti : Antitone d := by
    exact antitone_iterated_shiftedZetaPhase_decrement t m shifts ht.le hm
  have hlast : R - 1 + 1 = R := by omega
  have hbounds := iterated_shiftedZetaPhase_decrement_bounds
    t m (R - 1) shifts ht.le hm
  rw [hlast] at hbounds
  have hprodPos : 0 < ((1 : ℝ) :: natShiftsToReal shifts).prod := by
    simp only [List.prod_cons, one_mul]
    exact prod_natShiftsToReal_pos shifts hshifts
  have hbasePos : 0 < (((m + (R - 1) : ℕ) : ℝ) +
      ((1 : ℝ) :: natShiftsToReal shifts).sum) := by
    have : 0 < ((m + (R - 1) : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hsum := list_sum_nonneg_of_forall
      ((1 : ℝ) :: natShiftsToReal shifts) (by
        intro k hk
        simp only [List.mem_cons] at hk
        rcases hk with rfl | hk
        · norm_num
        · exact natShiftsToReal_nonneg shifts k hk)
    linarith
  have hlowerPos : 0 < t * ((shifts.length.factorial : ℝ) *
      ((1 : ℝ) :: natShiftsToReal shifts).prod *
      ((((m + (R - 1) : ℕ) : ℝ) +
        ((1 : ℝ) :: natShiftsToReal shifts).sum) ^
          ((1 : ℝ) :: natShiftsToReal shifts).length)⁻¹) := by
    have hpow : 0 < ((((m + (R - 1) : ℕ) : ℝ) +
        ((1 : ℝ) :: natShiftsToReal shifts).sum) ^
          ((1 : ℝ) :: natShiftsToReal shifts).length)⁻¹ := by positivity
    positivity
  have hdelta : 0 < d (R - 1) := by
    dsimp [d]
    rw [hlast]
    exact hlowerPos.trans_le hbounds.1
  rw [← hlast]
  apply kusminLandau_negative_antitone_two_pi_div
    (iteratedPhaseDifference shifts (shiftedZetaPhase t m)) (R - 1)
    hdelta
  · intro n hn
    exact hdAnti hn
  · intro n hn
    have hn0 : d n ≤ d 0 := hdAnti (Nat.zero_le n)
    have hturnD : d 0 ≤ 2 * Real.pi - d (R - 1) := by
      dsimp [d]
      rw [hlast]
      exact hturn
    exact hn0.trans hturnD
  · intro n hn
    exact hdAnti (Nat.le_succ n)

end ZeroFreeRegion.VinogradovKorobov
