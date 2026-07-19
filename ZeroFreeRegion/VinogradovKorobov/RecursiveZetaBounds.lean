import ZeroFreeRegion.VinogradovKorobov.RecursiveZetaAProcess

namespace ZeroFreeRegion.VinogradovKorobov

@[simp] lemma sum_natShiftsToReal (shifts : List ℕ) :
    (natShiftsToReal shifts).sum = (shifts.sum : ℝ) := by
  simp [natShiftsToReal]

@[simp] lemma prod_natShiftsToReal (shifts : List ℕ) :
    (natShiftsToReal shifts).prod = (shifts.prod : ℝ) := by
  simp [natShiftsToReal]

lemma one_le_prod_natShiftsToReal
    (shifts : List ℕ) (hshifts : ∀ h ∈ shifts, 0 < h) :
    1 ≤ (natShiftsToReal shifts).prod := by
  induction shifts with
  | nil => simp
  | cons h shifts ih =>
      simp only [natShiftsToReal_cons, List.prod_cons]
      have hh : 1 ≤ (h : ℝ) := by
        exact_mod_cast hshifts h (by simp)
      have htail : 1 ≤ (natShiftsToReal shifts).prod :=
        ih (fun k hk ↦ hshifts k (by simp [hk]))
      calc
        1 = 1 * 1 := by ring
        _ ≤ (h : ℝ) * (natShiftsToReal shifts).prod :=
          mul_le_mul hh htail (by norm_num) (by positivity)

/-- Path-independent lower bound for the terminal adjacent decrement at a
fixed A-process depth. -/
noncomputable def zetaAProcessUniformLeafDeltaLower
    (t : ℝ) (m N depth : ℕ) : ℝ :=
  t * ((depth.factorial : ℝ) *
    (((m + N : ℕ) : ℝ) ^ (depth + 1))⁻¹)

/-- Path-independent squared Kusmin--Landau envelope at fixed depth. -/
noncomputable def zetaAProcessUniformLeafSquaredBound
    (t : ℝ) (m N depth : ℕ) : ℝ :=
  (2 * Real.pi / zetaAProcessUniformLeafDeltaLower t m N depth) ^ 2

/-- Every positive-shift leaf of the prescribed depth has at least the
uniform terminal decrement. -/
theorem zetaAProcessUniformLeafDeltaLower_le
    (t : ℝ) (m N depth : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hR : 1 ≤ remainingAProcessLength N shifts)
    (hshifts : ∀ h ∈ shifts, 0 < h)
    (hdepth : shifts.length = depth) :
    zetaAProcessUniformLeafDeltaLower t m N depth ≤
      zetaAProcessLeafDelta t m N shifts := by
  let R := remainingAProcessLength N shifts
  have hsumlt : shifts.sum < N := by
    unfold remainingAProcessLength at hR
    omega
  have hnat : m + (R - 1) + (1 + shifts.sum) = m + N := by
    dsimp [R, remainingAProcessLength]
    omega
  have hbase :
      (((m + (R - 1) : ℕ) : ℝ) +
          ((1 : ℝ) :: natShiftsToReal shifts).sum) =
        ((m + N : ℕ) : ℝ) := by
    simp only [List.sum_cons, sum_natShiftsToReal]
    exact_mod_cast hnat
  have hbounds := iterated_shiftedZetaPhase_decrement_bounds
    t m (R - 1) shifts ht.le hm
  have hfull :
      t * ((depth.factorial : ℝ) *
          ((1 : ℝ) :: natShiftsToReal shifts).prod *
          (((m + N : ℕ) : ℝ) ^ (depth + 1))⁻¹) ≤
        zetaAProcessLeafDelta t m N shifts := by
    simpa only [R, zetaAProcessLeafDelta, iteratedZetaPhaseDecrement,
      hbase, List.length_cons, length_natShiftsToReal, hdepth] using hbounds.1
  have hprod : 1 ≤ ((1 : ℝ) :: natShiftsToReal shifts).prod := by
    simp only [List.prod_cons, one_mul]
    exact one_le_prod_natShiftsToReal shifts hshifts
  unfold zetaAProcessUniformLeafDeltaLower
  calc
    t * ((depth.factorial : ℝ) *
        (((m + N : ℕ) : ℝ) ^ (depth + 1))⁻¹) =
        t * ((depth.factorial : ℝ) * 1 *
          (((m + N : ℕ) : ℝ) ^ (depth + 1))⁻¹) := by ring
    _ ≤ t * ((depth.factorial : ℝ) *
        ((1 : ℝ) :: natShiftsToReal shifts).prod *
        (((m + N : ℕ) : ℝ) ^ (depth + 1))⁻¹) := by
      gcongr
    _ ≤ zetaAProcessLeafDelta t m N shifts := hfull

/-- The path-dependent leaf envelope is bounded by a single envelope that
depends only on the root block and the recursion depth. -/
theorem zetaAProcessLeafSquaredBound_le_uniform
    (t : ℝ) (m N depth : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hR : 1 ≤ remainingAProcessLength N shifts)
    (hshifts : ∀ h ∈ shifts, 0 < h)
    (hdepth : shifts.length = depth) :
    zetaAProcessLeafSquaredBound t m N shifts ≤
      zetaAProcessUniformLeafSquaredBound t m N depth := by
  have hlower := zetaAProcessUniformLeafDeltaLower_le
    t m N depth shifts ht hm hR hshifts hdepth
  have hlowerPos : 0 < zetaAProcessUniformLeafDeltaLower t m N depth := by
    unfold zetaAProcessUniformLeafDeltaLower
    have hmN : 0 < ((m + N : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    positivity
  have hdeltaPos : 0 < zetaAProcessLeafDelta t m N shifts := by
    exact iterated_shiftedZetaPhase_decrement_pos
      t m (remainingAProcessLength N shifts - 1) shifts ht hm hshifts
  have hquot :
      2 * Real.pi / zetaAProcessLeafDelta t m N shifts ≤
        2 * Real.pi / zetaAProcessUniformLeafDeltaLower t m N depth :=
    div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num) Real.pi_pos.le) hlowerPos hlower
  unfold zetaAProcessLeafSquaredBound zetaAProcessUniformLeafSquaredBound
  exact (sq_le_sq₀
    (div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hdeltaPos.le)
    (div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hlowerPos.le)).2 hquot

end ZeroFreeRegion.VinogradovKorobov
