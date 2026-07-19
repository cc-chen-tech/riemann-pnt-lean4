import ZeroFreeRegion.VinogradovKorobov.RecursiveZetaAProcess
import ZeroFreeRegion.VinogradovKorobov.RecursiveAProcessEnvelope

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

/-- The path-independent leaf decrement lower bound decreases when the
right endpoint of the root block moves to the right. -/
theorem zetaAProcessUniformLeafDeltaLower_antitone_endpoint
    (t : ℝ) (m₁ N₁ m₂ N₂ depth : ℕ)
    (ht : 0 ≤ t) (hleft : 0 < m₁ + N₁)
    (hend : m₁ + N₁ ≤ m₂ + N₂) :
    zetaAProcessUniformLeafDeltaLower t m₂ N₂ depth ≤
      zetaAProcessUniformLeafDeltaLower t m₁ N₁ depth := by
  have hleftReal : 0 < (((m₁ + N₁ : ℕ) : ℝ)) := by
    exact_mod_cast hleft
  have hendReal : (((m₁ + N₁ : ℕ) : ℝ)) ≤
      (((m₂ + N₂ : ℕ) : ℝ)) := by
    exact_mod_cast hend
  have hinv := inv_pow_antitone (depth + 1) hleftReal hendReal
  unfold zetaAProcessUniformLeafDeltaLower
  apply mul_le_mul_of_nonneg_left _ ht
  exact mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg depth.factorial)

/-- Path-independent squared Kusmin--Landau envelope at fixed depth. -/
noncomputable def zetaAProcessUniformLeafSquaredBound
    (t : ℝ) (m N depth : ℕ) : ℝ :=
  (2 * Real.pi / zetaAProcessUniformLeafDeltaLower t m N depth) ^ 2

/-- Path-sensitive terminal envelope retaining the full product of the
A-process shifts. -/
noncomputable def zetaAProcessProductLeafSquaredBound
    (t : ℝ) (m N depth : ℕ) (shifts : List ℕ) : ℝ :=
  (2 * Real.pi /
    (zetaAProcessUniformLeafDeltaLower t m N depth * (shifts.prod : ℝ))) ^ 2

/-- Path-sensitive terminal envelope retaining both the trivial length bound
and the reciprocal shift-product Kusmin--Landau bound. -/
noncomputable def zetaAProcessHybridProductLeafSquaredBound
    (t : ℝ) (m N depth : ℕ) (shifts : List ℕ) : ℝ :=
  min ((remainingAProcessLength N shifts : ℝ) ^ 2)
    (zetaAProcessProductLeafSquaredBound t m N depth shifts)

/-- The uniform coefficient times the complete positive shift product is a
lower bound for the terminal adjacent decrement. -/
theorem zetaAProcessUniformLeafDeltaLower_mul_prod_le
    (t : ℝ) (m N depth : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hR : 1 ≤ remainingAProcessLength N shifts)
    (hdepth : shifts.length = depth) :
    zetaAProcessUniformLeafDeltaLower t m N depth * (shifts.prod : ℝ) ≤
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
  have hraw :
      t * ((depth.factorial : ℝ) * (shifts.prod : ℝ) *
          (((m + N : ℕ) : ℝ) ^ (depth + 1))⁻¹) ≤
        zetaAProcessLeafDelta t m N shifts := by
    simpa only [R, zetaAProcessLeafDelta, iteratedZetaPhaseDecrement,
      hbase, List.length_cons, length_natShiftsToReal, hdepth,
      List.prod_cons, one_mul, prod_natShiftsToReal] using hbounds.1
  unfold zetaAProcessUniformLeafDeltaLower
  calc
    t * ((depth.factorial : ℝ) *
        (((m + N : ℕ) : ℝ) ^ (depth + 1))⁻¹) * (shifts.prod : ℝ) =
      t * ((depth.factorial : ℝ) * (shifts.prod : ℝ) *
        (((m + N : ℕ) : ℝ) ^ (depth + 1))⁻¹) := by ring
    _ ≤ zetaAProcessLeafDelta t m N shifts := hraw

/-- The actual leaf envelope is controlled by the path-sensitive product
envelope. -/
theorem zetaAProcessLeafSquaredBound_le_product
    (t : ℝ) (m N depth : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hR : 1 ≤ remainingAProcessLength N shifts)
    (hshifts : ∀ h ∈ shifts, 0 < h)
    (hdepth : shifts.length = depth) :
    zetaAProcessLeafSquaredBound t m N shifts ≤
      zetaAProcessProductLeafSquaredBound t m N depth shifts := by
  have hlower := zetaAProcessUniformLeafDeltaLower_mul_prod_le
    t m N depth shifts ht hm hR hdepth
  have hcoeffPos : 0 < zetaAProcessUniformLeafDeltaLower t m N depth := by
    unfold zetaAProcessUniformLeafDeltaLower
    have hmN : 0 < ((m + N : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    positivity
  have hprodPos : 0 < (shifts.prod : ℝ) := by
    exact_mod_cast (show 0 < shifts.prod by
      exact List.prod_pos hshifts)
  have hlowerPos : 0 <
      zetaAProcessUniformLeafDeltaLower t m N depth * (shifts.prod : ℝ) :=
    mul_pos hcoeffPos hprodPos
  have hdeltaPos : 0 < zetaAProcessLeafDelta t m N shifts := by
    exact iterated_shiftedZetaPhase_decrement_pos
      t m (remainingAProcessLength N shifts - 1) shifts ht hm hshifts
  have hquot :
      2 * Real.pi / zetaAProcessLeafDelta t m N shifts ≤
        2 * Real.pi /
          (zetaAProcessUniformLeafDeltaLower t m N depth *
            (shifts.prod : ℝ)) :=
    div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num) Real.pi_pos.le) hlowerPos hlower
  unfold zetaAProcessLeafSquaredBound zetaAProcessProductLeafSquaredBound
  exact (sq_le_sq₀
    (div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hdeltaPos.le)
    (div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hlowerPos.le)).2 hquot

/-- At a scale-valid leaf, the unconditional hybrid envelope is controlled
by the explicit minimum of the trivial and shift-product bounds. -/
theorem zetaAProcessHybridLeafSquaredBound_le_productMin
    (t : ℝ) (m N depth : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hscale : ZetaAProcessScaleLeafValid t m N shifts)
    (hdepth : shifts.length = depth) :
    zetaAProcessHybridLeafSquaredBound t m N shifts ≤
      zetaAProcessHybridProductLeafSquaredBound t m N depth shifts := by
  rcases hscale with ⟨hR, hshifts, hmajor⟩
  have hvalid : ZetaAProcessLeafValid t m N shifts :=
    zetaAProcessLeafValid_of_scale t m N shifts ht hm
      ⟨hR, hshifts, hmajor⟩
  rw [zetaAProcessHybridLeafSquaredBound, if_pos hvalid]
  unfold zetaAProcessHybridProductLeafSquaredBound
  exact min_le_min le_rfl (zetaAProcessLeafSquaredBound_le_product
    t m N depth shifts ht hm hR hshifts hdepth)

/-- A scale-valid zeta tree can retain the pathwise minimum of the trivial
and reciprocal-product terminal bounds. -/
theorem recursiveZetaAProcessScaleValid_to_hybridProductGeneric
    (t : ℝ) (m N totalDepth depth : ℕ) (H : ℕ → ℕ)
    (shifts : List ℕ) (ht : 0 < t) (hm : 0 < m)
    (hlen : shifts.length + depth = totalDepth)
    (hvalid : RecursiveZetaAProcessScaleValid
      t m (fun s ↦ H s.length) N depth shifts) :
    RecursiveAProcessValid (shiftedZetaPhase t m) (fun s ↦ H s.length)
      (zetaAProcessHybridProductLeafSquaredBound t m N totalDepth)
      N depth shifts := by
  induction depth generalizing shifts with
  | zero =>
      have hdepth : shifts.length = totalDepth := by omega
      exact (norm_iteratedZetaPhase_sum_sq_le_hybridLeaf
        t m N shifts ht hm).trans
          (zetaAProcessHybridLeafSquaredBound_le_productMin
            t m N totalDepth shifts ht hm hvalid hdepth)
  | succ depth ih =>
      rcases hvalid with ⟨hH, hHR, hchildren⟩
      refine ⟨hH, hHR, ?_⟩
      intro ell hell
      have hchildLen : (ell :: shifts).length + depth = totalDepth := by
        simp only [List.length_cons]
        omega
      exact ih (ell :: shifts) hchildLen (hchildren ell hell)

/-- Root A-process estimate retaining the path-sensitive minimum at every
terminal node. -/
theorem norm_zetaPhase_sum_sq_le_hybridProductRecursiveAProcess_of_scale
    (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : RecursiveZetaAProcessScaleValid
      t m (fun s ↦ H s.length) N depth []) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      recursiveAProcessSquaredBound (fun s ↦ H s.length)
        (zetaAProcessHybridProductLeafSquaredBound t m N depth)
        N depth [] := by
  apply norm_phaseSum_sq_le_recursiveAProcess
  exact recursiveZetaAProcessScaleValid_to_hybridProductGeneric
    t m N depth depth H [] ht hm (by simp) hvalid

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

/-- A scale-valid zeta tree can use one constant terminal bound at every leaf
because every root-to-leaf path has the prescribed total depth. -/
theorem recursiveZetaAProcessScaleValid_to_uniformGeneric
    (t : ℝ) (m N totalDepth depth : ℕ) (H : ℕ → ℕ)
    (shifts : List ℕ) (ht : 0 < t) (hm : 0 < m)
    (hlen : shifts.length + depth = totalDepth)
    (hvalid : RecursiveZetaAProcessScaleValid
      t m (fun s ↦ H s.length) N depth shifts) :
    RecursiveAProcessValid (shiftedZetaPhase t m) (fun s ↦ H s.length)
      (fun _ ↦ zetaAProcessUniformLeafSquaredBound t m N totalDepth)
      N depth shifts := by
  induction depth generalizing shifts with
  | zero =>
      rcases hvalid with ⟨hR, hshifts, hmajor⟩
      have hdepth : shifts.length = totalDepth := by omega
      have hscale : ZetaAProcessScaleLeafValid t m N shifts :=
        ⟨hR, hshifts, hmajor⟩
      have hactual :
          RecursiveAProcessValid (shiftedZetaPhase t m)
            (fun s ↦ H s.length) (zetaAProcessLeafSquaredBound t m N)
            N 0 shifts := by
        apply recursiveZetaAProcessValid_to_generic
          t m (fun s ↦ H s.length) N 0 shifts ht hm
        exact recursiveZetaAProcessValid_of_scale
          t m (fun s ↦ H s.length) N 0 shifts ht hm hscale
      exact hactual.trans (zetaAProcessLeafSquaredBound_le_uniform
        t m N totalDepth shifts ht hm hR hshifts hdepth)
  | succ depth ih =>
      rcases hvalid with ⟨hH, hHR, hchildren⟩
      refine ⟨hH, hHR, ?_⟩
      intro ell hell
      have hchildLen : (ell :: shifts).length + depth = totalDepth := by
        simp only [List.length_cons]
        omega
      exact ih (ell :: shifts) hchildLen (hchildren ell hell)

/-- Fully connected arbitrary-depth zeta exponential-sum estimate: explicit
scale-valid tree conditions imply a path-independent numerical envelope. -/
theorem norm_zetaPhase_sum_sq_le_uniformCoarseRecursiveAProcess
    (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : RecursiveZetaAProcessScaleValid
      t m (fun s ↦ H s.length) N depth []) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      coarseRecursiveAProcessSquaredBound H N
        (zetaAProcessUniformLeafSquaredBound t m N depth) depth 0 := by
  apply norm_phaseSum_sq_le_coarseRecursiveAProcess
    (shiftedZetaPhase t m) H
    (fun _ ↦ zetaAProcessUniformLeafSquaredBound t m N depth)
    N (zetaAProcessUniformLeafSquaredBound t m N depth) depth
  · exact recursiveZetaAProcessScaleValid_to_uniformGeneric
      t m N depth depth H [] ht hm (by simp) hvalid
  · intro shifts
    exact le_rfl

end ZeroFreeRegion.VinogradovKorobov
