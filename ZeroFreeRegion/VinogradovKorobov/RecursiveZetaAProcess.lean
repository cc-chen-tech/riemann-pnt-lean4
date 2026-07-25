import ZeroFreeRegion.VinogradovKorobov.RecursiveAProcess
import ZeroFreeRegion.VinogradovKorobov.HighOrderZetaPhase

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- The adjacent phase decrement at an arbitrary A-process leaf. -/
noncomputable def iteratedZetaPhaseDecrement
    (t : ℝ) (m : ℕ) (shifts : List ℕ) (n : ℕ) : ℝ :=
  iteratedPhaseDifference shifts (shiftedZetaPhase t m) n -
    iteratedPhaseDifference shifts (shiftedZetaPhase t m) (n + 1)

/-- The smallest adjacent decrement used by the terminal Kusmin--Landau
estimate. -/
noncomputable def zetaAProcessLeafDelta
    (t : ℝ) (m N : ℕ) (shifts : List ℕ) : ℝ :=
  iteratedZetaPhaseDecrement t m shifts
    (remainingAProcessLength N shifts - 1)

/-- Squared terminal envelope supplied to the recursive A-process. -/
noncomputable def zetaAProcessLeafSquaredBound
    (t : ℝ) (m N : ℕ) (shifts : List ℕ) : ℝ :=
  (2 * Real.pi / zetaAProcessLeafDelta t m N shifts) ^ 2

/-- Explicit upper majorant for the first adjacent decrement at a leaf. -/
noncomputable def zetaAProcessLeafInitialMajorant
    (t : ℝ) (m : ℕ) (shifts : List ℕ) : ℝ :=
  t * ((shifts.length.factorial : ℝ) *
    ((1 : ℝ) :: natShiftsToReal shifts).prod *
    ((m : ℝ) ^ ((1 : ℝ) :: natShiftsToReal shifts).length)⁻¹)

/-- The terminal hypotheses needed to apply the arbitrary-depth
Kusmin--Landau estimate. -/
noncomputable def ZetaAProcessLeafValid
    (t : ℝ) (m N : ℕ) (shifts : List ℕ) : Prop :=
  let R := remainingAProcessLength N shifts
  1 ≤ R ∧
    (∀ h ∈ shifts, 0 < h) ∧
    iteratedZetaPhaseDecrement t m shifts 0 ≤
      2 * Real.pi - zetaAProcessLeafDelta t m N shifts

/-- An unconditional terminal envelope.  A leaf uses the better of the
trivial and Kusmin--Landau bounds when the nonresonant-turn hypotheses hold,
and otherwise falls back to the trivial bound. -/
noncomputable def zetaAProcessHybridLeafSquaredBound
    (t : ℝ) (m N : ℕ) (shifts : List ℕ) : ℝ := by
  classical
  exact if ZetaAProcessLeafValid t m N shifts then
      min ((remainingAProcessLength N shifts : ℝ) ^ 2)
        (zetaAProcessLeafSquaredBound t m N shifts)
    else
      (remainingAProcessLength N shifts : ℝ) ^ 2

/-- A purely scale-based sufficient condition for a zeta A-process leaf.
The explicit first-decrement majorant staying below `pi` prevents the entire
monotone decrement range from crossing one full turn. -/
noncomputable def ZetaAProcessScaleLeafValid
    (t : ℝ) (m N : ℕ) (shifts : List ℕ) : Prop :=
  1 ≤ remainingAProcessLength N shifts ∧
    (∀ h ∈ shifts, 0 < h) ∧
    zetaAProcessLeafInitialMajorant t m shifts ≤ Real.pi

/-- Specialized proof obligations for a zeta-phase recursive A-process tree.
Internal nodes choose admissible differencing lengths; leaves carry the
nonresonant-turn condition for Kusmin--Landau. -/
noncomputable def RecursiveZetaAProcessValid
    (t : ℝ) (m : ℕ) (L : List ℕ → ℕ) (N : ℕ) :
    ℕ → List ℕ → Prop
  | 0, shifts => ZetaAProcessLeafValid t m N shifts
  | depth + 1, shifts =>
      1 ≤ L shifts ∧
      L shifts ≤ remainingAProcessLength N shifts ∧
      ∀ ell ∈ Finset.Icc 1 (L shifts - 1),
        RecursiveZetaAProcessValid t m L N depth (ell :: shifts)

/-- Recursive A-process obligations with the terminal turn condition replaced
by the explicit initial-decrement scale inequality. -/
noncomputable def RecursiveZetaAProcessScaleValid
    (t : ℝ) (m : ℕ) (L : List ℕ → ℕ) (N : ℕ) :
    ℕ → List ℕ → Prop
  | 0, shifts => ZetaAProcessScaleLeafValid t m N shifts
  | depth + 1, shifts =>
      1 ≤ L shifts ∧
      L shifts ≤ remainingAProcessLength N shifts ∧
      ∀ ell ∈ Finset.Icc 1 (L shifts - 1),
        RecursiveZetaAProcessScaleValid t m L N depth (ell :: shifts)

/-- The explicit scale majorant implies the nonresonant-turn leaf condition. -/
theorem zetaAProcessLeafValid_of_scale
    (t : ℝ) (m N : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : ZetaAProcessScaleLeafValid t m N shifts) :
    ZetaAProcessLeafValid t m N shifts := by
  rcases hvalid with ⟨hR, hshifts, hmajor⟩
  refine ⟨hR, hshifts, ?_⟩
  let R := remainingAProcessLength N shifts
  have hbounds := iterated_shiftedZetaPhase_decrement_bounds
    t m 0 shifts ht.le hm
  have hfirst : iteratedZetaPhaseDecrement t m shifts 0 ≤
      zetaAProcessLeafInitialMajorant t m shifts := by
    simpa only [iteratedZetaPhaseDecrement,
      zetaAProcessLeafInitialMajorant, Nat.add_zero] using hbounds.2
  have hanti := antitone_iterated_shiftedZetaPhase_decrement
    t m shifts ht.le hm
  have hlastFirst : zetaAProcessLeafDelta t m N shifts ≤
      iteratedZetaPhaseDecrement t m shifts 0 := by
    simpa only [R, zetaAProcessLeafDelta, iteratedZetaPhaseDecrement] using
      hanti (Nat.zero_le (R - 1))
  have hfirstPi := hfirst.trans hmajor
  have hlastPi := hlastFirst.trans hfirstPi
  linarith

/-- Every scale-valid recursive zeta tree is valid for the terminal
Kusmin--Landau formulation. -/
theorem recursiveZetaAProcessValid_of_scale
    (t : ℝ) (m : ℕ) (L : List ℕ → ℕ) (N depth : ℕ)
    (shifts : List ℕ) (ht : 0 < t) (hm : 0 < m)
    (hvalid : RecursiveZetaAProcessScaleValid t m L N depth shifts) :
    RecursiveZetaAProcessValid t m L N depth shifts := by
  induction depth generalizing shifts with
  | zero =>
      exact zetaAProcessLeafValid_of_scale
        t m N shifts ht hm hvalid
  | succ depth ih =>
      rcases hvalid with ⟨hL, hLN, hchildren⟩
      exact ⟨hL, hLN, fun ell hell ↦
        ih (ell :: shifts) (hchildren ell hell)⟩

/-- The specialized zeta conditions discharge every leaf and internal-node
obligation of the generic recursive A-process. -/
theorem recursiveZetaAProcessValid_to_generic
    (t : ℝ) (m : ℕ) (L : List ℕ → ℕ) (N depth : ℕ)
    (shifts : List ℕ) (ht : 0 < t) (hm : 0 < m)
    (hvalid : RecursiveZetaAProcessValid t m L N depth shifts) :
    RecursiveAProcessValid (shiftedZetaPhase t m) L
      (zetaAProcessLeafSquaredBound t m N) N depth shifts := by
  induction depth generalizing shifts with
  | zero =>
      change ZetaAProcessLeafValid t m N shifts at hvalid
      rcases hvalid with ⟨hR, hshifts, hturn⟩
      let R := remainingAProcessLength N shifts
      have hlast : R - 1 + 1 = R := by omega
      have hturn' :
          (iteratedPhaseDifference shifts (shiftedZetaPhase t m) 0 -
              iteratedPhaseDifference shifts (shiftedZetaPhase t m) 1) ≤
            2 * Real.pi -
              (iteratedPhaseDifference shifts (shiftedZetaPhase t m) (R - 1) -
                iteratedPhaseDifference shifts (shiftedZetaPhase t m) R) := by
        simpa only [R, iteratedZetaPhaseDecrement, zetaAProcessLeafDelta,
          Nat.zero_add, hlast] using hturn
      have hnorm :
          ‖∑ n ∈ Finset.range R,
              phaseTerm
                (iteratedPhaseDifference shifts (shiftedZetaPhase t m)) n‖ ≤
            2 * Real.pi / zetaAProcessLeafDelta t m N shifts := by
        simpa only [R, zetaAProcessLeafDelta, iteratedZetaPhaseDecrement,
          hlast] using
          iterated_shiftedZetaPhase_kusminLandau_range
            t m R shifts ht hm hR hshifts hturn'
      have hdelta : 0 < zetaAProcessLeafDelta t m N shifts := by
        exact iterated_shiftedZetaPhase_decrement_pos
          t m (R - 1) shifts ht hm hshifts
      have hbound : 0 ≤ 2 * Real.pi /
          zetaAProcessLeafDelta t m N shifts :=
        div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hdelta.le
      change
        ‖∑ n ∈ Finset.range R,
            phaseTerm
              (iteratedPhaseDifference shifts (shiftedZetaPhase t m)) n‖ ^ 2 ≤
          zetaAProcessLeafSquaredBound t m N shifts
      exact (sq_le_sq₀ (norm_nonneg _) hbound).2 hnorm
  | succ depth ih =>
      rcases hvalid with ⟨hL, hLN, hchildren⟩
      exact ⟨hL, hLN, fun ell hell ↦
        ih (ell :: shifts) (hchildren ell hell)⟩

/-- Every iterated zeta phase sum satisfies the hybrid terminal envelope,
without requiring a nonresonance hypothesis at the leaf. -/
theorem norm_iteratedZetaPhase_sum_sq_le_hybridLeaf
    (t : ℝ) (m N : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m) :
    ‖∑ n ∈ Finset.range (remainingAProcessLength N shifts),
        phaseTerm
          (iteratedPhaseDifference shifts (shiftedZetaPhase t m)) n‖ ^ 2 ≤
      zetaAProcessHybridLeafSquaredBound t m N shifts := by
  by_cases hvalid : ZetaAProcessLeafValid t m N shifts
  · rw [zetaAProcessHybridLeafSquaredBound, if_pos hvalid]
    apply le_min
    · exact norm_iteratedPhase_sum_sq_le_trivial
        (shiftedZetaPhase t m) N shifts
    · exact recursiveZetaAProcessValid_to_generic
        t m (fun _ ↦ 1) N 0 shifts ht hm hvalid
  · rw [zetaAProcessHybridLeafSquaredBound, if_neg hvalid]
    exact norm_iteratedPhase_sum_sq_le_trivial
      (shiftedZetaPhase t m) N shifts

/-- Root estimate obtained by connecting the recursive A-process to
arbitrary-order logarithmic Kusmin--Landau leaves. -/
theorem norm_zetaPhase_sum_sq_le_recursiveAProcess
    (t : ℝ) (m : ℕ) (L : List ℕ → ℕ) (N depth : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : RecursiveZetaAProcessValid t m L N depth []) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      recursiveAProcessSquaredBound L
        (zetaAProcessLeafSquaredBound t m N) N depth [] := by
  apply norm_phaseSum_sq_le_recursiveAProcess
  exact recursiveZetaAProcessValid_to_generic
    t m L N depth [] ht hm hvalid

/-- Root recursive A-process estimate under fully explicit scale-valid leaf
conditions. -/
theorem norm_zetaPhase_sum_sq_le_recursiveAProcess_of_scale
    (t : ℝ) (m : ℕ) (L : List ℕ → ℕ) (N depth : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : RecursiveZetaAProcessScaleValid t m L N depth []) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      recursiveAProcessSquaredBound L
        (zetaAProcessLeafSquaredBound t m N) N depth [] := by
  apply norm_zetaPhase_sum_sq_le_recursiveAProcess t m L N depth ht hm
  exact recursiveZetaAProcessValid_of_scale
    t m L N depth [] ht hm hvalid

end ZeroFreeRegion.VinogradovKorobov
