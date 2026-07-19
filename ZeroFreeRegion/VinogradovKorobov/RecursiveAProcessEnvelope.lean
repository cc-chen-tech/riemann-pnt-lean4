import ZeroFreeRegion.VinogradovKorobov.AProcessBounds
import ZeroFreeRegion.VinogradovKorobov.RecursiveAProcess

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- A path-independent numerical envelope for a level-scheduled recursive
A-process.  The root length `N` majorizes every shorter descendant block. -/
noncomputable def coarseRecursiveAProcessSquaredBound
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => C
  | depth + 1, level =>
      2 * (N : ℝ) ^ 2 / H level +
        4 * (N : ℝ) * Real.sqrt
          (coarseRecursiveAProcessSquaredBound H N C depth (level + 1))

@[simp] lemma coarseRecursiveAProcessSquaredBound_zero
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ) (level : ℕ) :
    coarseRecursiveAProcessSquaredBound H N C 0 level = C := rfl

@[simp] lemma coarseRecursiveAProcessSquaredBound_succ
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ) (depth level : ℕ) :
    coarseRecursiveAProcessSquaredBound H N C (depth + 1) level =
      2 * (N : ℝ) ^ 2 / H level +
        4 * (N : ℝ) * Real.sqrt
          (coarseRecursiveAProcessSquaredBound H N C depth (level + 1)) := rfl

/-- A recursive A-process tree with level-dependent differencing lengths and
a uniform leaf bound is controlled by the coarse numerical envelope. -/
theorem recursiveAProcessSquaredBound_le_coarse
    (f : ℕ → ℝ) (H : ℕ → ℕ) (Q : List ℕ → ℝ)
    (N : ℕ) (C : ℝ) (depth : ℕ) (shifts : List ℕ)
    (hvalid : RecursiveAProcessValid
      f (fun s ↦ H s.length) Q N depth shifts)
    (hleaf : ∀ s, Q s ≤ C) :
    recursiveAProcessSquaredBound (fun s ↦ H s.length) Q N depth shifts ≤
      coarseRecursiveAProcessSquaredBound H N C depth shifts.length := by
  induction depth generalizing shifts with
  | zero =>
      exact hleaf shifts
  | succ depth ih =>
      rcases hvalid with ⟨hH, hHR, hchildren⟩
      let R := remainingAProcessLength N shifts
      let E := coarseRecursiveAProcessSquaredBound
        H N C depth (shifts.length + 1)
      have hstep :
          aProcessSquaredBound
              (fun ell ↦ Real.sqrt
                (recursiveAProcessSquaredBound
                  (fun s ↦ H s.length) Q N depth (ell :: shifts)))
              R (H shifts.length) ≤
            2 * (R : ℝ) ^ 2 / H shifts.length +
              4 * (R : ℝ) * Real.sqrt E := by
        apply aProcessSquaredBound_le
          _ (Real.sqrt E) R (H shifts.length) hH hHR
          (Real.sqrt_nonneg E)
        · intro ell hell
          exact Real.sqrt_nonneg _
        · intro ell hell
          apply Real.sqrt_le_sqrt
          simpa only [E, List.length_cons] using
            ih (ell :: shifts) (hchildren ell hell)
      have hRNnat : R ≤ N := by
        simpa only [R, remainingAProcessLength] using
          Nat.sub_le N shifts.sum
      have hRNR : (R : ℝ) ≤ (N : ℝ) := by exact_mod_cast hRNnat
      have hRnonneg : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
      have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      have hHpos : 0 < (H shifts.length : ℝ) :=
        Nat.cast_pos.mpr (by
          simpa using (lt_of_lt_of_le Nat.zero_lt_one hH))
      have hfirst :
          2 * (R : ℝ) ^ 2 / H shifts.length ≤
            2 * (N : ℝ) ^ 2 / H shifts.length := by
        apply div_le_div_of_nonneg_right _ hHpos.le
        gcongr
      have hsecond :
          4 * (R : ℝ) * Real.sqrt E ≤
            4 * (N : ℝ) * Real.sqrt E := by
        gcongr
      calc
        recursiveAProcessSquaredBound
            (fun s ↦ H s.length) Q N (depth + 1) shifts =
            aProcessSquaredBound
              (fun ell ↦ Real.sqrt
                (recursiveAProcessSquaredBound
                  (fun s ↦ H s.length) Q N depth (ell :: shifts)))
              R (H shifts.length) := rfl
        _ ≤ 2 * (R : ℝ) ^ 2 / H shifts.length +
              4 * (R : ℝ) * Real.sqrt E := hstep
        _ ≤ 2 * (N : ℝ) ^ 2 / H shifts.length +
              4 * (N : ℝ) * Real.sqrt E := add_le_add hfirst hsecond
        _ = coarseRecursiveAProcessSquaredBound
              H N C (depth + 1) shifts.length := rfl

/-- Root exponential-sum estimate after replacing the recursive tree by its
level-scheduled numerical envelope. -/
theorem norm_phaseSum_sq_le_coarseRecursiveAProcess
    (f : ℕ → ℝ) (H : ℕ → ℕ) (Q : List ℕ → ℝ)
    (N : ℕ) (C : ℝ) (depth : ℕ)
    (hvalid : RecursiveAProcessValid
      f (fun s ↦ H s.length) Q N depth [])
    (hleaf : ∀ s, Q s ≤ C) :
    ‖∑ n ∈ Finset.range N, phaseTerm f n‖ ^ 2 ≤
      coarseRecursiveAProcessSquaredBound H N C depth 0 := by
  calc
    ‖∑ n ∈ Finset.range N, phaseTerm f n‖ ^ 2 ≤
        recursiveAProcessSquaredBound
          (fun s ↦ H s.length) Q N depth [] :=
      norm_phaseSum_sq_le_recursiveAProcess
        f (fun s ↦ H s.length) Q N depth hvalid
    _ ≤ coarseRecursiveAProcessSquaredBound H N C depth 0 := by
      simpa using recursiveAProcessSquaredBound_le_coarse
        f H Q N C depth [] hvalid hleaf

end ZeroFreeRegion.VinogradovKorobov
