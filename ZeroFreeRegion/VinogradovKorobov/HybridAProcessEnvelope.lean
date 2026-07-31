import ZeroFreeRegion.VinogradovKorobov.AProcessSchedule

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- Terminal numerical envelope that keeps the better of the trivial bound
and reciprocal accumulated-product decay. -/
noncomputable def hybridProductLeafSquaredEnvelope
    (N : ℕ) (C P : ℝ) : ℝ :=
  min ((N : ℝ) ^ 2) (C / P ^ 2)

/-- The geometric-mean interpolation of the trivial and reciprocal-product
leaf bounds produces one full inverse power of the accumulated product. -/
theorem hybridProductLeafSquaredEnvelope_le_power
    (N : ℕ) (C P : ℝ) (hC : 0 ≤ C) (hP : 0 < P) :
    hybridProductLeafSquaredEnvelope N C P ≤
      (N : ℝ) * Real.sqrt C * P⁻¹ := by
  let A : ℝ := (N : ℝ) ^ 2
  let B : ℝ := C / P ^ 2
  have hA : 0 ≤ A := sq_nonneg _
  have hB : 0 ≤ B := div_nonneg hC (sq_nonneg P)
  have hgeom : min A B ≤ Real.sqrt (A * B) := by
    rcases le_total A B with hAB | hBA
    · rw [min_eq_left hAB]
      apply (Real.le_sqrt hA (mul_nonneg hA hB)).2
      simpa only [pow_two, mul_assoc] using
        mul_le_mul_of_nonneg_left hAB hA
    · rw [min_eq_right hBA]
      apply (Real.le_sqrt hB (mul_nonneg hA hB)).2
      calc
        B ^ 2 = B * B := by ring
        _ ≤ A * B := mul_le_mul_of_nonneg_right hBA hB
  unfold hybridProductLeafSquaredEnvelope
  change min A B ≤ (N : ℝ) * Real.sqrt C * P⁻¹
  calc
    min A B ≤ Real.sqrt (A * B) := hgeom
    _ = (N : ℝ) * Real.sqrt C * P⁻¹ := by
      dsimp only [A, B]
      rw [Real.sqrt_mul (sq_nonneg (N : ℝ)),
        Real.sqrt_sq (Nat.cast_nonneg N), Real.sqrt_div hC,
        Real.sqrt_sq hP.le]
      rw [div_eq_mul_inv]
      ring

/-- A level-scheduled A-process envelope whose state retains the accumulated
product of all shifts on the current path. -/
noncomputable def hybridProductRecursiveAProcessSquaredBound
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, _, P => hybridProductLeafSquaredEnvelope N C P
  | depth + 1, level, P =>
      aProcessSquaredBound
        (fun ell ↦ Real.sqrt
          (hybridProductRecursiveAProcessSquaredBound H N C depth
            (level + 1) ((ell : ℝ) * P)))
        N (H level)

@[simp] lemma hybridProductRecursiveAProcessSquaredBound_zero
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ) (level : ℕ) (P : ℝ) :
    hybridProductRecursiveAProcessSquaredBound H N C 0 level P =
      hybridProductLeafSquaredEnvelope N C P := rfl

@[simp] lemma hybridProductRecursiveAProcessSquaredBound_succ
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ) (depth level : ℕ) (P : ℝ) :
    hybridProductRecursiveAProcessSquaredBound H N C (depth + 1) level P =
      aProcessSquaredBound
        (fun ell ↦ Real.sqrt
          (hybridProductRecursiveAProcessSquaredBound H N C depth
            (level + 1) ((ell : ℝ) * P)))
        N (H level) := rfl

/-- The reciprocal-product leaf bound is the uniform coefficient divided by
the square of the accumulated positive shift product. -/
theorem zetaAProcessProductLeafSquaredBound_eq_div_prod_sq
    (t : ℝ) (m N depth : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hshifts : ∀ h ∈ shifts, 0 < h) :
    zetaAProcessProductLeafSquaredBound t m N depth shifts =
      zetaAProcessUniformLeafSquaredBound t m N depth /
        (shifts.prod : ℝ) ^ 2 := by
  have hprod : (shifts.prod : ℝ) ≠ 0 := by
    exact_mod_cast (show shifts.prod ≠ 0 by
      exact ne_of_gt (List.prod_pos hshifts))
  have hdelta : zetaAProcessUniformLeafDeltaLower t m N depth ≠ 0 := by
    unfold zetaAProcessUniformLeafDeltaLower
    have hmN : 0 < ((m + N : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    positivity
  unfold zetaAProcessProductLeafSquaredBound
    zetaAProcessUniformLeafSquaredBound
  field_simp

/-- Every path-sensitive zeta leaf is controlled by the product-state
terminal envelope with the root length replacing the shorter leaf length. -/
theorem zetaAProcessHybridProductLeafSquaredBound_le_envelope
    (t : ℝ) (m N depth : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hshifts : ∀ h ∈ shifts, 0 < h) :
    zetaAProcessHybridProductLeafSquaredBound t m N depth shifts ≤
      hybridProductLeafSquaredEnvelope N
        (zetaAProcessUniformLeafSquaredBound t m N depth)
        (shifts.prod : ℝ) := by
  unfold zetaAProcessHybridProductLeafSquaredBound
    hybridProductLeafSquaredEnvelope
  apply min_le_min
  · have hRnat : remainingAProcessLength N shifts ≤ N := by
      unfold remainingAProcessLength
      omega
    have hR : (remainingAProcessLength N shifts : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hRnat
    gcongr
  · rw [zetaAProcessProductLeafSquaredBound_eq_div_prod_sq
      t m N depth shifts ht hm hshifts]

/-- Product-state numerical propagation through an arbitrary valid recursive
A-process tree. -/
theorem recursiveAProcessSquaredBound_le_hybridProductEnvelope
    (f : ℕ → ℝ) (H : ℕ → ℕ) (Q : List ℕ → ℝ)
    (N : ℕ) (C : ℝ) (depth : ℕ) (shifts : List ℕ)
    (hvalid : RecursiveAProcessValid
      f (fun s ↦ H s.length) Q N depth shifts)
    (hleaf : ∀ s, (∀ h ∈ s, 0 < h) →
      Q s ≤ hybridProductLeafSquaredEnvelope N C (s.prod : ℝ))
    (hshifts : ∀ h ∈ shifts, 0 < h) :
    recursiveAProcessSquaredBound (fun s ↦ H s.length) Q N depth shifts ≤
      hybridProductRecursiveAProcessSquaredBound H N C depth
        shifts.length (shifts.prod : ℝ) := by
  induction depth generalizing shifts with
  | zero =>
      exact hleaf shifts hshifts
  | succ depth ih =>
      rcases hvalid with ⟨hH, hHR, hchildren⟩
      let R := remainingAProcessLength N shifts
      have hRN : R ≤ N := by
        dsimp only [R, remainingAProcessLength]
        omega
      have hmono :
          aProcessSquaredBound
              (fun ell ↦ Real.sqrt
                (recursiveAProcessSquaredBound
                  (fun s ↦ H s.length) Q N depth (ell :: shifts)))
              R (H shifts.length) ≤
            aProcessSquaredBound
              (fun ell ↦ Real.sqrt
                (hybridProductRecursiveAProcessSquaredBound H N C depth
                  (shifts.length + 1) ((ell : ℝ) * (shifts.prod : ℝ))))
              N (H shifts.length) := by
        apply aProcessSquaredBound_mono
          _ _ R N (H shifts.length) hH hRN
        · intro ell hell
          exact Real.sqrt_nonneg _
        · intro ell hell
          exact Real.sqrt_nonneg _
        · intro ell hell
          apply Real.sqrt_le_sqrt
          have hellPos : 0 < ell := (Finset.mem_Icc.mp hell).1
          have hchildShifts : ∀ h ∈ ell :: shifts, 0 < h := by
            intro h hh
            rcases List.mem_cons.mp hh with rfl | hh
            · exact hellPos
            · exact hshifts h hh
          simpa only [List.length_cons, List.prod_cons, Nat.cast_mul] using
            ih (ell :: shifts) (hchildren ell hell) hchildShifts
      calc
        recursiveAProcessSquaredBound
            (fun s ↦ H s.length) Q N (depth + 1) shifts =
            aProcessSquaredBound
              (fun ell ↦ Real.sqrt
                (recursiveAProcessSquaredBound
                  (fun s ↦ H s.length) Q N depth (ell :: shifts)))
              R (H shifts.length) := rfl
        _ ≤ aProcessSquaredBound
              (fun ell ↦ Real.sqrt
                (hybridProductRecursiveAProcessSquaredBound H N C depth
                  (shifts.length + 1) ((ell : ℝ) * (shifts.prod : ℝ))))
              N (H shifts.length) := hmono
        _ = hybridProductRecursiveAProcessSquaredBound H N C (depth + 1)
              shifts.length (shifts.prod : ℝ) := rfl

/-- Root zeta exponential-sum estimate with the full accumulated shift
product retained in the numerical recurrence. -/
theorem norm_zetaPhase_sum_sq_le_hybridProductEnvelope_of_scale
    (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : RecursiveZetaAProcessScaleValid
      t m (fun s ↦ H s.length) N depth []) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      hybridProductRecursiveAProcessSquaredBound H N
        (zetaAProcessUniformLeafSquaredBound t m N depth) depth 0 1 := by
  have hgeneric := recursiveZetaAProcessScaleValid_to_hybridProductGeneric
    t m N depth depth H [] ht hm (by simp) hvalid
  calc
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
        recursiveAProcessSquaredBound (fun s ↦ H s.length)
          (zetaAProcessHybridProductLeafSquaredBound t m N depth)
          N depth [] :=
      norm_phaseSum_sq_le_recursiveAProcess
        (shiftedZetaPhase t m) (fun s ↦ H s.length)
        (zetaAProcessHybridProductLeafSquaredBound t m N depth)
        N depth hgeneric
    _ ≤ hybridProductRecursiveAProcessSquaredBound H N
        (zetaAProcessUniformLeafSquaredBound t m N depth) depth 0 1 := by
      simpa using recursiveAProcessSquaredBound_le_hybridProductEnvelope
        (shiftedZetaPhase t m) H
        (zetaAProcessHybridProductLeafSquaredBound t m N depth)
        N (zetaAProcessUniformLeafSquaredBound t m N depth) depth []
        hgeneric
        (fun s hs ↦ zetaAProcessHybridProductLeafSquaredBound_le_envelope
          t m N depth s ht hm hs)
        (by simp)

end ZeroFreeRegion.VinogradovKorobov
