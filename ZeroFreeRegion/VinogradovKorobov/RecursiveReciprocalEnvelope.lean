import ZeroFreeRegion.VinogradovKorobov.AProcessSchedule

namespace ZeroFreeRegion.VinogradovKorobov

/-- Squared child bounds with reciprocal shift decay propagate through one
A-process step with the harmonic `(1 + log L) / L` gain. -/
theorem aProcessSquaredBound_le_of_sq_reciprocal
    (Q : ℕ → ℝ) (C : ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N) (hC : 0 ≤ C)
    (hQ : ∀ ell ∈ Finset.Icc 1 (L - 1),
      Q ell ≤ (C * (ell : ℝ)⁻¹) ^ 2) :
    aProcessSquaredBound (fun ell ↦ Real.sqrt (Q ell)) N L ≤
      2 * (N : ℝ) ^ 2 / L +
        4 * (N : ℝ) * C * (1 + Real.log L) / L := by
  apply aProcessSquaredBound_le_reciprocal
    (fun ell ↦ Real.sqrt (Q ell)) C N L hL hLN hC
  · intro ell hell
    exact Real.sqrt_nonneg _
  · intro ell hell
    apply (Real.sqrt_le_iff).2
    refine ⟨mul_nonneg hC (inv_nonneg.mpr (Nat.cast_nonneg ell)), ?_⟩
    exact hQ ell hell

/-- Scale-aware one-step propagation.  If the squared child at shift `ell`,
after multiplication by the accumulated scale `(ell * P)^2`, is at most `E`,
then the parent bound retains one factor of `P` in the off-diagonal term. -/
theorem aProcessSquaredBound_mul_sq_le_of_scaled_children
    (Q : ℕ → ℝ) (E P : ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N) (hE : 0 ≤ E) (hP : 0 < P)
    (hQ : ∀ ell ∈ Finset.Icc 1 (L - 1),
      Q ell * ((ell : ℝ) * P) ^ 2 ≤ E) :
    aProcessSquaredBound (fun ell ↦ Real.sqrt (Q ell)) N L * P ^ 2 ≤
      2 * (N : ℝ) ^ 2 * P ^ 2 / L +
        4 * (N : ℝ) * Real.sqrt E * P * (1 + Real.log L) / L := by
  have hbase := aProcessSquaredBound_le_of_sq_reciprocal
    Q (Real.sqrt E * P⁻¹) N L hL hLN
    (mul_nonneg (Real.sqrt_nonneg E) (inv_nonneg.mpr hP.le)) (by
      intro ell hell
      have hellPos : 0 < ell := by
        exact (Finset.mem_Icc.mp hell).1
      have hellReal : (0 : ℝ) < (ell : ℝ) := Nat.cast_pos.mpr hellPos
      have hden : (ell : ℝ) * P ≠ 0 := mul_ne_zero hellReal.ne' hP.ne'
      calc
        Q ell = Q ell * (((ell : ℝ) * P) ^ 2) /
            (((ell : ℝ) * P) ^ 2) := by field_simp
        _ ≤ E / (((ell : ℝ) * P) ^ 2) :=
          div_le_div_of_nonneg_right (hQ ell hell)
            (sq_nonneg ((ell : ℝ) * P))
        _ = (Real.sqrt E * P⁻¹ * (ell : ℝ)⁻¹) ^ 2 := by
          nth_rewrite 1 [← Real.sq_sqrt hE]
          field_simp [hden, hP.ne', hellReal.ne'])
  calc
    aProcessSquaredBound (fun ell ↦ Real.sqrt (Q ell)) N L * P ^ 2 ≤
        (2 * (N : ℝ) ^ 2 / L +
          4 * (N : ℝ) * (Real.sqrt E * P⁻¹) *
            (1 + Real.log L) / L) * P ^ 2 :=
      mul_le_mul_of_nonneg_right hbase (sq_nonneg P)
    _ = 2 * (N : ℝ) ^ 2 * P ^ 2 / L +
        4 * (N : ℝ) * Real.sqrt E * P * (1 + Real.log L) / L := by
      field_simp

/-- Level-scheduled A-process envelope that retains the accumulated shift
product.  Unlike the coarse envelope, its off-diagonal term keeps the
harmonic gain created by reciprocal child decay. -/
noncomputable def refinedRecursiveAProcessSquaredBound
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => C
  | depth + 1, level =>
      2 * (N : ℝ) ^ 2 * (aProcessScheduleProduct H level : ℝ) ^ 2 /
          H level +
        4 * (N : ℝ) * Real.sqrt
            (refinedRecursiveAProcessSquaredBound H N C depth (level + 1)) *
          (aProcessScheduleProduct H level : ℝ) *
          (1 + Real.log (H level)) / H level

@[simp] lemma refinedRecursiveAProcessSquaredBound_zero
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ) (level : ℕ) :
    refinedRecursiveAProcessSquaredBound H N C 0 level = C := rfl

@[simp] lemma refinedRecursiveAProcessSquaredBound_succ
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ) (depth level : ℕ) :
    refinedRecursiveAProcessSquaredBound H N C (depth + 1) level =
      2 * (N : ℝ) ^ 2 * (aProcessScheduleProduct H level : ℝ) ^ 2 /
          H level +
        4 * (N : ℝ) * Real.sqrt
            (refinedRecursiveAProcessSquaredBound H N C depth (level + 1)) *
          (aProcessScheduleProduct H level : ℝ) *
          (1 + Real.log (H level)) / H level := rfl

/-- The refined numerical recurrence is nonnegative for nonnegative terminal
data, including at unused schedule levels where `H level = 0`. -/
theorem refinedRecursiveAProcessSquaredBound_nonneg
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ) (depth level : ℕ) (hC : 0 ≤ C) :
    0 ≤ refinedRecursiveAProcessSquaredBound H N C depth level := by
  induction depth generalizing level with
  | zero => exact hC
  | succ depth ih =>
      rw [refinedRecursiveAProcessSquaredBound_succ]
      have hHnonneg : 0 ≤ (H level : ℝ) := Nat.cast_nonneg _
      have hlog : 0 ≤ Real.log (H level : ℝ) := by
        by_cases hzero : H level = 0
        · simp [hzero]
        · exact Real.log_nonneg (by
            exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hzero))
      have hnext :
          0 ≤ refinedRecursiveAProcessSquaredBound
            H N C depth (level + 1) := ih (level + 1)
      have hharm : 0 ≤ 1 + Real.log (H level : ℝ) := by linarith
      apply add_nonneg
      · exact div_nonneg (by positivity) hHnonneg
      · exact div_nonneg (by positivity) hHnonneg

/-- Arbitrary-depth propagation of product-sensitive leaf estimates through
a complete recursive A-process tree. -/
theorem recursiveAProcessSquaredBound_mul_prod_sq_le_refined
    (f : ℕ → ℝ) (H : ℕ → ℕ) (Q : List ℕ → ℝ)
    (N depth : ℕ) (C : ℝ) (shifts : List ℕ)
    (hC : 0 ≤ C)
    (hvalid : RecursiveAProcessValid
      f (fun s ↦ H s.length) Q N depth shifts)
    (hleaf : ∀ s, (∀ h ∈ s, 0 < h) → Q s * (s.prod : ℝ) ^ 2 ≤ C)
    (hprod : shifts.prod ≤ aProcessScheduleProduct H shifts.length)
    (hshifts : ∀ h ∈ shifts, 0 < h) :
    recursiveAProcessSquaredBound
        (fun s ↦ H s.length) Q N depth shifts * (shifts.prod : ℝ) ^ 2 ≤
      refinedRecursiveAProcessSquaredBound H N C depth shifts.length := by
  induction depth generalizing shifts with
  | zero =>
      exact hleaf shifts hshifts
  | succ depth ih =>
      rcases hvalid with ⟨hHL, hHLR, hchildren⟩
      let R := remainingAProcessLength N shifts
      let P : ℝ := shifts.prod
      let E := refinedRecursiveAProcessSquaredBound
        H N C depth (shifts.length + 1)
      have hPpos : 0 < P := by
        dsimp only [P]
        exact_mod_cast (show 0 < shifts.prod by exact List.prod_pos hshifts)
      have hE : 0 ≤ E := by
        exact refinedRecursiveAProcessSquaredBound_nonneg
          H N C depth (shifts.length + 1) hC
      have hstep :
          aProcessSquaredBound
              (fun ell ↦ Real.sqrt
                (recursiveAProcessSquaredBound
                  (fun s ↦ H s.length) Q N depth (ell :: shifts)))
              R (H shifts.length) * P ^ 2 ≤
            2 * (R : ℝ) ^ 2 * P ^ 2 / H shifts.length +
              4 * (R : ℝ) * Real.sqrt E * P *
                (1 + Real.log (H shifts.length)) / H shifts.length := by
        apply aProcessSquaredBound_mul_sq_le_of_scaled_children
          _ E P R (H shifts.length) hHL hHLR hE hPpos
        intro ell hell
        have hellBounds := Finset.mem_Icc.mp hell
        have hellPos : 0 < ell := hellBounds.1
        have hellH : ell ≤ H shifts.length := by omega
        have hchildProd : (ell :: shifts).prod ≤
            aProcessScheduleProduct H (ell :: shifts).length := by
          simp only [List.prod_cons, List.length_cons,
            aProcessScheduleProduct_succ]
          simpa only [Nat.mul_comm] using Nat.mul_le_mul hellH hprod
        have hchildShifts : ∀ h ∈ ell :: shifts, 0 < h := by
          intro h hh
          rcases (List.mem_cons.mp hh) with rfl | hh
          · exact hellPos
          · exact hshifts h hh
        simpa only [List.prod_cons, Nat.cast_mul, E, List.length_cons,
          mul_assoc] using
          ih (ell :: shifts) (hchildren ell hell) hchildProd hchildShifts
      have hRN : R ≤ N := by
        simpa only [R, remainingAProcessLength] using Nat.sub_le N shifts.sum
      have hPR : P ≤ (aProcessScheduleProduct H shifts.length : ℝ) := by
        dsimp only [P]
        exact_mod_cast hprod
      have hHpos : 0 < (H shifts.length : ℝ) :=
        Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hHL)
      have hharm : 0 ≤ 1 + Real.log (H shifts.length : ℝ) := by
        have hlog : 0 ≤ Real.log (H shifts.length : ℝ) :=
          Real.log_nonneg (by exact_mod_cast hHL)
        linarith
      have hfirst :
          2 * (R : ℝ) ^ 2 * P ^ 2 / H shifts.length ≤
            2 * (N : ℝ) ^ 2 *
              (aProcessScheduleProduct H shifts.length : ℝ) ^ 2 /
                H shifts.length := by
        apply div_le_div_of_nonneg_right _ hHpos.le
        gcongr
      have hsecond :
          4 * (R : ℝ) * Real.sqrt E * P *
              (1 + Real.log (H shifts.length)) / H shifts.length ≤
            4 * (N : ℝ) * Real.sqrt E *
              (aProcessScheduleProduct H shifts.length : ℝ) *
              (1 + Real.log (H shifts.length)) / H shifts.length := by
        apply div_le_div_of_nonneg_right _ hHpos.le
        gcongr
      calc
        recursiveAProcessSquaredBound
            (fun s ↦ H s.length) Q N (depth + 1) shifts *
              (shifts.prod : ℝ) ^ 2 =
            aProcessSquaredBound
              (fun ell ↦ Real.sqrt
                (recursiveAProcessSquaredBound
                  (fun s ↦ H s.length) Q N depth (ell :: shifts)))
              R (H shifts.length) * P ^ 2 := rfl
        _ ≤ 2 * (R : ℝ) ^ 2 * P ^ 2 / H shifts.length +
              4 * (R : ℝ) * Real.sqrt E * P *
                (1 + Real.log (H shifts.length)) / H shifts.length := hstep
        _ ≤ 2 * (N : ℝ) ^ 2 *
                (aProcessScheduleProduct H shifts.length : ℝ) ^ 2 /
                H shifts.length +
              4 * (N : ℝ) * Real.sqrt E *
                (aProcessScheduleProduct H shifts.length : ℝ) *
                (1 + Real.log (H shifts.length)) / H shifts.length :=
          add_le_add hfirst hsecond
        _ = refinedRecursiveAProcessSquaredBound
              H N C (depth + 1) shifts.length := rfl

/-- The product-sensitive zeta leaf envelope becomes exactly the uniform
leaf coefficient after restoring the square of the path product. -/
theorem zetaAProcessProductLeafSquaredBound_mul_prod_sq
    (t : ℝ) (m N depth : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hshifts : ∀ h ∈ shifts, 0 < h) :
    zetaAProcessProductLeafSquaredBound t m N depth shifts *
        (shifts.prod : ℝ) ^ 2 =
      zetaAProcessUniformLeafSquaredBound t m N depth := by
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

/-- A scale-valid zeta tree can use the path-sensitive product leaf envelope
at every terminal node. -/
theorem recursiveZetaAProcessScaleValid_to_productGeneric
    (t : ℝ) (m N totalDepth depth : ℕ) (H : ℕ → ℕ)
    (shifts : List ℕ) (ht : 0 < t) (hm : 0 < m)
    (hlen : shifts.length + depth = totalDepth)
    (hvalid : RecursiveZetaAProcessScaleValid
      t m (fun s ↦ H s.length) N depth shifts) :
    RecursiveAProcessValid (shiftedZetaPhase t m) (fun s ↦ H s.length)
      (zetaAProcessProductLeafSquaredBound t m N totalDepth)
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
      exact hactual.trans (zetaAProcessLeafSquaredBound_le_product
        t m N totalDepth shifts ht hm hR hshifts hdepth)
  | succ depth ih =>
      rcases hvalid with ⟨hH, hHR, hchildren⟩
      refine ⟨hH, hHR, ?_⟩
      intro ell hell
      have hchildLen : (ell :: shifts).length + depth = totalDepth := by
        simp only [List.length_cons]
        omega
      exact ih (ell :: shifts) hchildLen (hchildren ell hell)

/-- Product-sensitive arbitrary-depth zeta exponential-sum estimate under
the explicit scale-valid recursive tree conditions. -/
theorem norm_zetaPhase_sum_sq_le_refinedRecursiveAProcess_of_scale
    (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : RecursiveZetaAProcessScaleValid
      t m (fun s ↦ H s.length) N depth []) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      refinedRecursiveAProcessSquaredBound H N
        (zetaAProcessUniformLeafSquaredBound t m N depth) depth 0 := by
  have hgeneric := recursiveZetaAProcessScaleValid_to_productGeneric
    t m N depth depth H [] ht hm (by simp) hvalid
  have hrefined := recursiveAProcessSquaredBound_mul_prod_sq_le_refined
    (shiftedZetaPhase t m) H
    (zetaAProcessProductLeafSquaredBound t m N depth) N depth
    (zetaAProcessUniformLeafSquaredBound t m N depth) []
    (sq_nonneg _) hgeneric
    (fun s hs ↦ (zetaAProcessProductLeafSquaredBound_mul_prod_sq
      t m N depth s ht hm hs).le)
    (by simp) (by simp)
  exact (norm_phaseSum_sq_le_recursiveAProcess
    (shiftedZetaPhase t m) (fun s ↦ H s.length)
    (zetaAProcessProductLeafSquaredBound t m N depth) N depth hgeneric).trans
      (by simpa using hrefined)

/-- A valid level schedule yields the refined product-sensitive root bound. -/
theorem norm_zetaPhase_sum_sq_le_scheduledRefinedRecursiveAProcess
    (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : ZetaAProcessScheduleValid t m N depth H) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      refinedRecursiveAProcessSquaredBound H N
        (zetaAProcessUniformLeafSquaredBound t m N depth) depth 0 := by
  apply norm_zetaPhase_sum_sq_le_refinedRecursiveAProcess_of_scale
    t m N depth H ht hm
  exact recursiveZetaAProcessScaleValid_of_schedule
    t m N depth H ht hm hvalid

end ZeroFreeRegion.VinogradovKorobov
