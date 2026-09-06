import HardyTheorem.SelbergMollifierNonvanishing
import HardyTheorem.SelbergPacking
import HardyTheorem.SelbergSqrtZetaSmallAbsGapBound

open Complex Filter MeasureTheory Set

namespace HardyTheorem

/-!
# Square-root-zeta Selberg good windows

This file puts the small-absolute-mass and excessive-signed-mass exceptional
sets on the same square-root-zeta mollifier.  Avoiding both sets gives strict
cancellation in the short interval, hence a local sign change of Hardy's
function.  The final theorem is the coefficient-specific assembly interface
for Selberg's odd-multiplicity lower bound.
-/

/-- The signed short integral of the square-root-zeta mollified Hardy
function. -/
noncomputable def selbergSqrtZetaSignedShortIntegral
    (X : ℕ) (H t : ℝ) : ℝ :=
  ∫ u in t..t + H, selbergSqrtZetaMollifiedHardyZ X u

/-- Starts where the signed square-root-zeta mollified mass is too large. -/
def selbergSqrtZetaExcessiveSignedMassStarts
    (X : ℕ) (H eta : ℝ) : Set ℝ :=
  {t | eta ≤ |selbergSqrtZetaSignedShortIntegral X H t|}

/-- Starts avoiding both square-root-zeta exceptional sets. -/
def selbergSqrtZetaGoodWindowStarts
    (X : ℕ) (H eta : ℝ) : Set ℝ :=
  (selbergSqrtZetaSmallAbsoluteMassStarts X H eta ∪
    selbergSqrtZetaExcessiveSignedMassStarts X H eta)ᶜ

/-- The square-root-zeta mollified Hardy function is continuous. -/
theorem continuous_selbergSqrtZetaMollifiedHardyZ (X : ℕ) :
    Continuous (selbergSqrtZetaMollifiedHardyZ X) := by
  change Continuous (fun t : ℝ => selbergSqrtZetaMollifiedHardyZ X t)
  simpa only [selbergSqrtZetaMollifiedHardyZ] using
    continuous_selbergMollifiedHardyZ X
      (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))

/-- The square-root-zeta mollified Hardy function is nonzero somewhere in
every nonempty interval. -/
theorem exists_selbergSqrtZetaMollifiedHardyZ_ne_zero_Ioo
    (X : ℕ) (hX : 1 ≤ X) {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Set.Ioo a b, selbergSqrtZetaMollifiedHardyZ X t ≠ 0 := by
  simpa only [selbergSqrtZetaMollifiedHardyZ] using
    exists_selbergMollifiedHardyZ_ne_zero_Ioo X
      (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))
      hX (by simp) hab

/-- A square-root-zeta good start gives strict cancellation and therefore a
local sign change of the mollified Hardy function. -/
theorem exists_selbergSqrtZetaMollifiedHardyZ_localSignChange_of_goodStart
    {X : ℕ} (hX : 1 ≤ X) {H eta t : ℝ} (hH : 0 ≤ H)
    (ht : t ∈ selbergSqrtZetaGoodWindowStarts X H eta) :
    ∃ u ∈ Set.Ioo t (t + H),
      HasLocalSignChangeAt (selbergSqrtZetaMollifiedHardyZ X) u := by
  have hnot := ht
  rw [selbergSqrtZetaGoodWindowStarts, Set.mem_compl_iff,
    Set.mem_union] at hnot
  have hparts := not_or.mp hnot
  have hnotSmall :
      ¬ selbergSqrtZetaAbsShortIntegral X H t ≤ eta := by
    simpa only [selbergSqrtZetaSmallAbsoluteMassStarts,
      Set.mem_setOf_eq] using hparts.1
  have hnotExcessive :
      ¬ eta ≤ |selbergSqrtZetaSignedShortIntegral X H t| := by
    simpa only [selbergSqrtZetaExcessiveSignedMassStarts,
      Set.mem_setOf_eq] using hparts.2
  have hstrict :
      |selbergSqrtZetaSignedShortIntegral X H t| <
        selbergSqrtZetaAbsShortIntegral X H t :=
    (lt_of_not_ge hnotExcessive).trans (lt_of_not_ge hnotSmall)
  have hchange :=
    MathlibAux.exists_local_sign_change_of_abs_intervalIntegral_lt_intervalIntegral_abs
      (continuous_selbergSqrtZetaMollifiedHardyZ X)
      (show t ≤ t + H by linarith)
      (by simpa only [selbergSqrtZetaSignedShortIntegral,
          selbergSqrtZetaAbsShortIntegral] using hstrict)
      (fun a b hab =>
        exists_selbergSqrtZetaMollifiedHardyZ_ne_zero_Ioo X hX hab)
  simpa only [HasLocalSignChangeAt, HasNegToPosLocalSignChangeAt,
    HasPosToNegLocalSignChangeAt] using hchange

/-- A square-root-zeta good window contains a local sign change of Hardy's
unmollified `Z` function. -/
theorem exists_hardyZ_localSignChange_of_selbergSqrtZetaGoodStart
    {X : ℕ} (hX : 1 ≤ X) {H eta t : ℝ} (hH : 0 ≤ H)
    (ht : t ∈ selbergSqrtZetaGoodWindowStarts X H eta) :
    ∃ u ∈ Set.Ioo t (t + H), HasLocalSignChangeAt hardyZ u := by
  obtain ⟨u, hu, hchange⟩ :=
    exists_selbergSqrtZetaMollifiedHardyZ_localSignChange_of_goodStart
      hX hH ht
  exact ⟨u, hu, hasLocalSignChangeAt_hardyZ_of_mollified hchange⟩

/-- The two square-root-zeta bad-set estimates at logarithmic window length
imply Selberg's odd-multiplicity lower-bound target. -/
theorem selberg_odd_zero_proportion_target_of_sqrtZeta_good_window_bounds
    (A T0 : ℝ) (X : ℝ → ℕ) (eta : ℝ → ℝ) (hA : 0 < A)
    (hX : ∀ T ≥ T0, 1 ≤ X T)
    (hsmall : ∀ T ≥ T0,
      volume.real
          (Set.Icc T (2 * T - A / Real.log T) ∩
            selbergSqrtZetaSmallAbsoluteMassStarts
              (X T) (A / Real.log T) (eta T)) ≤ T / 24)
    (hexcessive : ∀ T ≥ T0,
      volume.real
          (Set.Icc T (2 * T - A / Real.log T) ∩
            selbergSqrtZetaExcessiveSignedMassStarts
              (X T) (A / Real.log T) (eta T)) ≤ T / 24) :
    selberg_odd_zero_proportion_target := by
  let T1 : ℝ := max T0 (Real.exp 1)
  let good : ℝ → Set ℝ := fun T =>
    selbergSqrtZetaGoodWindowStarts
      (X T) (A / Real.log T) (eta T)
  apply selberg_odd_zero_proportion_target_of_log_good_window_measure
    A T1 good hA
  · intro T hT
    have hT0 : T0 ≤ T := (le_max_left _ _).trans hT
    let I : Set ℝ := Set.Icc T (2 * T - A / Real.log T)
    let small : Set ℝ :=
      selbergSqrtZetaSmallAbsoluteMassStarts
        (X T) (A / Real.log T) (eta T)
    let excessive : Set ℝ :=
      selbergSqrtZetaExcessiveSignedMassStarts
        (X T) (A / Real.log T) (eta T)
    have hsubset :
        I \ good T ⊆ (I ∩ small) ∪ (I ∩ excessive) := by
      intro t ht
      rcases ht with ⟨htI, htbad⟩
      change t ∉ (small ∪ excessive)ᶜ at htbad
      simp only [Set.mem_compl_iff, Set.mem_union, not_not] at htbad
      rcases htbad with htSmall | htExcessive
      · exact Or.inl ⟨htI, htSmall⟩
      · exact Or.inr ⟨htI, htExcessive⟩
    have hunion_ne_top :
        volume ((I ∩ small) ∪ (I ∩ excessive)) ≠ ⊤ := by
      apply measure_ne_top_of_subset
        (union_subset inter_subset_left inter_subset_left)
      simpa only [I] using
        (measure_Icc_lt_top :
          volume (Set.Icc T (2 * T - A / Real.log T)) < ⊤).ne
    have hmono :
        volume.real (I \ good T) ≤
          volume.real ((I ∩ small) ∪ (I ∩ excessive)) :=
      measureReal_mono hsubset hunion_ne_top
    calc
      volume.real
          (Set.Icc T (2 * T - A / Real.log T) \ good T) =
          volume.real (I \ good T) := by rfl
      _ ≤ volume.real ((I ∩ small) ∪ (I ∩ excessive)) := hmono
      _ ≤ volume.real (I ∩ small) + volume.real (I ∩ excessive) :=
        measureReal_union_le _ _
      _ ≤ T / 12 := by
        have hs := hsmall T hT0
        have he := hexcessive T hT0
        change volume.real (I ∩ small) ≤ T / 24 at hs
        change volume.real (I ∩ excessive) ≤ T / 24 at he
        nlinarith
  · intro T hT t ht
    have hT0 : T0 ≤ T := (le_max_left _ _).trans hT
    have hTexp : Real.exp 1 ≤ T := (le_max_right _ _).trans hT
    have hTpos : 0 < T := (Real.exp_pos 1).trans_le hTexp
    have hlogone : 1 ≤ Real.log T := by
      rw [Real.le_log_iff_exp_le hTpos]
      exact hTexp
    have hH : 0 ≤ A / Real.log T :=
      div_nonneg hA.le (zero_le_one.trans hlogone)
    exact
      exists_hardyZ_localSignChange_of_selbergSqrtZetaGoodStart
        (hX T hT0) hH ht.1

end HardyTheorem
