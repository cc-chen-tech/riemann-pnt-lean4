import HardyTheorem.ConreyEtaArgumentFactors
import HardyTheorem.ConreyV1HorizontalArgument
import HardyTheorem.ConreyMollifiedContourCount
import HardyTheorem.ConreyEquation37Edges

/-! Finite-height quantitative eta argument on the original three edges.
The long product supplies only horizontal nonvanishing. Auxiliary cutoff
two controls V1, without changing the parameters of any mean-square integral. -/

open Complex Set MeasureTheory

namespace HardyTheorem

private theorem eta_horizontal_split {g g0 g1 L A t : ℝ}
    (hA : (1 / 2 : ℝ) ≤ A) (ht : 0 < t)
    (hne : ∀ x ∈ Icc (1 / 2 : ℝ) A, conreyDegreeOneV1 g g0 g1 L ((x : ℂ) + I * t) ≠ 0) :
    (∫ x in (1 / 2 : ℝ)..A, (logDeriv (conreyDegreeOneEta g g0 g1 L) ((x : ℂ) + I * t)).im) =
      (∫ x in (1 / 2 : ℝ)..A, (logDeriv conreyH ((x : ℂ) + I * t)).im) +
      ∫ x in (1 / 2 : ℝ)..A, (logDeriv (conreyDegreeOneV1 g g0 g1 L) ((x : ℂ) + I * t)).im := by
  apply integral_projection_logDeriv_conreyEta_eq_add Complex.imCLM
  · fun_prop
  · intro x hx
    rw [uIcc_of_le hA] at hx
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      zero_mul, mul_zero, sub_self, add_zero]
    linarith [hx.1]
  · intro x _ he
    have hi := congrArg Complex.im he
    simp at hi
    linarith
  · intro x hx
    rw [uIcc_of_le hA] at hx
    exact hne x hx

private theorem eta_vertical_split {g g0 g1 L A U T : ℝ}
    (hA : 0 < A) (hU : 0 < U) (hUT : U ≤ T)
    (hne : ∀ t ∈ Icc U T, conreyDegreeOneV1 g g0 g1 L ((A : ℂ) + I * t) ≠ 0) :
    (∫ t in U..T, (logDeriv (conreyDegreeOneEta g g0 g1 L) ((A : ℂ) + I * t)).re) =
      (∫ t in U..T, (logDeriv conreyH ((A : ℂ) + I * t)).re) +
      ∫ t in U..T, (logDeriv (conreyDegreeOneV1 g g0 g1 L) ((A : ℂ) + I * t)).re := by
  apply integral_projection_logDeriv_conreyEta_eq_add Complex.reCLM
  · fun_prop
  · intro t _
    simpa using hA
  · intro t ht he
    rw [uIcc_of_le hUT] at ht
    have hi := congrArg Complex.im he
    simp at hi
    linarith [ht.1]
  · intro t ht
    exact hne t (by simpa [uIcc_of_le hUT] using ht)

/-- Explicit finite-height lower expression for eta's three-edge argument.
This retains the integral main term and every H/V1 error contribution. -/
noncomputable def conreyEtaThreeEdgeLowerMain (L U T : ℝ) : ℝ :=
  (∫ t in U..T, Real.log (t / (2 * Real.pi))) / 2 - 8 * (T - U) -
    (2 * Real.log L - 1 / 2) *
      (conreyHorizontalJensenArchimedeanConstant *
        (1 + Real.log (conreyHorizontalJensenHeightBase L (2 * Real.log L + 1) + 2)) +
       conreyHorizontalJensenArchimedeanConstant *
        (1 + Real.log (conreyHorizontalJensenHeightBase L (Real.exp L - 1) + 2))) -
    2200000000000 * L ^ 7 - Real.pi

/-- The full finite-height eta lower bound for any original admissible
long-product heights. No new height is chosen, and no moment asymptotic,
right-edge nonvanishing, or eta decomposition is supplied by the caller. -/
theorem exists_conreyEta_threeEdgeArgument_lower_bound :
    ∃ L0 : ℝ, 40000 ≤ L0 ∧ ∀ {Y : ℕ} {L sigma0 U T : ℝ},
      L0 ≤ L → sigma0 ≤ 1 / 2 →
      U ∈ Icc (2 * Real.log L + 1) (2 * Real.log L + 2) →
      T ∈ Icc (Real.exp L - 1) (Real.exp L) → U < T →
      (∀ x ∈ Icc sigma0 (2 * Real.log L),
        conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y sigma0
          conreyExplicitP ((x : ℂ) + I * U) ≠ 0) →
      (∀ x ∈ Icc sigma0 (2 * Real.log L),
        conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y sigma0
          conreyExplicitP ((x : ℂ) + I * T) ≠ 0) →
      conreyEtaThreeEdgeLowerMain L U T ≤
        conreyEtaThreeEdgeArgument (49 / 100) 0 (51 / 50) L (2 * Real.log L) U T := by
  obtain ⟨L0, hL0, hhorizontal⟩ := exists_conreyV1_horizontalArgument_le_coarse
  refine ⟨L0, hL0, ?_⟩
  intro Y L sigma0 U T hlarge hsigma hU hT hUT hbottom htop
  have hL : 40000 ≤ L := hL0.trans hlarge
  have hA : (1 / 2 : ℝ) ≤ 2 * Real.log L := by
    linarith [two_le_log_of_forty_thousand_le hL]
  have hA1 : 1 < 2 * Real.log L := by
    linarith [two_le_log_of_forty_thousand_le hL]
  have hU2 : 2 ≤ U := by linarith [hU.1]
  have hUpos : 0 < U := by linarith
  have hTpos : 0 < T := hUpos.trans hUT
  have hAU : 2 * Real.log L ≤ U := by linarith [hU.1]
  have hVbottom : ∀ x ∈ Icc (1 / 2 : ℝ) (2 * Real.log L),
      conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L ((x : ℂ) + I * U) ≠ 0 := by
    intro x hx he
    apply hbottom x ⟨hsigma.trans hx.1, hx.2⟩
    simp [conreyMollifiedDegreeOneV1, he]
  have hVtop : ∀ x ∈ Icc (1 / 2 : ℝ) (2 * Real.log L),
      conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L ((x : ℂ) + I * T) ≠ 0 := by
    intro x hx he
    apply htop x ⟨hsigma.trans hx.1, hx.2⟩
    simp [conreyMollifiedDegreeOneV1, he]
  have hsep := conreyHorizontalRightEdge_add_three_lt_exp hL
  dsimp [conreyHorizontalRightEdge] at hsep
  have hbwindow : U ∈ Icc (2 * Real.log L + 1) ((2 * Real.log L + 1) + 1) := by
    constructor <;> linarith [hU.1, hU.2]
  have htwindow : T ∈ Icc (Real.exp L - 1) ((Real.exp L - 1) + 1) := by
    constructor <;> linarith [hT.1, hT.2]
  have hbupper : (2 * Real.log L + 1) + 1 ≤ Real.exp L := by linarith
  have htbase : 2 * Real.log L + 1 ≤ Real.exp L - 1 := by linarith
  have htupper : (Real.exp L - 1) + 1 ≤ Real.exp L := by linarith
  have hVB := hhorizontal hlarge le_rfl hbupper hbwindow hVbottom
  have hVT := hhorizontal hlarge htbase htupper htwindow hVtop
  have hHB := conreyH_horizontalArgument_bound hL le_rfl hbwindow
  dsimp only [conreyHorizontalRightEdge] at hHB
  have hHT := conreyH_horizontalArgument_bound hL htbase htwindow
  have hVR := conreyV1_right_nonzero_and_argument_bound hL (by linarith) hUT.le hT.2
  have hHR := conreyH_rightArgument_mainTerm_bound hA1 hU2 hAU hUT.le
  have hBsplit := eta_horizontal_split hA hUpos hVbottom
  have hTsplit := eta_horizontal_split hA hTpos hVtop
  have hRsplit := eta_vertical_split (by linarith : 0 < 2 * Real.log L) hUpos hUT.le hVR.1
  unfold conreyEtaThreeEdgeArgument
  rw [hBsplit, hRsplit, hTsplit]
  dsimp [conreyEtaThreeEdgeLowerMain]
  have hHBlower := (abs_le.mp hHB).1
  have hHTupper := (abs_le.mp hHT).2
  have hVBlower := (abs_le.mp hVB).1
  have hVTupper := (abs_le.mp hVT).2
  have hVRlower := (abs_le.mp hVR.2).1
  have hHRlower := (abs_le.mp hHR).1
  linarith only [hHBlower, hHTupper, hVBlower, hVTupper, hVRlower, hHRlower]

end HardyTheorem
