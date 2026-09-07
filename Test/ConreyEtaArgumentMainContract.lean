import HardyTheorem.ConreyEtaArgumentMain

open Complex Set MeasureTheory HardyTheorem

/-! Exact contracts: actual eta factorization, the right H main term, and
the full three-edge lower bound on the original long-product heights. -/

example {g g0 g1 L : ℝ} {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hne : conreyDegreeOneV1 g g0 g1 L s ≠ 0) :
    logDeriv (conreyDegreeOneEta g g0 g1 L) s =
      logDeriv conreyH s + logDeriv (conreyDegreeOneV1 g g0 g1 L) s :=
  logDeriv_conreyDegreeOneEta_eq_add hs hs1 hne

example {A U T : ℝ} (hA : 1 < A) (hU : 2 ≤ U) (hAU : A ≤ U) (hUT : U ≤ T) :
    |(∫ t in U..T, (logDeriv conreyH ((A : ℂ) + I * t)).re) -
      (∫ t in U..T, Real.log (t / (2 * Real.pi))) / 2| ≤ 8 * (T - U) :=
  conreyH_rightArgument_mainTerm_bound hA hU hAU hUT

example : ∃ L0 : ℝ, 40000 ≤ L0 ∧ ∀ {Y : ℕ} {L sigma0 U T : ℝ},
    L0 ≤ L → sigma0 ≤ 1 / 2 →
    U ∈ Icc (2 * Real.log L + 1) (2 * Real.log L + 2) →
    T ∈ Icc (Real.exp L - 1) (Real.exp L) → U < T →
    (∀ x ∈ Icc sigma0 (2 * Real.log L),
      conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y sigma0
        conreyExplicitP ((x : ℂ) + I * U) ≠ 0) →
    (∀ x ∈ Icc sigma0 (2 * Real.log L),
      conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y sigma0
        conreyExplicitP ((x : ℂ) + I * T) ≠ 0) →
    (∫ t in U..T, Real.log (t / (2 * Real.pi))) / 2 - 8 * (T - U) -
      (2 * Real.log L - 1 / 2) *
        (conreyHorizontalJensenArchimedeanConstant *
          (1 + Real.log (conreyHorizontalJensenHeightBase L (2 * Real.log L + 1) + 2)) +
         conreyHorizontalJensenArchimedeanConstant *
          (1 + Real.log (conreyHorizontalJensenHeightBase L (Real.exp L - 1) + 2))) -
      2200000000000 * L ^ 7 - Real.pi ≤
        conreyEtaThreeEdgeArgument (49 / 100) 0 (51 / 50) L (2 * Real.log L) U T :=
  exists_conreyEta_threeEdgeArgument_lower_bound

#print axioms logDeriv_conreyDegreeOneEta_eq_add
#print axioms conreyH_rightArgument_mainTerm_bound
#print axioms exists_conreyEta_threeEdgeArgument_lower_bound
