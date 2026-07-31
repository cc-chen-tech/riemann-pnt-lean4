import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightGoodHeightChoice
import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamicOptimization

/-!
# Pintz optimization over actual good-height candidates

An arbitrary finite height grid need not contain an analytic good height.  This
module instead builds the dynamic grid from a finite family of actual uniform
good-height selectors.  The pointwise cost minimizer therefore retains a
witnessing selector, an exact truncated explicit-formula certificate, and every
pointwise property shared by the certified candidates.

This is an upper-transfer component.  It does not assert a zero-free region,
an unconditional signed Omega theorem, or RH.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- A finite nonempty family of uniform good-height selectors whose truncated
explicit-formula certificates use one common constant. -/
structure ActualPintzGoodHeightCandidateFamily
    (ι : Type*) [Fintype ι] where
  selector : ι → UniformNaturalPointGoodHeightSelection
  commonConstant : ℝ
  constant_eq : ∀ i, (selector i).constant = commonConstant
  nonempty : Nonempty ι

/-- Every uniform selector gives a singleton certified candidate family. -/
noncomputable def actualPintzSingletonGoodHeightCandidateFamily
    (selection : UniformNaturalPointGoodHeightSelection) :
    ActualPintzGoodHeightCandidateFamily (Fin 1) where
  selector := fun _ => selection
  commonConstant := selection.constant
  constant_eq := fun _ => rfl
  nonempty := inferInstance

/-- The actual good-height candidate, regularized by a positive fallback below
the asymptotic range. -/
noncomputable def actualPintzCandidateHeight
    (alpha : ℝ) (selection : UniformNaturalPointGoodHeightSelection)
    (x : ℝ) : ℝ :=
  if 9 ≤ x ^ alpha then
    selectedUniformGoodHeight alpha selection x
  else
    8

/-- The lower envelope used by the certified dynamic grid. -/
noncomputable def actualPintzCandidateLowerEnvelope (alpha x : ℝ) : ℝ :=
  if 9 ≤ x ^ alpha then x ^ alpha - 1 else 0

theorem actualPintzCandidateLowerEnvelope_tendsto_atTop
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (actualPintzCandidateLowerEnvelope alpha) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  have hpower : Tendsto (fun x : ℝ => x ^ alpha) atTop atTop :=
    tendsto_rpow_atTop halpha
  have hlarge :
      ∀ᶠ x : ℝ in atTop, max 9 (b + 1) ≤ x ^ alpha :=
    (tendsto_atTop.1 hpower) (max 9 (b + 1))
  filter_upwards [hlarge] with x hx
  have hx9 : 9 ≤ x ^ alpha := (le_max_left _ _).trans hx
  have hxb : b + 1 ≤ x ^ alpha := (le_max_right _ _).trans hx
  rw [actualPintzCandidateLowerEnvelope, if_pos hx9]
  linarith

/-- At each scale the certified candidates form a finite nonempty positive
height grid. -/
noncomputable def actualPintzCandidateFiniteGrid
    {ι : Type*} [Fintype ι]
    (alpha : ℝ) (family : ActualPintzGoodHeightCandidateFamily ι)
    (x : ℝ) : FiniteHeightGrid where
  heights := Finset.univ.image
    (fun i => actualPintzCandidateHeight alpha (family.selector i) x)
  nonempty := by
    classical
    let i : ι := Classical.choice family.nonempty
    refine ⟨actualPintzCandidateHeight alpha (family.selector i) x, ?_⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  positive := by
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨i, _hi, rfl⟩
    by_cases hlarge : 9 ≤ x ^ alpha
    · have hbase : 8 ≤ x ^ alpha - 1 := by linarith
      have hmem := (family.selector i).height_mem
        (x ^ alpha - 1) hbase
      simp only [actualPintzCandidateHeight, if_pos hlarge,
        selectedUniformGoodHeight]
      exact lt_of_lt_of_le (by linarith : 0 < x ^ alpha - 1) hmem.1
    · simp [actualPintzCandidateHeight, hlarge]

theorem actualPintzCandidateLowerEnvelope_le
    {ι : Type*} [Fintype ι]
    (alpha : ℝ) (family : ActualPintzGoodHeightCandidateFamily ι)
    (x T : ℝ)
    (hT : T ∈ (actualPintzCandidateFiniteGrid alpha family x).heights) :
    actualPintzCandidateLowerEnvelope alpha x ≤ T := by
  rcases Finset.mem_image.mp hT with ⟨i, _hi, rfl⟩
  by_cases hlarge : 9 ≤ x ^ alpha
  · have hbase : 8 ≤ x ^ alpha - 1 := by linarith
    have hmem := (family.selector i).height_mem
      (x ^ alpha - 1) hbase
    simpa [actualPintzCandidateLowerEnvelope, actualPintzCandidateHeight,
      selectedUniformGoodHeight, hlarge] using hmem.1
  · simp [actualPintzCandidateLowerEnvelope, actualPintzCandidateHeight,
      hlarge]

/-- The dynamic grid generated entirely from certified actual good heights. -/
noncomputable def actualPintzCertifiedDynamicGrid
    {ι : Type*} [Fintype ι]
    (alpha : ℝ) (halpha : 0 < alpha)
    (family : ActualPintzGoodHeightCandidateFamily ι) :
    DynamicFiniteHeightGrid where
  grid := actualPintzCandidateFiniteGrid alpha family
  lowerEnvelope := actualPintzCandidateLowerEnvelope alpha
  lowerEnvelope_tendsto_atTop :=
    actualPintzCandidateLowerEnvelope_tendsto_atTop halpha
  lowerEnvelope_le := actualPintzCandidateLowerEnvelope_le alpha family

/-- The pointwise cost minimizer among the actual certified candidates. -/
noncomputable def actualPintzCertifiedOptimalHeight
    {ι : Type*} [Fintype ι]
    (cost : ℝ → ℝ → ℝ) (alpha : ℝ) (halpha : 0 < alpha)
    (family : ActualPintzGoodHeightCandidateFamily ι) (x : ℝ) : ℝ :=
  dynamicFiniteGridOptimalHeight cost
    (actualPintzCertifiedDynamicGrid alpha halpha family) x

/-- Optimizer membership recovers an actual selector producing exactly the
chosen height. -/
theorem actualPintzCertifiedOptimalHeight_eq_candidate
    {ι : Type*} [Fintype ι]
    (cost : ℝ → ℝ → ℝ) (alpha : ℝ) (halpha : 0 < alpha)
    (family : ActualPintzGoodHeightCandidateFamily ι) (x : ℝ) :
    ∃ i : ι,
      actualPintzCertifiedOptimalHeight cost alpha halpha family x =
        actualPintzCandidateHeight alpha (family.selector i) x := by
  have hmem := dynamicFiniteGridOptimalHeight_mem cost
    (actualPintzCertifiedDynamicGrid alpha halpha family) x
  rcases Finset.mem_image.mp hmem with ⟨i, _hi, hi⟩
  exact ⟨i, hi.symm⟩

/-- Exact Pintz-style pointwise cost optimality against every certified family
member. -/
theorem actualPintzCertifiedOptimalHeight_le_candidate
    {ι : Type*} [Fintype ι]
    (cost : ℝ → ℝ → ℝ) (alpha : ℝ) (halpha : 0 < alpha)
    (family : ActualPintzGoodHeightCandidateFamily ι) (x : ℝ) (i : ι) :
    cost x (actualPintzCertifiedOptimalHeight cost alpha halpha family x) ≤
      cost x (actualPintzCandidateHeight alpha (family.selector i) x) := by
  apply dynamicFiniteGridOptimalHeight_le_of_mem cost
    (actualPintzCertifiedDynamicGrid alpha halpha family)
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- The certified optimizer tends to infinity by its inherited Pintz lower
envelope. -/
theorem actualPintzCertifiedOptimalHeight_tendsto_atTop
    {ι : Type*} [Fintype ι]
    (cost : ℝ → ℝ → ℝ) (alpha : ℝ) (halpha : 0 < alpha)
    (family : ActualPintzGoodHeightCandidateFamily ι) :
    Tendsto (actualPintzCertifiedOptimalHeight cost alpha halpha family)
      atTop atTop :=
  dynamicFiniteGridOptimalHeight_tendsto_atTop cost
    (actualPintzCertifiedDynamicGrid alpha halpha family)

/-- Eventually the optimized height lies in the polynomial unit interval used
by the actual selected-height transfer. -/
theorem eventually_actualPintzCertifiedOptimalHeight_mem
    {ι : Type*} [Fintype ι]
    (cost : ℝ → ℝ → ℝ) {alpha : ℝ} (halpha : 0 < alpha)
    (family : ActualPintzGoodHeightCandidateFamily ι) :
    ∀ᶠ x : ℝ in atTop,
      actualPintzCertifiedOptimalHeight cost alpha halpha family x ∈
        Set.Icc (x ^ alpha - 1) (x ^ alpha) := by
  have hpower : Tendsto (fun x : ℝ => x ^ alpha) atTop atTop :=
    tendsto_rpow_atTop halpha
  have hlarge : ∀ᶠ x : ℝ in atTop, 9 ≤ x ^ alpha :=
    (tendsto_atTop.1 hpower) 9
  filter_upwards [hlarge] with x hx
  rcases actualPintzCertifiedOptimalHeight_eq_candidate
      cost alpha halpha family x with ⟨i, hi⟩
  have hbase : 8 ≤ x ^ alpha - 1 := by linarith
  rw [hi]
  simpa [actualPintzCandidateHeight, selectedUniformGoodHeight, hx] using
    (family.selector i).height_mem (x ^ alpha - 1) hbase

/-- Eventually every optimized height is an analytic good height. -/
theorem eventually_actualPintzCertifiedOptimalHeight_good
    {ι : Type*} [Fintype ι]
    (cost : ℝ → ℝ → ℝ) {alpha : ℝ} (halpha : 0 < alpha)
    (family : ActualPintzGoodHeightCandidateFamily ι) :
    ∀ᶠ x : ℝ in atTop,
      ExplicitFormulaAux.goodHeight
        (actualPintzCertifiedOptimalHeight cost alpha halpha family x) := by
  have hpower : Tendsto (fun x : ℝ => x ^ alpha) atTop atTop :=
    tendsto_rpow_atTop halpha
  have hlarge : ∀ᶠ x : ℝ in atTop, 9 ≤ x ^ alpha :=
    (tendsto_atTop.1 hpower) 9
  filter_upwards [hlarge] with x hx
  rcases actualPintzCertifiedOptimalHeight_eq_candidate
      cost alpha halpha family x with ⟨i, hi⟩
  have hbase : 8 ≤ x ^ alpha - 1 := by linarith
  rw [hi]
  simpa [actualPintzCandidateHeight, selectedUniformGoodHeight, hx] using
    (family.selector i).good_height (x ^ alpha - 1) hbase

/-- Every admissible natural sample receives a truncated explicit-formula
certificate at exactly the pointwise optimized height. -/
theorem actualPintzCertifiedOptimalHeight_truncatedCertificate
    {ι : Type*} [Fintype ι]
    (cost : ℝ → ℝ → ℝ) {alpha : ℝ} (halpha : 0 < alpha)
    (family : ActualPintzGoodHeightCandidateFamily ι)
    (m N : ℕ) (hm : 3 ≤ m)
    (hbase : 8 ≤ (m : ℝ) ^ alpha - 1) :
    ∃ certificate : TruncatedPNTErrorCertificate (m : ℝ)
        (actualPintzCertifiedOptimalHeight cost alpha halpha family (m : ℝ)),
      certificate.trivialContribution =
          cofinalTrivialZeroContribution m N ∧
        certificate.remainderBound =
          cofinalPNTFormulaRemainderBound family.commonConstant
            ((m : ℝ) ^ alpha - 1)
            (actualPintzCertifiedOptimalHeight cost alpha halpha family (m : ℝ))
            m N := by
  rcases actualPintzCertifiedOptimalHeight_eq_candidate
      cost alpha halpha family (m : ℝ) with ⟨i, hi⟩
  have hlarge : 9 ≤ (m : ℝ) ^ alpha := by linarith
  have hheight :
      actualPintzCertifiedOptimalHeight cost alpha halpha family (m : ℝ) =
        selectedUniformGoodHeight alpha (family.selector i) (m : ℝ) := by
    rw [hi]
    simp [actualPintzCandidateHeight, hlarge]
  rw [hheight]
  rcases selectedUniformGoodHeight_truncatedCertificate
      (family.selector i) m N hm hbase with
    ⟨certificate, htrivial, hremainder⟩
  refine ⟨certificate, htrivial, ?_⟩
  simpa [family.constant_eq i] using hremainder

/-- Any pointwise property shared by all certified candidates is inherited by
the pointwise optimizer.  Stack120 instantiates this with the visible-zero
envelope predicate. -/
theorem actualPintzCertifiedOptimalHeight_property
    {ι : Type*} [Fintype ι]
    (cost : ℝ → ℝ → ℝ) (alpha : ℝ) (halpha : 0 < alpha)
    (family : ActualPintzGoodHeightCandidateFamily ι)
    (P : ℝ → ℝ → Prop)
    (hP : ∀ i x,
      P x (actualPintzCandidateHeight alpha (family.selector i) x)) :
    ∀ x, P x (actualPintzCertifiedOptimalHeight cost alpha halpha family x) := by
  intro x
  rcases actualPintzCertifiedOptimalHeight_eq_candidate
      cost alpha halpha family x with ⟨i, hi⟩
  rw [hi]
  exact hP i x

end PrimeNumberTheorem
