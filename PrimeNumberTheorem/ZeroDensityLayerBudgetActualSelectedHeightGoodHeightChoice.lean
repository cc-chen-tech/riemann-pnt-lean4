import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTGoodHeightAdapter

/-!
# A global selected good-height function

The uniform natural-point contour theorem has quantifier order

`exists C, forall A >= 8, exists T in [A, A + 1], ...`.

Classical choice therefore produces one height for every admissible base
point while retaining the same constant `C`.  Evaluating this selector at
`A(x) = x ^ alpha - 1` gives a single height function in
`[x ^ alpha - 1, x ^ alpha]`, exactly the interval required by the selected
Carlson transfer.

This module only constructs the selector and its truncated formula
certificates.  It does not yet prove target-amplitude negligibility of the
resulting explicit-formula remainder.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- One global choice of uniform short-interval good heights, with the common
constant and every natural-point truncated explicit-formula certificate. -/
structure UniformNaturalPointGoodHeightSelection : Type where
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  height : ℝ → ℝ
  height_mem :
    ∀ A : ℝ, 8 ≤ A → height A ∈ Set.Icc A (A + 1)
  good_height :
    ∀ A : ℝ, 8 ≤ A → ExplicitFormulaAux.goodHeight (height A)
  truncated_certificate :
    ∀ (A : ℝ), 8 ≤ A →
      ∀ (m N : ℕ), 3 ≤ m →
        ∃ certificate : TruncatedPNTErrorCertificate (m : ℝ) (height A),
          certificate.trivialContribution =
              cofinalTrivialZeroContribution m N ∧
            certificate.remainderBound =
              cofinalPNTFormulaRemainderBound constant A (height A) m N

/-- The uniform good-height theorem admits a single global selector. -/
theorem exists_uniformNaturalPointGoodHeightSelection :
    Nonempty UniformNaturalPointGoodHeightSelection := by
  rcases exists_uniform_goodHeight_Icc_truncatedPNTErrorCertificate with
    ⟨C, hC, hselect⟩
  have htotal :
      ∀ A : ℝ, ∃ T : ℝ, 8 ≤ A →
        T ∈ Set.Icc A (A + 1) ∧
          ExplicitFormulaAux.goodHeight T ∧
            ∀ (m N : ℕ), 3 ≤ m →
              ∃ certificate : TruncatedPNTErrorCertificate (m : ℝ) T,
                certificate.trivialContribution =
                    cofinalTrivialZeroContribution m N ∧
                  certificate.remainderBound =
                    cofinalPNTFormulaRemainderBound C A T m N := by
    intro A
    by_cases hA : 8 ≤ A
    · rcases hselect A hA with ⟨T, hT, hgood, hcertificate⟩
      exact ⟨T, fun _ => ⟨hT, hgood, hcertificate⟩⟩
    · exact ⟨8, fun hA' => (hA hA').elim⟩
  choose height hheight using htotal
  exact ⟨{
    constant := C
    constant_nonneg := hC
    height := height
    height_mem := fun A hA => (hheight A hA).1
    good_height := fun A hA => (hheight A hA).2.1
    truncated_certificate := fun A hA =>
      (hheight A hA).2.2
  }⟩

/-- A fixed canonical selector, used only to expose a convenient global
height schedule. -/
noncomputable def uniformNaturalPointGoodHeightSelection :
    UniformNaturalPointGoodHeightSelection :=
  Classical.choice exists_uniformNaturalPointGoodHeightSelection

/-- Polynomial selected-height schedule obtained from a uniform selector. -/
noncomputable def selectedUniformGoodHeight
    (alpha : ℝ) (selection : UniformNaturalPointGoodHeightSelection)
    (x : ℝ) : ℝ :=
  selection.height (x ^ alpha - 1)

/-- For positive polynomial exponent, the selected schedule eventually lies
in the interval required by the selected-height Carlson transfer. -/
theorem eventually_selectedUniformGoodHeight_mem
    {alpha : ℝ} (halpha : 0 < alpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ x : ℝ in atTop,
      selectedUniformGoodHeight alpha selection x ∈
        Set.Icc (x ^ alpha - 1) (x ^ alpha) := by
  have hpower :
      Tendsto (fun x : ℝ => x ^ alpha) atTop atTop :=
    tendsto_rpow_atTop halpha
  have hlarge : ∀ᶠ x : ℝ in atTop, 9 ≤ x ^ alpha :=
    (tendsto_atTop.1 hpower) 9
  filter_upwards [hlarge] with x hx
  have hbase : 8 ≤ x ^ alpha - 1 := by linarith
  simpa [selectedUniformGoodHeight] using
    selection.height_mem (x ^ alpha - 1) hbase

/-- The same selected schedule consists eventually of analytic good heights. -/
theorem eventually_selectedUniformGoodHeight_good
    {alpha : ℝ} (halpha : 0 < alpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ x : ℝ in atTop,
      ExplicitFormulaAux.goodHeight
        (selectedUniformGoodHeight alpha selection x) := by
  have hpower :
      Tendsto (fun x : ℝ => x ^ alpha) atTop atTop :=
    tendsto_rpow_atTop halpha
  have hlarge : ∀ᶠ x : ℝ in atTop, 9 ≤ x ^ alpha :=
    (tendsto_atTop.1 hpower) 9
  filter_upwards [hlarge] with x hx
  have hbase : 8 ≤ x ^ alpha - 1 := by linarith
  exact selection.good_height (x ^ alpha - 1) hbase

/-- Every admissible natural sample receives a truncated explicit-formula
certificate at exactly the selected polynomial height. -/
theorem selectedUniformGoodHeight_truncatedCertificate
    {alpha : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (m N : ℕ) (hm : 3 ≤ m)
    (hbase : 8 ≤ (m : ℝ) ^ alpha - 1) :
    ∃ certificate :
        TruncatedPNTErrorCertificate (m : ℝ)
          (selectedUniformGoodHeight alpha selection (m : ℝ)),
      certificate.trivialContribution =
          cofinalTrivialZeroContribution m N ∧
        certificate.remainderBound =
          cofinalPNTFormulaRemainderBound selection.constant
            ((m : ℝ) ^ alpha - 1)
            (selectedUniformGoodHeight alpha selection (m : ℝ)) m N := by
  simpa [selectedUniformGoodHeight] using
    selection.truncated_certificate
      ((m : ℝ) ^ alpha - 1) hbase m N hm

/--
Auditable existence form of the selected-height construction.

The same `C` and `H` work in the eventual Carlson interval and in every
admissible natural-point contour certificate.
-/
theorem exists_selectedUniformGoodHeightSchedule
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∃ (C : ℝ) (H : ℝ → ℝ), 0 ≤ C ∧
      (∀ᶠ x : ℝ in atTop,
        H x ∈ Set.Icc (x ^ alpha - 1) (x ^ alpha)) ∧
      (∀ᶠ x : ℝ in atTop, ExplicitFormulaAux.goodHeight (H x)) ∧
      ∀ (m N : ℕ), 3 ≤ m → 8 ≤ (m : ℝ) ^ alpha - 1 →
        ∃ certificate : TruncatedPNTErrorCertificate (m : ℝ) (H (m : ℝ)),
          certificate.trivialContribution =
              cofinalTrivialZeroContribution m N ∧
            certificate.remainderBound =
              cofinalPNTFormulaRemainderBound C
                ((m : ℝ) ^ alpha - 1) (H (m : ℝ)) m N := by
  let selection := uniformNaturalPointGoodHeightSelection
  refine ⟨selection.constant,
    selectedUniformGoodHeight alpha selection,
    selection.constant_nonneg,
    eventually_selectedUniformGoodHeight_mem halpha selection,
    eventually_selectedUniformGoodHeight_good halpha selection,
    ?_⟩
  intro m N hm hbase
  exact
    selectedUniformGoodHeight_truncatedCertificate
      selection m N hm hbase

end PrimeNumberTheorem
