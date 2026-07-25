import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZetaFiniteStripsExcludingCluster
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualFullTailConjugation

/-!
# Full actual zeta tail outside a conjugation-invariant main cluster

Carlson controls the positive-height tail outside the distinguished finite
cluster.  If that cluster is closed under complex conjugation, the negative
tail is the conjugate of the positive tail.  The real-ordinate outside-cluster
piece remains an explicit residual.
-/

open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem

open Filter
open Complex

/-- The distinguished finite cluster is stable under complex conjugation. -/
def IsConjugationInvariantCluster (S : Finset ℂ) : Prop :=
  ∀ rho, conj rho ∈ S ↔ rho ∈ S

/-- Suppress the distinguished cluster in a summand without changing the
ambient finite zero partition. -/
noncomputable def clusterExcludedTerm
    (S : Finset ℂ) (term : ℂ → ℂ) (rho : ℂ) : ℂ :=
  if rho ∈ S then 0 else term rho

/-- Suppressing a cluster in the summand is exactly summation over the finite
difference. -/
theorem sum_clusterExcludedTerm_eq_sum_sdiff
    (A S : Finset ℂ) (term : ℂ → ℂ) :
    (∑ rho ∈ A, clusterExcludedTerm S term rho) =
      ∑ rho ∈ A \ S, term rho := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      simp
  | @insert rho A hrho ih =>
      by_cases hS : rho ∈ S
      · have hdiff : insert rho A \ S = A \ S := by
          ext z
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨hz | hz, hzNotS⟩
            · exact False.elim (hzNotS (hz ▸ hS))
            · exact ⟨hz, hzNotS⟩
          · rintro ⟨hzA, hzNotS⟩
            exact ⟨Or.inr hzA, hzNotS⟩
        rw [hdiff]
        simpa [hrho, hS, clusterExcludedTerm] using ih
      · have hdiff : insert rho A \ S = insert rho (A \ S) := by
          ext z
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨hz | hz, hzNotS⟩
            · exact Or.inl hz
            · exact Or.inr ⟨hz, hzNotS⟩
          · rintro (hz | ⟨hzA, hzNotS⟩)
            · exact ⟨Or.inl hz, hz ▸ hS⟩
            · exact ⟨Or.inr hzA, hzNotS⟩
        rw [hdiff]
        simpa [hrho, hS, clusterExcludedTerm] using ih

/-- Full finite nontrivial zero set with the main cluster removed. -/
noncomputable def nontrivialZerosOutsideClusterFinset
    (T : ℝ) (S : Finset ℂ) : Finset ℂ :=
  nontrivialZerosFinset T \ S

/-- Negative-height finite zero set with the main cluster removed. -/
noncomputable def negativeNontrivialZerosOutsideClusterFinset
    (T : ℝ) (S : Finset ℂ) : Finset ℂ :=
  negativeNontrivialZerosFinset T \ S

/-- Real-ordinate finite zero residual with the main cluster removed. -/
noncomputable def realOrdinateNontrivialZerosOutsideClusterFinset
    (T : ℝ) (S : Finset ℂ) : Finset ℂ :=
  realOrdinateNontrivialZerosFinset T \ S

/-- A conjugation-equivariant term remains equivariant after suppressing a
conjugation-invariant cluster. -/
theorem clusterExcludedTerm_conj
    {T : ℝ} {S : Finset ℂ} {term : ℂ → ℂ}
    (hS : IsConjugationInvariantCluster S)
    (hterm :
      ∀ rho ∈ nontrivialZerosFinset T,
        term (conj rho) = conj (term rho))
    (rho : ℂ) (hrho : rho ∈ nontrivialZerosFinset T) :
    clusterExcludedTerm S term (conj rho) =
      conj (clusterExcludedTerm S term rho) := by
  by_cases hrhoS : rho ∈ S
  · have hconjS : conj rho ∈ S := (hS rho).2 hrhoS
    simp [clusterExcludedTerm, hrhoS, hconjS]
  · have hconjNotS : conj rho ∉ S := by
      intro hconjS
      exact hrhoS ((hS rho).1 hconjS)
    simp [clusterExcludedTerm, hrhoS, hconjNotS, hterm rho hrho]

/-- Conjugation identifies the negative and positive sums after deletion of a
conjugation-invariant cluster. -/
theorem sum_negativeOutsideCluster_eq_conj_sum_positiveOutsideCluster
    (T : ℝ) (S : Finset ℂ) (term : ℂ → ℂ)
    (hS : IsConjugationInvariantCluster S)
    (hterm :
      ∀ rho ∈ nontrivialZerosFinset T,
        term (conj rho) = conj (term rho)) :
    (∑ rho ∈ negativeNontrivialZerosOutsideClusterFinset T S, term rho) =
      conj
        (∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
          term rho) := by
  have hconj :=
    sum_negative_eq_conj_sum_positive T
      (clusterExcludedTerm S term)
      (clusterExcludedTerm_conj hS hterm)
  rw [sum_clusterExcludedTerm_eq_sum_sdiff,
    sum_clusterExcludedTerm_eq_sum_sdiff] at hconj
  exact hconj

/-- Exact positive/negative/real partition after deletion of the main
cluster. -/
theorem finiteZeroSumOutsideCluster_eq_positive_add_negative_add_real
    (T : ℝ) (S : Finset ℂ) (term : ℂ → ℂ) :
    ∑ rho ∈ nontrivialZerosOutsideClusterFinset T S, term rho =
      (∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
        term rho) +
      (∑ rho ∈ negativeNontrivialZerosOutsideClusterFinset T S,
        term rho) +
      ∑ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset T S,
        term rho := by
  have hpartition :=
    finiteZeroSum_eq_positive_add_negative_add_real T
      (clusterExcludedTerm S term)
  rw [sum_clusterExcludedTerm_eq_sum_sdiff,
    sum_clusterExcludedTerm_eq_sum_sdiff,
    sum_clusterExcludedTerm_eq_sum_sdiff,
    sum_clusterExcludedTerm_eq_sum_sdiff] at hpartition
  exact hpartition

/-- Norm of the complete relative PNT finite zero sum outside `S`. -/
noncomputable def dynamicFullOutsideClusterPNTZeroTailNorm
    (T : ℝ → ℝ) (S : Finset ℂ) (x : ℝ) : ℝ :=
  ‖∑ rho ∈ nontrivialZerosOutsideClusterFinset (T x) S,
      pntRelativeZeroContribution x rho‖

/-- Norm of the real-ordinate outside-cluster residual. -/
noncomputable def dynamicRealOrdinateOutsideClusterPNTZeroTailNorm
    (T : ℝ → ℝ) (S : Finset ℂ) (x : ℝ) : ℝ :=
  ‖∑ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset (T x) S,
      pntRelativeZeroContribution x rho‖

/-- The full outside-cluster tail is bounded by twice its positive part plus
the real-ordinate outside-cluster residual. -/
theorem dynamicFullOutsideClusterPNTZeroTailNorm_le_two_positive_add_real
    {T : ℝ → ℝ} {S : Finset ℂ}
    (hS : IsConjugationInvariantCluster S)
    {x : ℝ} (hx : 0 < x) :
    dynamicFullOutsideClusterPNTZeroTailNorm T S x ≤
      dynamicPositiveOutsideClusterPNTTailNorm T S x +
        dynamicPositiveOutsideClusterPNTTailNorm T S x +
          dynamicRealOrdinateOutsideClusterPNTZeroTailNorm T S x := by
  let positiveSum :=
    ∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset (T x) S,
      pntRelativeZeroContribution x rho
  let negativeSum :=
    ∑ rho ∈ negativeNontrivialZerosOutsideClusterFinset (T x) S,
      pntRelativeZeroContribution x rho
  let realSum :=
    ∑ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset (T x) S,
      pntRelativeZeroContribution x rho
  have hdecomp :
      (∑ rho ∈ nontrivialZerosOutsideClusterFinset (T x) S,
          pntRelativeZeroContribution x rho) =
        positiveSum + negativeSum + realSum :=
    finiteZeroSumOutsideCluster_eq_positive_add_negative_add_real
      (T x) S (pntRelativeZeroContribution x)
  have hnegative : negativeSum = conj positiveSum := by
    apply sum_negativeOutsideCluster_eq_conj_sum_positiveOutsideCluster
    · exact hS
    · intro rho hrho
      exact pntRelativeZeroContribution_conj hx
        (mem_nontrivialZerosFinset.mp hrho).1
  rw [dynamicFullOutsideClusterPNTZeroTailNorm, hdecomp]
  calc
    ‖positiveSum + negativeSum + realSum‖ ≤
        ‖positiveSum‖ + ‖negativeSum‖ + ‖realSum‖ := by
      calc
        ‖positiveSum + negativeSum + realSum‖ ≤
            ‖positiveSum + negativeSum‖ + ‖realSum‖ :=
          norm_add_le _ _
        _ ≤ ‖positiveSum‖ + ‖negativeSum‖ + ‖realSum‖ := by
          gcongr
          exact norm_add_le _ _
    _ = dynamicPositiveOutsideClusterPNTTailNorm T S x +
          dynamicPositiveOutsideClusterPNTTailNorm T S x +
            dynamicRealOrdinateOutsideClusterPNTZeroTailNorm T S x := by
      rw [hnegative, norm_conj]
      rfl

/-- Positive and real-residual target control implies target control of the
full outside-cluster finite zero tail. -/
theorem
    dynamicFullOutsideClusterPNTZeroTailNorm_targetAmplitudeNegligible
    {T amplitude : ℝ → ℝ} {S : Finset ℂ}
    (hS : IsConjugationInvariantCluster S)
    (hamplitude : ∀ᶠ x in atTop, 0 < amplitude x)
    (hpositive :
      TargetAmplitudeNegligible amplitude
        (dynamicPositiveOutsideClusterPNTTailNorm T S))
    (hreal :
      TargetAmplitudeNegligible amplitude
        (dynamicRealOrdinateOutsideClusterPNTZeroTailNorm T S)) :
    TargetAmplitudeNegligible amplitude
      (dynamicFullOutsideClusterPNTZeroTailNorm T S) := by
  have hmajorant :
      TargetAmplitudeNegligible amplitude
        (fun x =>
          dynamicPositiveOutsideClusterPNTTailNorm T S x +
            dynamicPositiveOutsideClusterPNTTailNorm T S x +
              dynamicRealOrdinateOutsideClusterPNTZeroTailNorm T S x) :=
    (hpositive.add hamplitude hpositive).add hamplitude hreal
  unfold TargetAmplitudeNegligible at hmajorant ⊢
  refine squeeze_zero' ?_ ?_ hmajorant
  · filter_upwards [hamplitude] with x hx
    exact div_nonneg (abs_nonneg _) hx.le
  · filter_upwards [hamplitude,
      eventually_gt_atTop (0 : ℝ)] with x hxAmplitude hx
    have hfull :=
      dynamicFullOutsideClusterPNTZeroTailNorm_le_two_positive_add_real
        (T := T) hS hx
    have hfullNonneg :
        0 ≤ dynamicFullOutsideClusterPNTZeroTailNorm T S x :=
      norm_nonneg _
    have hmajorantNonneg :
        0 ≤ dynamicPositiveOutsideClusterPNTTailNorm T S x +
            dynamicPositiveOutsideClusterPNTTailNorm T S x +
              dynamicRealOrdinateOutsideClusterPNTZeroTailNorm T S x :=
      add_nonneg
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
        (norm_nonneg _)
    rw [abs_of_nonneg hfullNonneg, abs_of_nonneg hmajorantNonneg]
    exact div_le_div_of_nonneg_right hfull hxAmplitude.le

/-- Finite outside-cluster Carlson strips plus the explicit real-ordinate
residual control the complete outside-cluster finite zero tail. -/
theorem
    actualZetaFiniteStripsOutsideCluster_fullTail_targetAmplitudeNegligible
    {n : ℕ} {S : Finset ℂ} {beta alpha : ℝ}
    (hS : IsConjugationInvariantCluster S)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x) S n)
    (sigma tau kappa epsilon : Fin n → ℝ)
    (hfixedSigma :
      ∀ i x, (input x).sigma i = sigma i)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (halpha : 0 < alpha)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hepsilon : ∀ i, 0 < epsilon i)
    (hmargin :
      ∀ i,
        targetAmplitudeStripEndpointExponent beta (tau i)
            (carlsonClassicalPolynomialDensityExponent
              alpha (sigma i)) +
          epsilon i < 0)
    (hreal :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta)
        (dynamicRealOrdinateOutsideClusterPNTZeroTailNorm
          (carlsonPolynomialHeight alpha) S)) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicFullOutsideClusterPNTZeroTailNorm
        (carlsonPolynomialHeight alpha) S) := by
  apply
    dynamicFullOutsideClusterPNTZeroTailNorm_targetAmplitudeNegligible
      hS (targetZeroPowerAmplitude_eventually_pos beta)
  · exact
      actualZetaFiniteStripsOutsideCluster_positiveTail_targetAmplitudeNegligible
        input sigma tau kappa epsilon hfixedSigma
        hsigma hsigmaOne halpha hkappa hnorm hre hepsilon hmargin
  · exact hreal

end PrimeNumberTheorem
