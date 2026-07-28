import PrimeNumberTheorem.VKEdgeExplicitFormulaPairBridge
import PrimeNumberTheorem.ZeroForcedOscillationComplementaryBound

open Complex
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The genuine finite explicit-formula zero remainder after deleting the
selected conjugate pair, normalized at the growth scale of `rho0`. -/
def normalizedFiniteNontrivialZeroResidueRemainder
    (rho0 : ℂ) (T y : ℝ) : ℂ :=
  ((‖rho0‖ * Real.exp (-rho0.re * y) : ℝ) : ℂ) *
    finiteNontrivialZeroResidueRemainder (Real.exp y) T rho0

/-- If every finite-height zero left after deleting the target conjugate pair
lies a fixed real-part gap below the target, its normalized contribution is
controlled by the repository's full multiplicity-weighted reciprocal-zero
sum. This is an actual explicit-formula remainder, not a cosine model. -/
theorem norm_normalizedFiniteNontrivialZeroResidueRemainder_le
    {rho0 : ℂ} {T delta y : ℝ}
    (hy : 0 ≤ y)
    (hgap :
      ∀ rho ∈ ((nontrivialZerosFinset T).erase rho0).erase (conj rho0),
        rho.re ≤ rho0.re - delta) :
    ‖normalizedFiniteNontrivialZeroResidueRemainder rho0 T y‖ ≤
      ‖rho0‖ * Real.exp (-delta * y) *
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
  classical
  let S : ℂ :=
    ∑ rho ∈ ((nontrivialZerosFinset T).erase rho0).erase (conj rho0),
      explicitFormulaZeroResidueTerm (Real.exp y) rho
  have hsum :
      ‖S‖ ≤
        Real.exp ((rho0.re - delta) * y) *
          ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
    calc
      ‖S‖ ≤
          ∑ rho ∈
              ((nontrivialZerosFinset T).erase rho0).erase (conj rho0),
            ‖explicitFormulaZeroResidueTerm (Real.exp y) rho‖ := by
        dsimp only [S]
        exact norm_sum_le _ _
      _ = ∑ rho ∈
              ((nontrivialZerosFinset T).erase rho0).erase (conj rho0),
            (analyticOrderNatAt riemannZeta rho : ℝ) *
              (Real.exp y) ^ rho.re / ‖rho‖ := by
        refine Finset.sum_congr rfl fun rho _ => ?_
        unfold explicitFormulaZeroResidueTerm
        rw [norm_div, norm_mul, norm_neg, Complex.norm_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos y)]
      _ ≤ ∑ rho ∈
              ((nontrivialZerosFinset T).erase rho0).erase (conj rho0),
            Real.exp ((rho0.re - delta) * y) *
              ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) := by
        refine Finset.sum_le_sum fun rho hrho => ?_
        have hexp :
            (Real.exp y) ^ rho.re ≤
              Real.exp ((rho0.re - delta) * y) := by
          rw [Real.rpow_def_of_pos (Real.exp_pos y), Real.log_exp,
            mul_comm y rho.re]
          exact Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_right (hgap rho hrho) hy)
        have hden : 0 ≤ ‖rho‖ := norm_nonneg rho
        calc
          (analyticOrderNatAt riemannZeta rho : ℝ) *
                (Real.exp y) ^ rho.re / ‖rho‖ ≤
              (analyticOrderNatAt riemannZeta rho : ℝ) *
                Real.exp ((rho0.re - delta) * y) / ‖rho‖ :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _)) hden
          _ = Real.exp ((rho0.re - delta) * y) *
                ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) := by
            ring
      _ = Real.exp ((rho0.re - delta) * y) *
            ∑ rho ∈
                ((nontrivialZerosFinset T).erase rho0).erase (conj rho0),
              ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) := by
        rw [Finset.mul_sum]
      _ ≤ Real.exp ((rho0.re - delta) * y) *
            ∑ rho ∈ nontrivialZerosFinset T,
              ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg
            ((Finset.erase_subset (conj rho0)
              ((nontrivialZerosFinset T).erase rho0)).trans
              (Finset.erase_subset rho0 (nontrivialZerosFinset T)))
            (fun _ _ _ =>
              div_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        · exact Real.exp_nonneg _
      _ = Real.exp ((rho0.re - delta) * y) *
            ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
        rfl
  calc
    ‖normalizedFiniteNontrivialZeroResidueRemainder rho0 T y‖ =
        (‖rho0‖ * Real.exp (-rho0.re * y)) * ‖S‖ := by
      simp only [normalizedFiniteNontrivialZeroResidueRemainder,
        finiteNontrivialZeroResidueRemainder, S, norm_mul,
        norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg rho0),
        abs_of_pos (Real.exp_pos _)]
    _ ≤ (‖rho0‖ * Real.exp (-rho0.re * y)) *
          (Real.exp ((rho0.re - delta) * y) *
            ExplicitFormulaAux.globalReciprocalZeroMultiplicity T) :=
      mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))
    _ = ‖rho0‖ * Real.exp (-delta * y) *
          ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
      calc
        (‖rho0‖ * Real.exp (-rho0.re * y)) *
              (Real.exp ((rho0.re - delta) * y) *
                ExplicitFormulaAux.globalReciprocalZeroMultiplicity T) =
            ‖rho0‖ *
              (Real.exp (-rho0.re * y) *
                Real.exp ((rho0.re - delta) * y)) *
              ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by ring
        _ = _ := by
          rw [← Real.exp_add]
          congr 3
          ring

/-- Exact triangle decomposition of the genuine normalized explicit-formula
residual into the jump correction, the remaining zero residues, the closed
terms, and the finite-height approximation error. -/
theorem norm_normalizedExplicitFormulaResidual_le_components
    (rho0 : ℂ) (T y : ℝ) :
    ‖normalizedExplicitFormulaResidual rho0 T y‖ ≤
      ‖rho0‖ * Real.exp (-rho0.re * y) *
        (|chebyshevPsi (Real.exp y) - chebyshevPsi0 (Real.exp y)| +
          ‖finiteNontrivialZeroResidueRemainder
            (Real.exp y) T rho0‖ +
          ‖explicitFormulaClosedTerms y‖ +
          ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖) := by
  let jump : ℂ :=
    ((chebyshevPsi (Real.exp y) - chebyshevPsi0 (Real.exp y) : ℝ) : ℂ)
  let zeros : ℂ :=
    finiteNontrivialZeroResidueRemainder (Real.exp y) T rho0
  let closed : ℂ := explicitFormulaClosedTerms y
  let approximation : ℂ :=
    explicitFormulaApproxWithMultiplicity (Real.exp y) T -
      (chebyshevPsi0 (Real.exp y) : ℂ)
  have hinside :
      ‖jump + zeros - closed - approximation‖ ≤
        ‖jump‖ + ‖zeros‖ + ‖closed‖ + ‖approximation‖ := by
    calc
      ‖jump + zeros - closed - approximation‖ ≤
          ‖jump + zeros - closed‖ + ‖approximation‖ :=
        norm_sub_le _ _
      _ ≤ (‖jump + zeros‖ + ‖closed‖) + ‖approximation‖ :=
        by
          gcongr
          exact norm_sub_le _ _
      _ ≤ (‖jump‖ + ‖zeros‖ + ‖closed‖) + ‖approximation‖ := by
        gcongr
        exact norm_add_le _ _
      _ = ‖jump‖ + ‖zeros‖ + ‖closed‖ + ‖approximation‖ := by
        ring
  calc
    ‖normalizedExplicitFormulaResidual rho0 T y‖ =
        (‖rho0‖ * Real.exp (-rho0.re * y)) *
          ‖jump + zeros - closed - approximation‖ := by
      simp only [normalizedExplicitFormulaResidual, jump, zeros, closed,
        approximation, norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg rho0),
        abs_of_pos (Real.exp_pos _)]
    _ ≤ (‖rho0‖ * Real.exp (-rho0.re * y)) *
          (‖jump‖ + ‖zeros‖ + ‖closed‖ + ‖approximation‖) :=
      mul_le_mul_of_nonneg_left hinside
        (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))
    _ = ‖rho0‖ * Real.exp (-rho0.re * y) *
        (|chebyshevPsi (Real.exp y) - chebyshevPsi0 (Real.exp y)| +
          ‖finiteNontrivialZeroResidueRemainder
            (Real.exp y) T rho0‖ +
          ‖explicitFormulaClosedTerms y‖ +
          ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖) := by
      simp only [jump, zeros, closed, approximation, norm_real,
        Real.norm_eq_abs]

/-- The genuine explicit-formula residual bound after inserting a fixed
real-part gap for every finite-height zero outside the selected conjugate
pair. The jump correction, closed terms, and finite-height approximation
error remain visible because this theorem does not assume estimates for
them. -/
theorem norm_normalizedExplicitFormulaResidual_le_components_of_gap
    {rho0 : ℂ} {T delta y : ℝ}
    (hy : 0 ≤ y)
    (hgap :
      ∀ rho ∈ ((nontrivialZerosFinset T).erase rho0).erase (conj rho0),
        rho.re ≤ rho0.re - delta) :
    ‖normalizedExplicitFormulaResidual rho0 T y‖ ≤
      ‖rho0‖ * Real.exp (-rho0.re * y) *
          (|chebyshevPsi (Real.exp y) - chebyshevPsi0 (Real.exp y)| +
            ‖explicitFormulaClosedTerms y‖ +
            ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
              (chebyshevPsi0 (Real.exp y) : ℂ)‖) +
        ‖rho0‖ * Real.exp (-delta * y) *
          ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
  let scale : ℝ := ‖rho0‖ * Real.exp (-rho0.re * y)
  let jump : ℝ :=
    |chebyshevPsi (Real.exp y) - chebyshevPsi0 (Real.exp y)|
  let zeros : ℝ :=
    ‖finiteNontrivialZeroResidueRemainder (Real.exp y) T rho0‖
  let closed : ℝ := ‖explicitFormulaClosedTerms y‖
  let approximation : ℝ :=
    ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
      (chebyshevPsi0 (Real.exp y) : ℂ)‖
  have hcomponents :
      ‖normalizedExplicitFormulaResidual rho0 T y‖ ≤
        scale * (jump + zeros + closed + approximation) := by
    simpa only [scale, jump, zeros, closed, approximation] using
      norm_normalizedExplicitFormulaResidual_le_components rho0 T y
  have hzero :
      scale * zeros ≤
        ‖rho0‖ * Real.exp (-delta * y) *
          ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
    have hnormalized :=
      norm_normalizedFiniteNontrivialZeroResidueRemainder_le
        (rho0 := rho0) (T := T) (delta := delta) (y := y) hy hgap
    have hnormEq :
        ‖normalizedFiniteNontrivialZeroResidueRemainder rho0 T y‖ =
          scale * zeros := by
      simp only [normalizedFiniteNontrivialZeroResidueRemainder,
        scale, zeros, norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg rho0),
        abs_of_pos (Real.exp_pos _)]
    rwa [hnormEq] at hnormalized
  calc
    ‖normalizedExplicitFormulaResidual rho0 T y‖ ≤
        scale * (jump + zeros + closed + approximation) := hcomponents
    _ = scale * (jump + closed + approximation) + scale * zeros := by
      ring
    _ ≤ scale * (jump + closed + approximation) +
          ‖rho0‖ * Real.exp (-delta * y) *
            ExplicitFormulaAux.globalReciprocalZeroMultiplicity T :=
      add_le_add (le_refl _) hzero
    _ = ‖rho0‖ * Real.exp (-rho0.re * y) *
          (|chebyshevPsi (Real.exp y) - chebyshevPsi0 (Real.exp y)| +
            ‖explicitFormulaClosedTerms y‖ +
            ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
              (chebyshevPsi0 (Real.exp y) : ℂ)‖) +
        ‖rho0‖ * Real.exp (-delta * y) *
          ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
      rfl

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
