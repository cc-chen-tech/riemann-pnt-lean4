import MathlibAux.PaleyZygmund

open MeasureTheory Set

namespace MathlibAux

/-!
# First-moment gaps force positive support measure

This is the exact Cauchy--Schwarz step used in Selberg S5.  If `A - B`
vanishes away from a measurable exceptional set `e`, a lower first-moment
gap between `A` and `B` can only be carried by `e`.  Its square is therefore
bounded by the measure of `e` times the second moment on `e`.
-/

/-- A first-moment gap supported on `e` gives a quantitative lower bound for
the measure of `e`.  The product form avoids division by a possibly zero
second-moment bound. -/
theorem firstMomentGap_sq_le_measureReal_mul_secondMoment
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s e : Set α} {A B : α → ℝ} {L R M : ℝ}
    (hs : MeasurableSet s) (he : MeasurableSet e)
    (hμe : μ e ≠ ⊤) (hes : e ⊆ s)
    (hAint : IntegrableOn A s μ) (hBint : IntegrableOn B s μ)
    (hgapSqInt : IntegrableOn (fun x => (A x - B x) ^ 2) e μ)
    (hzero : ∀ x ∈ s \ e, A x - B x = 0)
    (hfirst : L ≤ ∫ x in s, A x ∂μ)
    (hsigned : (∫ x in s, B x ∂μ) ≤ R)
    (hsecond : (∫ x in e, (A x - B x) ^ 2 ∂μ) ≤ M)
    (hgap : 0 ≤ L - R) :
    (L - R) ^ 2 ≤ μ.real e * M := by
  let D : α → ℝ := fun x => A x - B x
  have hDint : IntegrableOn D s μ := by
    exact hAint.sub hBint
  have hDzero : (∫ x in s \ e, D x ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (hs.diff he)] with x hx
    exact hzero x hx
  have hDeq : (∫ x in e, D x ∂μ) = ∫ x in s, D x ∂μ := by
    have hdiff := setIntegral_sdiff he hDint hes
    rw [hDzero] at hdiff
    linarith
  have hDlower : L - R ≤ ∫ x in e, D x ∂μ := by
    rw [hDeq]
    have hsub := integral_sub hAint hBint
    change (∫ x in s, A x - B x ∂μ) = _ at hsub
    rw [hsub]
    linarith
  have hDnonneg : 0 ≤ ∫ x in e, D x ∂μ := hgap.trans hDlower
  have hcs :
      (∫ x in e, D x ∂μ) ^ 2 ≤
        μ.real e * ∫ x in e, D x ^ 2 ∂μ :=
    sq_setIntegral_le_measureReal_mul_setIntegral_sq_of_aestronglyMeasurable
      hμe
      (hDint.mono_set hes).aestronglyMeasurable
      (by simpa only [D] using hgapSqInt)
  calc
    (L - R) ^ 2 ≤ (∫ x in e, D x ∂μ) ^ 2 := by
      nlinarith
    _ ≤ μ.real e * ∫ x in e, D x ^ 2 ∂μ := hcs
    _ ≤ μ.real e * M :=
      mul_le_mul_of_nonneg_left (by simpa only [D] using hsecond)
        measureReal_nonneg

end MathlibAux
