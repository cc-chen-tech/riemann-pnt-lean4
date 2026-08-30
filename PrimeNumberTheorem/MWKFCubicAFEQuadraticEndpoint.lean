import PrimeNumberTheorem.MWKFCubicAFEWeightEndpoint
import Mathlib.MeasureTheory.Function.JacobianOneDim

open Complex MeasureTheory Set

namespace PrimeNumberTheorem.MWKFCubic

/-!
# The nonzero-shift quadratic product, with its Jacobian retained

On x>0 and delta+r*x>0, P(x)=x*(delta+r*x)/s is positive and
injective. Its derivative is at least |delta|/s when delta is nonzero.
The actual product-weight L1 theorem can therefore be pulled back to
this entire physical domain. Both signs of the shift are included;
no lower cutoff is inserted. The inverse Jacobian bound is s/|delta|,
not a constant uniform in all physical parameters or a summable shift
majorant. Physical phases/time factors and global limit exchanges are
not asserted in this file.
-/

theorem integrableOn_cubicAFERealProductWeightVertical_quadratic
    (t : ℝ) {X r s δ : ℝ} (hX : 1 / 2 < X)
    (hr : 0 < r) (hs : 0 < s) (hδ : δ ≠ 0) :
    IntegrableOn (fun x : ℝ ↦
      (((x * (δ + r * x) / s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        cubicAFERealProductWeightVertical t X (x * (δ + r * x) / s))
      {x : ℝ | 0 < x ∧ 0 < δ + r * x} := by
  let D : Set ℝ := {x : ℝ | 0 < x ∧ 0 < δ + r * x}
  let Q : ℝ → ℝ := fun x ↦ x * (δ + r * x) / s
  let Q' : ℝ → ℝ := fun x ↦ (δ + 2 * r * x) / s
  let F : ℝ → ℂ := fun P ↦ ((P ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
    cubicAFERealProductWeightVertical t X P
  let c : ℝ := |δ| / s
  have hc : 0 < c := div_pos (abs_pos.mpr hδ) hs
  have hD : MeasurableSet D :=
    ((isOpen_lt continuous_const continuous_id).inter
      (isOpen_lt continuous_const (continuous_const.add (continuous_const.mul continuous_id)))).measurableSet
  have hd (x : ℝ) : HasDerivAt Q (Q' x) x := by
    dsimp [Q, Q']
    exact (((hasDerivAt_id x).mul
      (((hasDerivAt_id x).const_mul r).const_add δ)).div_const s).congr_deriv
      (by simp only [id_eq]; ring)
  have hQ : Continuous Q := by dsimp [Q]; fun_prop
  have hmin (x : ℝ) (hx : x ∈ D) : c ≤ |Q' x| := by
    have hnum : |δ| ≤ δ + 2 * r * x := by
      rcases le_total 0 δ with hpos | hneg
      · rw [abs_of_nonneg hpos]
        nlinarith [mul_pos hr hx.1]
      · rw [abs_of_nonpos hneg]
        linarith [hx.2]
    exact (div_le_div_of_nonneg_right hnum hs.le).trans (le_abs_self _)
  have hinj : InjOn Q D := by
    intro x hx y hy hxy
    have heq : x * (δ + r * x) = y * (δ + r * y) := by
      have hh := congrArg (fun u : ℝ ↦ u * s) hxy
      simpa only [Q, div_mul_cancel₀ _ hs.ne'] using hh
    have hf : (x - y) * (δ + r * (x + y)) = 0 := by nlinarith [heq]
    have hp : 0 < δ + r * (x + y) := by nlinarith [hx.2, mul_pos hr hy.1]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hp.ne')
  have himage : Q '' D ⊆ Ioi 0 := by
    rintro _ ⟨x, hx, rfl⟩
    exact div_pos (mul_pos hx.1 hx.2) hs
  have hiF : IntegrableOn F (Ioi 0) := integrableOn_cubicAFERealProductWeightVertical_weighted t hX
  have hi : IntegrableOn (fun x ↦ |Q' x| • F (Q x)) D :=
    (integrableOn_image_iff_integrableOn_abs_deriv_smul hD
      (fun x _ ↦ (hd x).hasDerivWithinAt) hinj F).mp (hiF.mono_set himage)
  have hp : StronglyMeasurable (fun P : ℝ ↦ ((P ^ (-1 / 2 : ℝ) : ℝ) : ℂ)) :=
    (Complex.measurable_ofReal.comp (measurable_id.pow measurable_const)).stronglyMeasurable
  have hmF : StronglyMeasurable F := hp.mul
    (stronglyMeasurable_cubicAFERealProductWeightVertical t (by linarith) (by linarith))
  have hm := hmF.comp_measurable hQ.measurable
  apply (hi.norm.const_mul c⁻¹).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem hD] with x hx
  change ‖F (Q x)‖ ≤ c⁻¹ * ‖|Q' x| • F (Q x)‖
  rw [norm_smul, Real.norm_eq_abs, abs_abs]
  calc
    _ = c⁻¹ * (c * ‖F (Q x)‖) := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hmin x hx) (norm_nonneg _)) (inv_nonneg.mpr hc.le)

end PrimeNumberTheorem.MWKFCubic
