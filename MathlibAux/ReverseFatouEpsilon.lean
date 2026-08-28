import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Filter MeasureTheory Topology

namespace MathlibAux

/-- Reverse-Fatou epsilon principle for an integrable sequence with a
common constant upper bound.  It is the measure-theoretic core needed when
moving a logarithmic vertical boundary onto finitely many zeros. -/
theorem exists_integral_le_add_of_ae_tendsto_of_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ} {C δ : ℝ}
    (hδ : 0 < δ)
    (hC : Integrable (fun _ : α => C) μ)
    (hf : ∀ n, Integrable (f n) μ)
    (hg : Integrable g μ)
    (hfle : ∀ n, f n ≤ᵐ[μ] fun _ => C)
    (hgle : g ≤ᵐ[μ] fun _ => C)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ∃ n, ∫ x, f n x ∂μ ≤ (∫ x, g x ∂μ) + δ := by
  let F : ℕ → α → ℝ := fun n x => C - f n x
  let G : α → ℝ := fun x => C - g x
  have hFint : ∀ n, Integrable (F n) μ := fun n =>
    hC.sub (hf n)
  have hGint : Integrable G μ := hC.sub hg
  have hFnonneg : ∀ n, 0 ≤ᵐ[μ] F n := by
    intro n
    filter_upwards [hfle n] with x hx
    exact sub_nonneg.mpr hx
  have hGnonneg : 0 ≤ᵐ[μ] G := by
    filter_upwards [hgle] with x hx
    exact sub_nonneg.mpr hx
  have hFG : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (G x)) := by
    filter_upwards [hfg] with x hx
    exact tendsto_const_nhds.sub hx
  have hFatou :
      (∫⁻ x, ENNReal.ofReal (G x) ∂μ) ≤
        liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop := by
    calc
      (∫⁻ x, ENNReal.ofReal (G x) ∂μ) =
          ∫⁻ x, liminf (fun n => ENNReal.ofReal (F n x)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hFG] with x hx
        exact (ENNReal.continuous_ofReal.tendsto _ |>.comp hx).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => (hFint n).aemeasurable.ennreal_ofReal)
  by_contra h
  push Not at h
  have hFlt : ∀ n, (∫ x, F n x ∂μ) < (∫ x, G x ∂μ) - δ := by
    intro n
    have hn := h n
    dsimp only [F, G]
    rw [integral_sub hC (hf n), integral_sub hC hg]
    linarith
  have htargetPos : 0 < (∫ x, G x ∂μ) - δ := by
    have hzero : 0 ≤ ∫ x, F 0 x ∂μ := integral_nonneg_of_ae (hFnonneg 0)
    linarith [hFlt 0]
  have hEach : ∀ n,
      (∫⁻ x, ENNReal.ofReal (F n x) ∂μ) ≤
        ENNReal.ofReal ((∫ x, G x ∂μ) - δ) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hFint n) (hFnonneg n)]
    exact ENNReal.ofReal_le_ofReal (hFlt n).le
  have hLiminfLe :
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop ≤
        ENNReal.ofReal ((∫ x, G x ∂μ) - δ) :=
    liminf_le_of_frequently_le' (Frequently.of_forall hEach)
  have hOfReal :
      ENNReal.ofReal (∫ x, G x ∂μ) ≤
        ENNReal.ofReal ((∫ x, G x ∂μ) - δ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hGint hGnonneg]
    exact hFatou.trans hLiminfLe
  have hReal :
      (∫ x, G x ∂μ) ≤ (∫ x, G x ∂μ) - δ :=
    (ENNReal.ofReal_le_ofReal_iff htargetPos.le).mp hOfReal
  linarith

end MathlibAux
