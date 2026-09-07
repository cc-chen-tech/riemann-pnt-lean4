import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set MeasureTheory
open scoped BigOperators Interval

namespace MathlibAux

/-- Integrating all disjoint components omitting a finite set recovers the whole interval. -/
theorem sum_intervalIntegral_eq_of_finite_complement
    {ι : Type*} [Fintype ι] {a b : ι → ℝ} {q : ℝ → ℝ}
    {K : Finset ℝ} {U T : ℝ} (hUT : U < T)
    (hgeom : ∀ i, U ≤ a i ∧ a i < b i ∧ b i ≤ T)
    (hdisjoint : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hcover : ∀ t ∈ Ioo U T, t ∉ K ↔ ∃ i, t ∈ Ioo (a i) (b i))
    (hq : ContinuousOn q (Icc U T)) :
    (∑ i, ∫ t in a i..b i, q t) = ∫ t in U..T, q t := by
  have hsub : ∀ i, Ioo (a i) (b i) ⊆ Ioo U T :=
    fun i => Ioo_subset_Ioo (hgeom i).1 (hgeom i).2.2
  have hunion : (⋃ i, Ioo (a i) (b i)) = Ioo U T \ (K : Set ℝ) := by
    ext t
    simp only [mem_iUnion, mem_sdiff, Finset.mem_coe]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨hsub i hi, (hcover t (hsub i hi)).mpr ⟨i, hi⟩⟩
    · rintro ⟨ht, hK⟩
      exact (hcover t ht).mp hK
  have hint : ∀ i, IntegrableOn q (Ioo (a i) (b i)) volume := by
    intro i
    have hcont : ContinuousOn q (Icc (a i) (b i)) :=
      hq.mono (Icc_subset_Icc (hgeom i).1 (hgeom i).2.2)
    exact hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  calc
    (∑ i, ∫ t in a i..b i, q t) = ∑ i, ∫ t in Ioo (a i) (b i), q t := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [intervalIntegral.integral_of_le (hgeom i).2.1.le, integral_Ioc_eq_integral_Ioo]
    _ = ∫ t in ⋃ i, Ioo (a i) (b i), q t :=
      (integral_iUnion_fintype (fun _ => measurableSet_Ioo) hdisjoint hint).symm
    _ = ∫ t in Ioo U T \ (K : Set ℝ), q t := by rw [hunion]
    _ = ∫ t in Ioo U T, q t :=
      setIntegral_congr_set (sdiff_null_ae_eq_self (K.measure_zero volume))
    _ = ∫ t in U..T, q t := by
      rw [intervalIntegral.integral_of_le hUT.le, integral_Ioc_eq_integral_Ioo]

end MathlibAux
