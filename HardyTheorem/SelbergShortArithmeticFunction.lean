import HardyTheorem.SelbergShortHarmonicDecomposition
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

open scoped BigOperators

namespace HardyTheorem

/-!
# Arithmetic-function form of the short Selberg coefficients

The tapered Moebius coefficient is cut off outside `1, ..., X` and packaged
as an arithmetic function.  Dirichlet convolution then records exactly the
product collection used by the complete-range Selberg energy, while
convolution with the arithmetic zeta function records its divisor sums.
-/

/-- The linearly tapered Moebius coefficient, cut off to the finite interval
`1, ..., X`, as a real-valued arithmetic function. -/
noncomputable def selbergShortTaperedMoebius
    (X : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ∈ Finset.Icc 1 X then selbergMoebiusCoeff X n else 0, by simp⟩

@[simp] theorem selbergShortTaperedMoebius_apply
    (X n : ℕ) :
    selbergShortTaperedMoebius X n =
      if n ∈ Finset.Icc 1 X then selbergMoebiusCoeff X n else 0 :=
  rfl

/-- On every positive index, the product-collected double tapered Moebius
coefficient is exactly the Dirichlet convolution square of the corresponding
finitely supported arithmetic function. -/
theorem selbergShortDoubleMoebiusCoeff_eq_convolution_sq
    {X r : ℕ} (hr : 0 < r) :
    selbergShortDoubleMoebiusCoeff X r =
      (selbergShortTaperedMoebius X * selbergShortTaperedMoebius X) r := by
  classical
  rw [ArithmeticFunction.mul_apply]
  unfold selbergShortDoubleMoebiusCoeff
  have hfinset :
      (selbergShortCompleteRangePairSupport X).filter
          (fun p => selbergShortCompleteRangePairProduct p = r) =
        r.divisorsAntidiagonal.filter
          (fun p => p.1 ∈ Finset.Icc 1 X ∧ p.2 ∈ Finset.Icc 1 X) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hpSupport, hp⟩
      rcases Finset.mem_product.mp hpSupport with ⟨hp1, hp2⟩
      change p.1 * p.2 = r at hp
      exact ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨hp, Nat.ne_of_gt hr⟩, hp1, hp2⟩
    · rintro ⟨hp, hp1, hp2⟩
      refine ⟨Finset.mem_product.mpr ⟨hp1, hp2⟩, ?_⟩
      exact (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [hfinset]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hp1 : p.1 ∈ Finset.Icc 1 X
  · by_cases hp2 : p.2 ∈ Finset.Icc 1 X
    · simp [hp1, hp2, selbergShortCompleteRangePairWeight]
    · simp [hp1, hp2]
  · simp [hp1]

/-- The divisor sum in the complete-range square identity is the value of
the Dirichlet convolution of the double tapered coefficient with the
arithmetic zeta function. -/
theorem selbergShortDoubleMoebiusDivisorSum_eq_zetaConvolution
    {X k : ℕ} (hk : 0 < k) :
    (∑ r ∈ k.divisors, selbergShortDoubleMoebiusCoeff X r) =
      ((selbergShortTaperedMoebius X * selbergShortTaperedMoebius X) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) k := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← selbergShortDoubleMoebiusCoeff_eq_convolution_sq]
  exact Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hr) hk

end HardyTheorem
