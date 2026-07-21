import HardyTheorem.SelbergShortDirichletCollected
import HardyTheorem.SelbergMollifiedCoefficientArithmetic

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# Arithmetic of the collected Selberg short polynomial

The coefficient collected from triples `m * n * l = k` is the truncated
ordinary Dirichlet convolution of the already-collected coefficient for
`P_N M_X` with one further Selberg Moebius coefficient.  The critical-line
normalization contributes the common factor `1 / sqrt k`.
-/

/-- The truncated ordinary Dirichlet convolution of the coefficient of
`P_N M_X` with one further Selberg Moebius coefficient. -/
noncomputable def selbergShortCollectedDirichletConvolution
    (N X k : ℕ) : ℝ :=
  ∑ p ∈ selbergMollifiedDirichletPairs (N * X) X k,
    selbergMollifiedDirichletCoeff N X p.1 *
      selbergMoebiusCoeff X p.2

private theorem selbergShortCollectedRawSum_eq_convolution
    (N X k : ℕ) :
    (∑ p ∈ selbergShortDirichletTriples N X k,
        selbergMoebiusCoeff X p.2.1 * selbergMoebiusCoeff X p.2.2) =
      selbergShortCollectedDirichletConvolution N X k := by
  classical
  let P := selbergShortDirichletTriples N X k
  let Q := selbergMollifiedDirichletPairs (N * X) X k
  let g : ℕ × (ℕ × ℕ) → ℕ × ℕ := fun p =>
    (p.1 * p.2.1, p.2.2)
  let f : ℕ × (ℕ × ℕ) → ℝ := fun p =>
    selbergMoebiusCoeff X p.2.1 * selbergMoebiusCoeff X p.2.2
  have hmaps : ∀ p ∈ P, g p ∈ Q := by
    intro p hp
    change p ∈ selbergShortDirichletTriples N X k at hp
    rcases Finset.mem_filter.mp hp with ⟨hpSupport, hprod⟩
    rcases Finset.mem_product.mp hpSupport with ⟨hmN, hnlX⟩
    rcases Finset.mem_product.mp hnlX with ⟨hnX, hlX⟩
    rcases Finset.mem_Icc.mp hmN with ⟨hm1, hmN⟩
    rcases Finset.mem_Icc.mp hnX with ⟨hn1, hnX⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr
          ⟨Nat.mul_pos hm1 hn1, Nat.mul_le_mul hmN hnX⟩,
          hlX⟩,
        hprod⟩
  have hfiber :
      (∑ p ∈ P, f p) =
        ∑ q ∈ Q, ∑ p ∈ P.filter (fun p => g p = q), f p := by
    symm
    exact Finset.sum_fiberwise_of_maps_to hmaps f
  calc
    (∑ p ∈ selbergShortDirichletTriples N X k,
        selbergMoebiusCoeff X p.2.1 * selbergMoebiusCoeff X p.2.2) =
        ∑ p ∈ P, f p := by rfl
    _ = ∑ q ∈ Q, ∑ p ∈ P.filter (fun p => g p = q), f p := hfiber
    _ = ∑ q ∈ Q,
        selbergMollifiedDirichletCoeff N X q.1 *
          selbergMoebiusCoeff X q.2 := by
      apply Finset.sum_congr rfl
      intro q hq
      change q ∈ selbergMollifiedDirichletPairs (N * X) X k at hq
      have hqData := Finset.mem_filter.mp hq
      have hqProd := Finset.mem_product.mp hqData.1
      have hqMul : q.1 * q.2 = k := hqData.2
      rw [selbergMollifiedDirichletCoeff, Finset.sum_mul]
      apply Finset.sum_bij
          (fun p _hp => (p.1, p.2.1))
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpP, hgp⟩
        change p ∈ selbergShortDirichletTriples N X k at hpP
        rcases Finset.mem_filter.mp hpP with ⟨hpSupport, _hpMul⟩
        rcases Finset.mem_product.mp hpSupport with ⟨hmN, hnlX⟩
        rcases Finset.mem_product.mp hnlX with ⟨hnX, _hlX⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hmN, hnX⟩,
            congrArg Prod.fst hgp⟩
      · intro p₁ hp₁ p₂ hp₂ hpairs
        rcases Finset.mem_filter.mp hp₁ with ⟨_hp₁P, hg₁⟩
        rcases Finset.mem_filter.mp hp₂ with ⟨_hp₂P, hg₂⟩
        have hm : p₁.1 = p₂.1 := (Prod.ext_iff.mp hpairs).1
        have hn : p₁.2.1 = p₂.2.1 := (Prod.ext_iff.mp hpairs).2
        change (p₁.1 * p₁.2.1, p₁.2.2) = q at hg₁
        change (p₂.1 * p₂.2.1, p₂.2.2) = q at hg₂
        have hl₁ : p₁.2.2 = q.2 := (Prod.ext_iff.mp hg₁).2
        have hl₂ : p₂.2.2 = q.2 := (Prod.ext_iff.mp hg₂).2
        have hl : p₁.2.2 = p₂.2.2 := hl₁.trans hl₂.symm
        exact Prod.ext hm (Prod.ext hn hl)
      · intro r hr
        refine ⟨(r.1, r.2, q.2), ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          constructor
          · apply Finset.mem_filter.mpr
            constructor
            · exact Finset.mem_product.mpr
                ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hr).1).1,
                  Finset.mem_product.mpr
                    ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hr).1).2,
                      hqProd.2⟩⟩
            · rw [(Finset.mem_filter.mp hr).2, hqMul]
          · apply Prod.ext
            · exact (Finset.mem_filter.mp hr).2
            · rfl
        · rfl
      · intro p hp
        have hgp := (Finset.mem_filter.mp hp).2
        change selbergMoebiusCoeff X p.2.1 *
            selbergMoebiusCoeff X p.2.2 =
          selbergMoebiusCoeff X p.2.1 * selbergMoebiusCoeff X q.2
        rw [congrArg Prod.snd hgp]
    _ = selbergShortCollectedDirichletConvolution N X k := by rfl

/-- The collected critical-line coefficient is the truncated ordinary
Dirichlet convolution, multiplied by the common factor `1 / sqrt k`. -/
theorem selbergShortDirichletCollectedCoeff_eq_convolution
    (N X k : ℕ) :
    selbergShortDirichletCollectedCoeff N X k =
      (selbergShortCollectedDirichletConvolution N X k : ℂ) *
        (Real.sqrt (k : ℝ) : ℂ)⁻¹ := by
  classical
  rw [selbergShortDirichletCollectedCoeff]
  calc
    (∑ p ∈ selbergShortDirichletTriples N X k,
        selbergShortDirichletTripleCoeff X p) =
        (∑ p ∈ selbergShortDirichletTriples N X k,
          ((selbergMoebiusCoeff X p.2.1 *
            selbergMoebiusCoeff X p.2.2 : ℝ) : ℂ)) *
          (Real.sqrt (k : ℝ) : ℂ)⁻¹ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have hprod : p.1 * p.2.1 * p.2.2 = k :=
        (Finset.mem_filter.mp hp).2
      unfold selbergShortDirichletTripleCoeff
      rw [hprod]
      push_cast
      ring
    _ = (selbergShortCollectedDirichletConvolution N X k : ℂ) *
        (Real.sqrt (k : ℝ) : ℂ)⁻¹ := by
      have hraw := selbergShortCollectedRawSum_eq_convolution N X k
      have hcast :
          (∑ p ∈ selbergShortDirichletTriples N X k,
            ((selbergMoebiusCoeff X p.2.1 *
              selbergMoebiusCoeff X p.2.2 : ℝ) : ℂ)) =
            (selbergShortCollectedDirichletConvolution N X k : ℂ) := by
        exact_mod_cast hraw
      rw [hcast]

/-- The collected coefficient vanishes outside its explicit positive product
support. -/
theorem selbergShortDirichletCollectedCoeff_eq_zero_of_not_mem
    {N X k : ℕ} (hk : k ∉ Finset.Icc 1 (N * X * X)) :
    selbergShortDirichletCollectedCoeff N X k = 0 := by
  classical
  unfold selbergShortDirichletCollectedCoeff
  apply Finset.sum_eq_zero
  intro p hp
  exfalso
  apply hk
  rcases Finset.mem_filter.mp hp with ⟨hpSupport, hprod⟩
  rcases Finset.mem_product.mp hpSupport with ⟨hmN, hnlX⟩
  rcases Finset.mem_product.mp hnlX with ⟨hnX, hlX⟩
  rcases Finset.mem_Icc.mp hmN with ⟨hm1, hmN⟩
  rcases Finset.mem_Icc.mp hnX with ⟨hn1, hnX⟩
  rcases Finset.mem_Icc.mp hlX with ⟨hl1, hlX⟩
  rw [← hprod]
  exact Finset.mem_Icc.mpr
    ⟨Nat.mul_pos (Nat.mul_pos hm1 hn1) hl1,
      Nat.mul_le_mul (Nat.mul_le_mul hmN hnX) hlX⟩

/-- A conservative pointwise majorant for the collected coefficient.  It
uses only the divisor-count bound for the first mollified coefficient and
`|b_X(l)| ≤ 1` for the final mollifier factor; no sharp coefficient-energy
estimate is asserted here. -/
theorem norm_selbergShortDirichletCollectedCoeff_le_convolutionMajorant
    {N X k : ℕ} (hX : 2 ≤ X) :
    ‖selbergShortDirichletCollectedCoeff N X k‖ ≤
      (∑ p ∈ selbergMollifiedDirichletPairs (N * X) X k,
        (p.1.divisorsAntidiagonal.card : ℝ)) /
        Real.sqrt (k : ℝ) := by
  classical
  have hconv :
      |selbergShortCollectedDirichletConvolution N X k| ≤
        ∑ p ∈ selbergMollifiedDirichletPairs (N * X) X k,
          (p.1.divisorsAntidiagonal.card : ℝ) := by
    unfold selbergShortCollectedDirichletConvolution
    calc
      |∑ p ∈ selbergMollifiedDirichletPairs (N * X) X k,
          selbergMollifiedDirichletCoeff N X p.1 *
            selbergMoebiusCoeff X p.2| ≤
          ∑ p ∈ selbergMollifiedDirichletPairs (N * X) X k,
            |selbergMollifiedDirichletCoeff N X p.1 *
              selbergMoebiusCoeff X p.2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ selbergMollifiedDirichletPairs (N * X) X k,
          (p.1.divisorsAntidiagonal.card : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpSupport := (Finset.mem_filter.mp hp).1
        have hpX := (Finset.mem_product.mp hpSupport).2
        have ha := abs_selbergMollifiedDirichletCoeff_le_card_divisorsAntidiagonal
          (N := N) (X := X) (k := p.1) hX
        have hb := abs_selbergMoebiusCoeff_le_one hX
          (Finset.mem_Icc.mp hpX).1 (Finset.mem_Icc.mp hpX).2
        calc
          |selbergMollifiedDirichletCoeff N X p.1 *
              selbergMoebiusCoeff X p.2| =
              |selbergMollifiedDirichletCoeff N X p.1| *
                |selbergMoebiusCoeff X p.2| := abs_mul _ _
          _ ≤ (p.1.divisorsAntidiagonal.card : ℝ) * 1 :=
            mul_le_mul ha hb (abs_nonneg _) (by positivity)
          _ = (p.1.divisorsAntidiagonal.card : ℝ) := mul_one _
  rw [selbergShortDirichletCollectedCoeff_eq_convolution]
  simp only [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), norm_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hconv (inv_nonneg.mpr (Real.sqrt_nonneg _))

end HardyTheorem
