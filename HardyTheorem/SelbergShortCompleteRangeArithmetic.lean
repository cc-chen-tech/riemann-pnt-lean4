import HardyTheorem.SelbergShortCollectedArithmetic

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# Complete-range arithmetic for the collected Selberg short coefficient

When `1 <= k <= N`, the truncation on the zeta-polynomial index is automatic:
for every pair `d,l <= X` with `d*l | k`, the remaining factor
`m = k/(d*l)` lies in `1,...,N`.  Thus the collected coefficient exposes the
full finite coefficient of `M_X^2`, with no remaining `m <= N` condition.
-/

/-- The two mollifier indices contributing to product `k` after the
zeta-polynomial truncation has become automatic. -/
noncomputable def selbergShortCompleteRangePairs
    (X k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 X).product (Finset.Icc 1 X)).filter
    (fun p => p.1 * p.2 ∣ k)

/-- For `1 <= k <= N`, triples `m*d*l=k` in the original support are exactly
the image of the complete pair support under `m = k/(d*l)`. -/
theorem selbergShortDirichletTriples_eq_completeRangePairs_image
    {N X k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    selbergShortDirichletTriples N X k =
      (selbergShortCompleteRangePairs X k).image
        (fun p => (k / (p.1 * p.2), (p.1, p.2))) := by
  classical
  ext q
  rcases q with ⟨m, d, l⟩
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqSupport, hprod⟩
    rcases Finset.mem_product.mp hqSupport with ⟨hmN, hdlX⟩
    rcases Finset.mem_product.mp hdlX with ⟨hdX, hlX⟩
    have hdlDvd : d * l ∣ k := by
      refine ⟨m, ?_⟩
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hprod.symm
    have hdlPos : 0 < d * l :=
      Nat.mul_pos (Finset.mem_Icc.mp hdX).1 (Finset.mem_Icc.mp hlX).1
    have hquot : k / (d * l) = m := by
      apply Nat.div_eq_of_eq_mul_left hdlPos
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hprod.symm
    apply Finset.mem_image.mpr
    refine ⟨(d, l), ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hdX, hlX⟩, hdlDvd⟩
    · simp only [hquot]
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, hpEq⟩
    rcases p with ⟨d', l'⟩
    rcases Finset.mem_filter.mp hp with ⟨hpSupport, hdlDvd⟩
    rcases Finset.mem_product.mp hpSupport with ⟨hdX, hlX⟩
    have hdlPos : 0 < d' * l' :=
      Nat.mul_pos (Finset.mem_Icc.mp hdX).1 (Finset.mem_Icc.mp hlX).1
    have hm1 : 1 ≤ k / (d' * l') := by
      exact Nat.div_pos (Nat.le_of_dvd hk1 hdlDvd) hdlPos
    have hmN : k / (d' * l') ≤ N :=
      (Nat.div_le_self k (d' * l')).trans hkN
    have hprod : (k / (d' * l')) * d' * l' = k := by
      calc
        (k / (d' * l')) * d' * l' =
            (k / (d' * l')) * (d' * l') := by simp [Nat.mul_assoc]
        _ = k := Nat.div_mul_cancel hdlDvd
    have himage :
        (k / (d' * l'), (d', l')) = (m, (d, l)) := hpEq
    rw [← himage]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hm1, hmN⟩,
          Finset.mem_product.mpr ⟨hdX, hlX⟩⟩,
        hprod⟩

/-- In the complete `k <= N` range, the collected short convolution is the
exact finite coefficient of `M_X^2`: a double tapered-Moebius sum over
`d,l <= X` with `d*l | k`. -/
theorem selbergShortCollectedDirichletConvolution_eq_completeRange
    {N X k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    selbergShortCollectedDirichletConvolution N X k =
      ∑ p ∈ selbergShortCompleteRangePairs X k,
        selbergMoebiusCoeff X p.1 * selbergMoebiusCoeff X p.2 := by
  classical
  let S := selbergShortCompleteRangePairs X k
  let g : ℕ × ℕ → ℕ × (ℕ × ℕ) := fun p =>
    (k / (p.1 * p.2), (p.1, p.2))
  let B : ℝ := ∑ p ∈ S,
    selbergMoebiusCoeff X p.1 * selbergMoebiusCoeff X p.2
  have hgInj : ∀ a ∈ S, ∀ b ∈ S, g a = g b → a = b := by
    intro a _ha b _hb hab
    exact congrArg Prod.snd hab
  have hcoeff :
      selbergShortDirichletCollectedCoeff N X k =
        (B : ℂ) * (Real.sqrt (k : ℝ) : ℂ)⁻¹ := by
    rw [selbergShortDirichletCollectedCoeff,
      selbergShortDirichletTriples_eq_completeRangePairs_image hk1 hkN]
    change (∑ q ∈ S.image g, selbergShortDirichletTripleCoeff X q) = _
    calc
      (∑ q ∈ S.image g, selbergShortDirichletTripleCoeff X q) =
          ∑ p ∈ S, selbergShortDirichletTripleCoeff X (g p) := by
        exact Finset.sum_image
          (f := fun q : ℕ × (ℕ × ℕ) =>
            selbergShortDirichletTripleCoeff X q) hgInj
      _ = ∑ p ∈ S,
          ((selbergMoebiusCoeff X p.1 *
            selbergMoebiusCoeff X p.2 : ℝ) : ℂ) *
              (Real.sqrt (k : ℝ) : ℂ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpData : p ∈ selbergShortCompleteRangePairs X k := by
          simpa only [S] using hp
        have hdiv : p.1 * p.2 ∣ k :=
          (Finset.mem_filter.mp hpData).2
        have hprod : (k / (p.1 * p.2)) * p.1 * p.2 = k := by
          calc
            (k / (p.1 * p.2)) * p.1 * p.2 =
                (k / (p.1 * p.2)) * (p.1 * p.2) := by
                  simp [Nat.mul_assoc]
            _ = k := Nat.div_mul_cancel hdiv
        unfold g selbergShortDirichletTripleCoeff
        simp only
        rw [hprod]
        push_cast
        ring
      _ = (B : ℂ) * (Real.sqrt (k : ℝ) : ℂ)⁻¹ := by
        rw [← Finset.sum_mul]
        unfold B
        push_cast
        rfl
  have hconv := selbergShortDirichletCollectedCoeff_eq_convolution N X k
  have hfactor : (Real.sqrt (k : ℝ) : ℂ)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast hk1 : (0 : ℝ) < k)).ne'
  have hcast : (selbergShortCollectedDirichletConvolution N X k : ℂ) =
      (B : ℂ) := by
    apply mul_right_cancel₀ hfactor
    rw [← hconv, hcoeff]
  change selbergShortCollectedDirichletConvolution N X k = B
  exact_mod_cast hcast

end HardyTheorem
