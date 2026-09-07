import HardyTheorem.SelbergMollifiedDualPolynomial
import MathlibAux.GaussianSeparatedFrequency
import MathlibAux.LogRatioLowerBound

/-!
# Rational collection and spacing for the mollified dual AFE polynomial

Equal dual frequencies are exactly equal positive ratios `n/d`.  Collecting
by that rational key exposes the coprime-ray mass which remains to be bounded
arithmetically.  Distinct collected frequencies have the sharp elementary
spacing `1/(N*X)`.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace HardyTheorem

/-- The positive rational key of a dual pair `(n,d)`. -/
noncomputable def selbergMollifiedDualRationalKey (p : ℕ × ℕ) : ℚ :=
  (p.1 : ℚ) / (p.2 : ℚ)

/-- Rational keys actually occurring in the dual pair support. -/
noncomputable def selbergMollifiedDualRationalSupport
    (N X : ℕ) : Finset ℚ :=
  (selbergMollifiedDualSupport N X).image
    selbergMollifiedDualRationalKey

/-- Raw dual pairs in a single rational-frequency fiber. -/
noncomputable def selbergMollifiedDualRationalFiber
    (N X : ℕ) (q : ℚ) : Finset (ℕ × ℕ) :=
  (selbergMollifiedDualSupport N X).filter
    (fun p => selbergMollifiedDualRationalKey p = q)

/-- Signed coefficient collected at one rational key. -/
noncomputable def selbergMollifiedDualRationalCoeff
    (N X : ℕ) (q : ℚ) : ℂ :=
  ∑ p ∈ selbergMollifiedDualRationalFiber N X q,
    selbergMollifiedDualCoeff X p

/-- Absolute mass collected at one rational key. -/
noncomputable def selbergMollifiedDualRationalMass
    (N X : ℕ) (q : ℚ) : ℝ :=
  ∑ p ∈ selbergMollifiedDualRationalFiber N X q,
    selbergMollifiedDualMass X p

/-- Logarithmic frequency of a positive rational key. -/
noncomputable def selbergMollifiedDualRationalFrequency (q : ℚ) : ℝ :=
  Real.log (q : ℝ)

/-- The rationally collected dual polynomial. -/
noncomputable def selbergMollifiedDualRationalCollectedPolynomial
    (N X : ℕ) (t : ℝ) : ℂ :=
  MathlibAux.exponentialPolynomial
    (selbergMollifiedDualRationalSupport N X)
    (selbergMollifiedDualRationalCoeff N X)
    selbergMollifiedDualRationalFrequency t

theorem selbergMollifiedDualRationalKey_pos_of_mem
    {N X : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ selbergMollifiedDualSupport N X) :
    0 < selbergMollifiedDualRationalKey p := by
  rcases Finset.mem_product.mp hp with ⟨hn, hd⟩
  exact div_pos (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
    (by exact_mod_cast (Finset.mem_Icc.mp hd).1)

theorem selbergMollifiedDualFrequency_eq_rationalFrequency_key
    {N X : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ selbergMollifiedDualSupport N X) :
    selbergMollifiedDualFrequency p =
      selbergMollifiedDualRationalFrequency
        (selbergMollifiedDualRationalKey p) := by
  rcases Finset.mem_product.mp hp with ⟨hn, hd⟩
  have hn0 : (p.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
  have hd0 : (p.2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hd).1)
  unfold selbergMollifiedDualFrequency
    selbergMollifiedDualRationalFrequency selbergMollifiedDualRationalKey
  simp only [Rat.cast_div, Rat.cast_natCast]
  rw [Real.log_div hn0 hd0]

/-- Rational collection preserves the finite dual polynomial exactly. -/
theorem selbergMollifiedDualPolynomial_eq_rationalCollectedPolynomial
    (N X : ℕ) (t : ℝ) :
    selbergMollifiedDualPolynomial N X t =
      selbergMollifiedDualRationalCollectedPolynomial N X t := by
  classical
  let P := selbergMollifiedDualSupport N X
  let Q := selbergMollifiedDualRationalSupport N X
  let key := selbergMollifiedDualRationalKey
  let f : ℕ × ℕ → ℂ := fun p =>
    selbergMollifiedDualCoeff X p *
      Complex.exp (I * (selbergMollifiedDualFrequency p * t))
  have hmaps : ∀ p ∈ P, key p ∈ Q := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hfiber :
      (∑ p ∈ P, f p) =
        ∑ q ∈ Q, ∑ p ∈ P.filter (fun p => key p = q), f p := by
    symm
    exact Finset.sum_fiberwise_of_maps_to hmaps f
  unfold selbergMollifiedDualPolynomial
    selbergMollifiedDualRationalCollectedPolynomial
    MathlibAux.exponentialPolynomial
  calc
    (∑ p ∈ selbergMollifiedDualSupport N X,
        selbergMollifiedDualCoeff X p *
          Complex.exp (I * (selbergMollifiedDualFrequency p * t))) =
        ∑ p ∈ P, f p := by rfl
    _ = ∑ q ∈ Q, ∑ p ∈ P.filter (fun p => key p = q), f p := hfiber
    _ = ∑ q ∈ Q,
        selbergMollifiedDualRationalCoeff N X q *
          Complex.exp
            (I * (selbergMollifiedDualRationalFrequency q * t)) := by
      apply Finset.sum_congr rfl
      intro q hq
      calc
        (∑ p ∈ P.filter (fun p => key p = q), f p) =
            ∑ p ∈ P.filter (fun p => key p = q),
              selbergMollifiedDualCoeff X p *
                Complex.exp
                  (I * (selbergMollifiedDualRationalFrequency q * t)) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hpP : p ∈ selbergMollifiedDualSupport N X := by
            simpa only [P] using (Finset.mem_filter.mp hp).1
          have hpKey : selbergMollifiedDualRationalKey p = q := by
            simpa only [key] using (Finset.mem_filter.mp hp).2
          unfold f
          congr 2
          rw [selbergMollifiedDualFrequency_eq_rationalFrequency_key hpP,
            hpKey]
        _ = (∑ p ∈ P.filter (fun p => key p = q),
              selbergMollifiedDualCoeff X p) *
                Complex.exp
                  (I * (selbergMollifiedDualRationalFrequency q * t)) := by
          rw [Finset.sum_mul]
        _ = selbergMollifiedDualRationalCoeff N X q *
              Complex.exp
                (I * (selbergMollifiedDualRationalFrequency q * t)) := by
          congr 1

/-- Triangle inequality inside one rational ray. -/
theorem norm_selbergMollifiedDualRationalCoeff_le_mass
    (N X : ℕ) (q : ℚ) :
    ‖selbergMollifiedDualRationalCoeff N X q‖ ≤
      selbergMollifiedDualRationalMass N X q := by
  calc
    ‖selbergMollifiedDualRationalCoeff N X q‖ ≤
        ∑ p ∈ selbergMollifiedDualRationalFiber N X q,
          ‖selbergMollifiedDualCoeff X p‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ p ∈ selbergMollifiedDualRationalFiber N X q,
          selbergMollifiedDualMass X p := by
      apply Finset.sum_le_sum
      intro p hp
      exact norm_selbergMollifiedDualCoeff_le_mass
    _ = selbergMollifiedDualRationalMass N X q := rfl

private theorem one_div_nat_mul_le_abs_sub_dualRationalFrequency_key
    {N X : ℕ} {p r : ℕ × ℕ}
    (hp : p ∈ selbergMollifiedDualSupport N X)
    (hr : r ∈ selbergMollifiedDualSupport N X)
    (hne : selbergMollifiedDualRationalKey p ≠
      selbergMollifiedDualRationalKey r) :
    1 / ((N * X : ℕ) : ℝ) ≤
      |selbergMollifiedDualRationalFrequency
          (selbergMollifiedDualRationalKey p) -
        selbergMollifiedDualRationalFrequency
          (selbergMollifiedDualRationalKey r)| := by
  rcases Finset.mem_product.mp hp with ⟨hpn, hpd⟩
  rcases Finset.mem_product.mp hr with ⟨hrn, hrd⟩
  have hpnI := Finset.mem_Icc.mp hpn
  have hpdI := Finset.mem_Icc.mp hpd
  have hrnI := Finset.mem_Icc.mp hrn
  have hrdI := Finset.mem_Icc.mp hrd
  let a := p.1
  let b := p.2
  let c := r.1
  let d := r.2
  have ha : 0 < a := by simpa [a] using Nat.zero_lt_of_lt hpnI.1
  have hb : 0 < b := by simpa [b] using Nat.zero_lt_of_lt hpdI.1
  have hc : 0 < c := by simpa [c] using Nat.zero_lt_of_lt hrnI.1
  have hd : 0 < d := by simpa [d] using Nat.zero_lt_of_lt hrdI.1
  have hcross : a * d ≠ c * b := by
    intro hcrossEq
    apply hne
    unfold selbergMollifiedDualRationalKey
    apply (div_eq_div_iff
      (by exact_mod_cast hb.ne') (by exact_mod_cast hd.ne')).2
    exact_mod_cast hcrossEq
  have hnum :
      (1 : ℝ) ≤ |((a * d : ℕ) : ℝ) - ((c * b : ℕ) : ℝ)| := by
    rcases lt_or_gt_of_ne hcross with hlt | hgt
    · have hstep : a * d + 1 ≤ c * b := Nat.succ_le_iff.mpr hlt
      have hstepR : (((a * d : ℕ) : ℝ) + 1) ≤ ((c * b : ℕ) : ℝ) := by
        exact_mod_cast hstep
      have hnonpos :
          ((a * d : ℕ) : ℝ) - ((c * b : ℕ) : ℝ) ≤ 0 := by
        linarith [hstepR]
      rw [abs_of_nonpos hnonpos]
      linarith
    · have hstep : c * b + 1 ≤ a * d := Nat.succ_le_iff.mpr hgt
      have hstepR : (((c * b : ℕ) : ℝ) + 1) ≤ ((a * d : ℕ) : ℝ) := by
        exact_mod_cast hstep
      have hnonneg :
          0 ≤ ((a * d : ℕ) : ℝ) - ((c * b : ℕ) : ℝ) := by
        linarith [hstepR]
      rw [abs_of_nonneg hnonneg]
      linarith
  have hadLe : a * d ≤ N * X := Nat.mul_le_mul hpnI.2 hrdI.2
  have hcbLe : c * b ≤ N * X := Nat.mul_le_mul hrnI.2 hpdI.2
  have hx : 0 < ((a * d : ℕ) : ℝ) := by positivity
  have hy : 0 < ((c * b : ℕ) : ℝ) := by positivity
  have hmaxPos : 0 < max (((a * d : ℕ) : ℝ)) (((c * b : ℕ) : ℝ)) :=
    lt_max_of_lt_left hx
  have hmaxLe :
      max (((a * d : ℕ) : ℝ)) (((c * b : ℕ) : ℝ)) ≤
        ((N * X : ℕ) : ℝ) := by
    apply max_le
    · exact_mod_cast hadLe
    · exact_mod_cast hcbLe
  have hrecip :
      1 / ((N * X : ℕ) : ℝ) ≤
        1 / max (((a * d : ℕ) : ℝ)) (((c * b : ℕ) : ℝ)) :=
    one_div_le_one_div_of_le hmaxPos hmaxLe
  have hnumDiv :
      1 / max (((a * d : ℕ) : ℝ)) (((c * b : ℕ) : ℝ)) ≤
        |((a * d : ℕ) : ℝ) - ((c * b : ℕ) : ℝ)| /
          max (((a * d : ℕ) : ℝ)) (((c * b : ℕ) : ℝ)) :=
    div_le_div_of_nonneg_right hnum hmaxPos.le
  have hlog := MathlibAux.abs_sub_div_max_le_abs_log_div hx hy
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hc0 : (c : ℝ) ≠ 0 := by positivity
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hfreq :
      Real.log (((a * d : ℕ) : ℝ) / ((c * b : ℕ) : ℝ)) =
        selbergMollifiedDualRationalFrequency
            (selbergMollifiedDualRationalKey p) -
          selbergMollifiedDualRationalFrequency
            (selbergMollifiedDualRationalKey r) := by
    unfold selbergMollifiedDualRationalFrequency
      selbergMollifiedDualRationalKey
    simp only [Rat.cast_div, Rat.cast_natCast]
    push_cast
    rw [Real.log_div (mul_ne_zero ha0 hd0) (mul_ne_zero hc0 hb0),
      Real.log_mul ha0 hd0, Real.log_mul hc0 hb0,
      Real.log_div ha0 hb0, Real.log_div hc0 hd0]
    dsimp only [a, b, c, d]
    ring
  calc
    1 / ((N * X : ℕ) : ℝ) ≤
        1 / max (((a * d : ℕ) : ℝ)) (((c * b : ℕ) : ℝ)) := hrecip
    _ ≤ |((a * d : ℕ) : ℝ) - ((c * b : ℕ) : ℝ)| /
          max (((a * d : ℕ) : ℝ)) (((c * b : ℕ) : ℝ)) := hnumDiv
    _ ≤ |Real.log (((a * d : ℕ) : ℝ) / ((c * b : ℕ) : ℝ))| := hlog
    _ = _ := by rw [hfreq]

/-- Sharp elementary logarithmic spacing of distinct dual rational keys. -/
theorem one_div_nat_mul_le_abs_sub_dualRationalFrequency
    {N X : ℕ} {q r : ℚ}
    (hq : q ∈ selbergMollifiedDualRationalSupport N X)
    (hr : r ∈ selbergMollifiedDualRationalSupport N X)
    (hne : q ≠ r) :
    1 / ((N * X : ℕ) : ℝ) ≤
      |selbergMollifiedDualRationalFrequency q -
        selbergMollifiedDualRationalFrequency r| := by
  rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
  rcases Finset.mem_image.mp hr with ⟨r, hr, hkey⟩
  rw [← hkey]
  exact one_div_nat_mul_le_abs_sub_dualRationalFrequency_key hp hr
    (by simpa only [hkey] using hne)

/-- Every supported dual frequency is at least `-log X`. -/
theorem neg_log_X_le_dualRationalFrequency
    {N X : ℕ} {q : ℚ}
    (hq : q ∈ selbergMollifiedDualRationalSupport N X) :
    -Real.log X ≤ selbergMollifiedDualRationalFrequency q := by
  rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
  rcases Finset.mem_product.mp hp with ⟨hn, hd⟩
  have hnI := Finset.mem_Icc.mp hn
  have hdI := Finset.mem_Icc.mp hd
  rw [← selbergMollifiedDualFrequency_eq_rationalFrequency_key hp]
  unfold selbergMollifiedDualFrequency
  have hlogn : 0 ≤ Real.log p.1 := Real.log_nonneg (by exact_mod_cast hnI.1)
  have hdpos : (0 : ℝ) < p.2 := by exact_mod_cast hdI.1
  have hlogd : Real.log p.2 ≤ Real.log X :=
    Real.log_le_log hdpos (by exact_mod_cast hdI.2)
  linarith

/-- Gaussian mean square of the collected dual polynomial, reduced to the
explicit coprime-ray mass energy. -/
theorem
    integral_gaussian_normSq_selbergMollifiedDualPolynomial_le_rationalMassEnergy
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X)
    {Delta : ℝ} (hDelta : 2 * ((N * X : ℕ) : ℝ) ≤ Delta)
    (w : ℝ) :
    (∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq (selbergMollifiedDualPolynomial N X t)) ≤
      Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
        MathlibAux.gaussianBucketSchurConstant *
          ∑ q ∈ selbergMollifiedDualRationalSupport N X,
            (selbergMollifiedDualRationalMass N X q) ^ 2 := by
  have hNX : 0 < (N * X : ℕ) := Nat.mul_pos
    (Nat.zero_lt_of_lt hN) (Nat.zero_lt_of_lt hX)
  have hDeltaPos : 0 < Delta := by
    have : 0 < (2 : ℝ) * ((N * X : ℕ) : ℝ) := by positivity
    linarith
  rw [show (fun t : ℝ => Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
      Complex.normSq (selbergMollifiedDualPolynomial N X t)) =
      fun t : ℝ => Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (selbergMollifiedDualRationalCollectedPolynomial N X t) by
    funext t
    rw [selbergMollifiedDualPolynomial_eq_rationalCollectedPolynomial]]
  have hbase :=
    MathlibAux.integral_gaussian_mul_normSq_exponentialPolynomial_le_of_separated
      (selbergMollifiedDualRationalSupport N X)
      (selbergMollifiedDualRationalCoeff N X)
      selbergMollifiedDualRationalFrequency hDeltaPos w
      (lower := -Real.log X)
      (fun q hq => neg_log_X_le_dualRationalFrequency hq)
      (fun q hq r hr hne => by
        have hrecip : 2 / Delta ≤ 1 / (((N * X : ℕ) : ℝ)) := by
          apply (div_le_div_iff₀ hDeltaPos (by positivity)).2
          norm_num at hDelta ⊢
          nlinarith
        exact hrecip.trans
          (one_div_nat_mul_le_abs_sub_dualRationalFrequency hq hr hne))
  refine hbase.trans ?_
  have henergy :
      (∑ q ∈ selbergMollifiedDualRationalSupport N X,
          ‖selbergMollifiedDualRationalCoeff N X q‖ ^ 2) ≤
        ∑ q ∈ selbergMollifiedDualRationalSupport N X,
          (selbergMollifiedDualRationalMass N X q) ^ 2 := by
    apply Finset.sum_le_sum
    intro q hq
    have hmass : 0 ≤ selbergMollifiedDualRationalMass N X q := by
      unfold selbergMollifiedDualRationalMass
      apply Finset.sum_nonneg
      intro p hp
      unfold selbergMollifiedDualMass
      positivity
    exact (sq_le_sq₀ (norm_nonneg _) hmass).2
      (norm_selbergMollifiedDualRationalCoeff_le_mass N X q)
  have hfactor :
      0 ≤ Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
        MathlibAux.gaussianBucketSchurConstant :=
    mul_nonneg (Real.sqrt_nonneg _)
      MathlibAux.gaussianBucketSchurConstant_pos.le
  exact mul_le_mul_of_nonneg_left henergy hfactor

end HardyTheorem
