import HardyTheorem.SelbergSqrtZetaShortExpansion
import HardyTheorem.SelbergSqrtZetaCoeffBound
import MathlibAux.DyadicHarmonic
import MathlibAux.ExponentialPolynomialFirstMoment

open Complex MeasureTheory
open scoped BigOperators

namespace HardyTheorem

/-!
# The finite right edge in Selberg's first-moment rectangle

This module treats the finite zeta truncation on `re(s) = 2`.  The unique
zero-frequency triple `(1,1,1)` contributes the interval length.  All other
triples have logarithmic frequency at least `log 2`; elementary oscillation
and `sum n⁻² ≤ 2` give the uniform remainder `16 / log 2`, independently of
the truncation height and mollifier length.

Passing from the finite zeta polynomial to `riemannZeta` is deliberately left
to the next module.
-/

/-- Coefficient of one uncollected `(m,d,l)` triple on `re(s)=2`. -/
noncomputable def selbergFirstMomentRightTripleCoeff
    (X : ℕ) (p : ℕ × (ℕ × ℕ)) : ℂ :=
  (selbergSqrtZetaTaperedCoeff X p.2.1 : ℂ) *
    (selbergSqrtZetaTaperedCoeff X p.2.2 : ℂ) /
      ((p.1 * p.2.1 * p.2.2 : ℕ) : ℂ) ^ (2 : ℕ)

/-- The finite three-factor exponential polynomial on `re(s)=2`. -/
noncomputable def selbergFirstMomentRightTriplePolynomial
    (N X : ℕ) (t : ℝ) : ℂ :=
  MathlibAux.exponentialPolynomial
    (selbergShortDirichletTripleSupport N X)
    (selbergFirstMomentRightTripleCoeff X)
    selbergShortDirichletTripleFrequency t

private theorem inv_nat_cpow_rightLine_eq_exp
    {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    1 / (n : ℂ) ^ ((2 : ℂ) + I * t) =
      ((n : ℂ) ^ (2 : ℕ))⁻¹ *
        Complex.exp ((-I * (Real.log n : ℂ)) * t) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [Complex.cpow_add _ _ hnC, one_div, mul_inv_rev]
  have htwo : (n : ℂ) ^ (2 : ℂ) = (n : ℂ) ^ (2 : ℕ) := by
    norm_num
  calc
    ((n : ℂ) ^ (I * t))⁻¹ * ((n : ℂ) ^ (2 : ℂ))⁻¹ =
        ((n : ℂ) ^ (2 : ℕ))⁻¹ * ((n : ℂ) ^ (I * t))⁻¹ := by
      rw [htwo]
      ac_rfl
    _ = ((n : ℂ) ^ (2 : ℕ))⁻¹ *
        Complex.exp ((-I * (Real.log n : ℂ)) * t) := by
      congr 1
      rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.exp_neg,
        ← Complex.natCast_log]
      congr 1
      ring

private theorem rightLineTripleTerm_eq_exponentialTerm
    {X m d l : ℕ} (hm : m ≠ 0) (hd : d ≠ 0) (hl : l ≠ 0)
    (t : ℝ) :
    (selbergSqrtZetaTaperedCoeff X d : ℂ) *
          (selbergSqrtZetaTaperedCoeff X l : ℂ) *
          (1 / ((m * d * l : ℕ) : ℂ) ^
            ((2 : ℂ) + I * t)) =
      selbergFirstMomentRightTripleCoeff X (m, d, l) *
        Complex.exp
          (I * (selbergShortDirichletTripleFrequency
            (m, d, l) * t)) := by
  have hprod : m * d * l ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero hm hd) hl
  rw [inv_nat_cpow_rightLine_eq_exp hprod t]
  unfold selbergFirstMomentRightTripleCoeff
  unfold selbergShortDirichletTripleFrequency
  dsimp only
  have hexp :
      Complex.exp
          ((-I * (Real.log ((m * d * l : ℕ) : ℝ) : ℂ)) * t) =
        Complex.exp
          (I * (((-Real.log ((m * d * l : ℕ) : ℝ) : ℝ) : ℂ) *
            (t : ℂ))) := by
    congr 1
    push_cast
    ring
  change
    (selbergSqrtZetaTaperedCoeff X d : ℂ) *
          (selbergSqrtZetaTaperedCoeff X l : ℂ) *
          (((((m * d * l : ℕ) : ℂ) ^ (2 : ℕ))⁻¹) *
            Complex.exp
              ((-I * (Real.log ((m * d * l : ℕ) : ℝ) : ℂ)) * t)) =
      ((selbergSqrtZetaTaperedCoeff X d : ℂ) *
          (selbergSqrtZetaTaperedCoeff X l : ℂ) /
            (((m * d * l : ℕ) : ℂ) ^ (2 : ℕ))) *
        Complex.exp
          (I * (((-Real.log ((m * d * l : ℕ) : ℝ) : ℝ) : ℂ) *
            (t : ℂ)))
  rw [hexp]
  ring

/-- Multiplying the three finite factors on `re(s)=2` gives the exact finite
right-edge exponential polynomial. -/
theorem finiteZeta_mul_sqrtZetaMollifier_sq_rightLine_eq
    (N X : ℕ) (t : ℝ) :
    ((∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((2 : ℂ) + I * t)) *
        selbergSqrtZetaMollifier X ((2 : ℂ) + I * t)) *
        selbergSqrtZetaMollifier X ((2 : ℂ) + I * t) =
      selbergFirstMomentRightTriplePolynomial N X t := by
  have htriple :
      ((∑ m ∈ Finset.Icc 1 N,
          1 / (m : ℂ) ^ ((2 : ℂ) + I * t)) *
          selbergSqrtZetaMollifier X ((2 : ℂ) + I * t)) *
          selbergSqrtZetaMollifier X ((2 : ℂ) + I * t) =
        ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 X,
          ∑ l ∈ Finset.Icc 1 X,
            (selbergSqrtZetaTaperedCoeff X d : ℂ) *
              (selbergSqrtZetaTaperedCoeff X l : ℂ) *
              (1 / ((m * d * l : ℕ) : ℂ) ^
                ((2 : ℂ) + I * t)) := by
    unfold selbergSqrtZetaMollifier selbergMollifier
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    rw [show (((m * d * l : ℕ) : ℂ)) =
        (((m * d : ℕ) : ℂ) * (l : ℂ)) by norm_num,
      Complex.natCast_mul_natCast_cpow (m * d) l,
      show (((m * d : ℕ) : ℂ)) = (m : ℂ) * (d : ℂ) by norm_num,
      Complex.natCast_mul_natCast_cpow m d]
    simp only [one_div, mul_inv_rev]
    ring
  rw [htriple]
  unfold selbergFirstMomentRightTriplePolynomial
  unfold MathlibAux.exponentialPolynomial
  unfold selbergShortDirichletTripleSupport
  let A := Finset.Icc 1 N
  let B := Finset.Icc 1 X
  let F : ℕ × (ℕ × ℕ) → ℂ := fun p =>
    selbergFirstMomentRightTripleCoeff X p *
      Complex.exp
        (I * (selbergShortDirichletTripleFrequency p * t))
  calc
    (∑ m ∈ A, ∑ d ∈ B, ∑ l ∈ B,
        (selbergSqrtZetaTaperedCoeff X d : ℂ) *
          (selbergSqrtZetaTaperedCoeff X l : ℂ) *
          (1 / ((m * d * l : ℕ) : ℂ) ^
            ((2 : ℂ) + I * t))) =
        ∑ m ∈ A, ∑ d ∈ B, ∑ l ∈ B, F (m, d, l) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro l hl
      exact rightLineTripleTerm_eq_exponentialTerm
        (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)
        (Nat.ne_of_gt (Finset.mem_Icc.mp hd).1)
        (Nat.ne_of_gt (Finset.mem_Icc.mp hl).1) t
    _ = ∑ m ∈ A, ∑ q ∈ B.product B, F (m, q) := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact (Finset.sum_product B B (fun q => F (m, q))).symm
    _ = ∑ p ∈ A.product (B.product B), F p :=
      (Finset.sum_product A (B.product B) F).symm

private theorem selbergFirstMomentRightTripleCoeff_one (X : ℕ) :
    selbergFirstMomentRightTripleCoeff X (1, (1, 1)) = 1 := by
  simp [selbergFirstMomentRightTripleCoeff]

private theorem selbergFirstMomentRightFrequency_ne_zero
    {N X : ℕ} (p : ℕ × (ℕ × ℕ))
    (hp : p ∈ (selbergShortDirichletTripleSupport N X).erase (1, (1, 1))) :
    selbergShortDirichletTripleFrequency p ≠ 0 := by
  rcases p with ⟨m, d, l⟩
  have hpSupport := (Finset.mem_erase.mp hp).2
  have hpNe := (Finset.mem_erase.mp hp).1
  rcases Finset.mem_product.mp hpSupport with ⟨hm, hdl⟩
  rcases Finset.mem_product.mp hdl with ⟨hd, hl⟩
  have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
  have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
  have hlpos : 0 < l := (Finset.mem_Icc.mp hl).1
  have hprodpos : (0 : ℝ) < (m * d * l : ℕ) := by positivity
  have hprodNe : (m * d * l : ℕ) ≠ 1 := by
    intro hprod
    have hmd_l := mul_eq_one.mp hprod
    have hm_d := mul_eq_one.mp hmd_l.1
    apply hpNe
    simp [hm_d.1, hm_d.2, hmd_l.2]
  unfold selbergShortDirichletTripleFrequency
  exact neg_ne_zero.mpr
    (Real.log_ne_zero_of_pos_of_ne_one hprodpos (by exact_mod_cast hprodNe))

private theorem rightTripleOscillatoryTerm_le
    {N X : ℕ} (hX : 2 ≤ X) (p : ℕ × (ℕ × ℕ))
    (hp : p ∈
      (selbergShortDirichletTripleSupport N X).erase (1, (1, 1))) :
    2 * ‖selbergFirstMomentRightTripleCoeff X p‖ /
        |selbergShortDirichletTripleFrequency p| ≤
      (2 / Real.log 2) *
        (((p.1 : ℝ) ^ 2)⁻¹ * (((p.2.1 : ℝ) ^ 2)⁻¹ *
          ((p.2.2 : ℝ) ^ 2)⁻¹)) := by
  rcases p with ⟨m, d, l⟩
  have hpSupport := (Finset.mem_erase.mp hp).2
  have hpNe := (Finset.mem_erase.mp hp).1
  rcases Finset.mem_product.mp hpSupport with ⟨hm, hdl⟩
  rcases Finset.mem_product.mp hdl with ⟨hd, hl⟩
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
  have hdX : d ≤ X := (Finset.mem_Icc.mp hd).2
  have hlX : l ≤ X := (Finset.mem_Icc.mp hl).2
  let q : ℕ := m * d * l
  have hqpos : 0 < q := by
    dsimp [q]
    exact Nat.mul_pos (Nat.mul_pos hm1 hd1) hl1
  have hqne : q ≠ 1 := by
    intro hq
    have hmd_l := mul_eq_one.mp hq
    have hm_d := mul_eq_one.mp hmd_l.1
    apply hpNe
    simp [hm_d.1, hm_d.2, hmd_l.2]
  have hq2 : 2 ≤ q := by omega
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq2)
  have hlogmono : Real.log 2 ≤ Real.log q :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq2)
  have hfreq : |selbergShortDirichletTripleFrequency (m, d, l)| =
      Real.log q := by
    unfold selbergShortDirichletTripleFrequency
    dsimp only [q]
    rw [abs_neg, abs_of_pos hlogq]
  have hbetaD := abs_selbergSqrtZetaTaperedCoeff_le_one hX hd1 hdX
  have hbetaL := abs_selbergSqrtZetaTaperedCoeff_le_one hX hl1 hlX
  have hbetaProd :
      |selbergSqrtZetaTaperedCoeff X d| *
          |selbergSqrtZetaTaperedCoeff X l| ≤ 1 := by
    calc
      |selbergSqrtZetaTaperedCoeff X d| *
          |selbergSqrtZetaTaperedCoeff X l| ≤ 1 * 1 :=
        mul_le_mul hbetaD hbetaL (abs_nonneg _) zero_le_one
      _ = 1 := by norm_num
  have hqSq : 0 < ((q : ℝ) ^ 2) := by positivity
  have hcoeff :
      ‖selbergFirstMomentRightTripleCoeff X (m, d, l)‖ ≤
        (((q : ℝ) ^ 2)⁻¹) := by
    unfold selbergFirstMomentRightTripleCoeff
    dsimp only
    rw [norm_div, norm_mul, norm_pow, norm_natCast]
    simp only [norm_real, Real.norm_eq_abs]
    change
      |selbergSqrtZetaTaperedCoeff X d| *
            |selbergSqrtZetaTaperedCoeff X l| /
          ((q : ℝ) ^ 2) ≤ ((q : ℝ) ^ 2)⁻¹
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right hbetaProd hqSq.le
  rw [hfreq]
  calc
    2 * ‖selbergFirstMomentRightTripleCoeff X (m, d, l)‖ /
          Real.log q ≤
        2 * (((q : ℝ) ^ 2)⁻¹) / Real.log q := by
      gcongr
    _ ≤ 2 * (((q : ℝ) ^ 2)⁻¹) / Real.log 2 := by
      exact div_le_div_of_nonneg_left (by positivity) hlog2 hlogmono
    _ = (2 / Real.log 2) *
        (((m : ℝ) ^ 2)⁻¹ *
          (((d : ℝ) ^ 2)⁻¹ * ((l : ℝ) ^ 2)⁻¹)) := by
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      have hd0 : (d : ℝ) ≠ 0 := by positivity
      have hl0 : (l : ℝ) ≠ 0 := by positivity
      dsimp [q]
      push_cast
      field_simp

/-- The finite right-edge remainder is bounded uniformly in both cutoffs. -/
theorem norm_intervalIntegral_selbergFirstMomentRightTriplePolynomial_sub_one_le
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) {a b : ℝ} :
    ‖∫ t in a..b,
        (selbergFirstMomentRightTriplePolynomial N X t - 1)‖ ≤
      16 / Real.log 2 := by
  let S := selbergShortDirichletTripleSupport N X
  let i0 : ℕ × (ℕ × ℕ) := (1, (1, 1))
  let major : ℕ × (ℕ × ℕ) → ℝ := fun p =>
    (2 / Real.log 2) *
      (((p.1 : ℝ) ^ 2)⁻¹ *
        (((p.2.1 : ℝ) ^ 2)⁻¹ * ((p.2.2 : ℝ) ^ 2)⁻¹))
  have hi0 : i0 ∈ S := by
    dsimp [i0, S, selbergShortDirichletTripleSupport]
    simp only [Finset.mem_product, Finset.mem_Icc]
    omega
  have hfreq0 : selbergShortDirichletTripleFrequency i0 = 0 := by
    simp [i0, selbergShortDirichletTripleFrequency]
  have hbase :=
    MathlibAux.norm_intervalIntegral_exponentialPolynomial_sub_distinguished_le
      S (selbergFirstMomentRightTripleCoeff X)
        selbergShortDirichletTripleFrequency i0 hi0
        (by simpa only [i0] using selbergFirstMomentRightTripleCoeff_one X)
        hfreq0 (by
          intro p hp
          exact selbergFirstMomentRightFrequency_ne_zero p (by
            simpa only [S, i0] using hp)) (a := a) (b := b)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hterm :
      (∑ p ∈ S.erase i0,
          2 * ‖selbergFirstMomentRightTripleCoeff X p‖ /
            |selbergShortDirichletTripleFrequency p|) ≤
        ∑ p ∈ S.erase i0, major p := by
    apply Finset.sum_le_sum
    intro p hp
    exact rightTripleOscillatoryTerm_le hX p (by
      simpa only [S, i0, major] using hp)
  have hextend :
      (∑ p ∈ S.erase i0, major p) ≤ ∑ p ∈ S, major p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i0 S)
    intro p _hp _hnot
    dsimp [major]
    positivity
  have hfactor :
      (∑ p ∈ S, major p) =
        (2 / Real.log 2) *
          ((∑ m ∈ Finset.Icc 1 N, (((m : ℝ) ^ 2))⁻¹) *
            ((∑ d ∈ Finset.Icc 1 X, (((d : ℝ) ^ 2))⁻¹) *
              (∑ l ∈ Finset.Icc 1 X, (((l : ℝ) ^ 2))⁻¹))) := by
    let A := Finset.Icc 1 N
    let B := Finset.Icc 1 X
    let C : ℝ := 2 / Real.log 2
    let fm : ℕ → ℝ := fun m => (((m : ℝ) ^ 2))⁻¹
    have hinner (m : ℕ) :
        (∑ d ∈ B, ∑ l ∈ B,
          C * (fm m * ((((d : ℝ) ^ 2))⁻¹ * (((l : ℝ) ^ 2))⁻¹))) =
        C * (fm m *
          ((∑ d ∈ B, (((d : ℝ) ^ 2))⁻¹) *
            (∑ l ∈ B, (((l : ℝ) ^ 2))⁻¹))) := by
      rw [show
        C * (fm m *
            ((∑ d ∈ B, (((d : ℝ) ^ 2))⁻¹) *
              (∑ l ∈ B, (((l : ℝ) ^ 2))⁻¹))) =
          ∑ d ∈ B, ∑ l ∈ B,
            C * (fm m * ((((d : ℝ) ^ 2))⁻¹ * (((l : ℝ) ^ 2))⁻¹)) by
        rw [Finset.sum_mul, Finset.mul_sum]
        simp_rw [Finset.mul_sum]]
    dsimp [S, selbergShortDirichletTripleSupport, major]
    rw [Finset.sum_product]
    simp_rw [Finset.sum_product]
    change
      (∑ m ∈ A, ∑ d ∈ B, ∑ l ∈ B,
        C * (fm m * ((((d : ℝ) ^ 2))⁻¹ * (((l : ℝ) ^ 2))⁻¹))) = _
    calc
      (∑ m ∈ A, ∑ d ∈ B, ∑ l ∈ B,
          C * (fm m * ((((d : ℝ) ^ 2))⁻¹ * (((l : ℝ) ^ 2))⁻¹))) =
        ∑ m ∈ A,
          C * (fm m *
            ((∑ d ∈ B, (((d : ℝ) ^ 2))⁻¹) *
              (∑ l ∈ B, (((l : ℝ) ^ 2))⁻¹))) := by
          apply Finset.sum_congr rfl
          intro m _hm
          exact hinner m
      _ = C * ((∑ m ∈ A, fm m) *
          ((∑ d ∈ B, (((d : ℝ) ^ 2))⁻¹) *
            (∑ l ∈ B, (((l : ℝ) ^ 2))⁻¹))) := by
          let K : ℝ :=
            (∑ d ∈ B, (((d : ℝ) ^ 2))⁻¹) *
              (∑ l ∈ B, (((l : ℝ) ^ 2))⁻¹)
          change (∑ m ∈ A, C * (fm m * K)) =
            C * ((∑ m ∈ A, fm m) * K)
          rw [Finset.sum_mul, Finset.mul_sum]
      _ = _ := by rfl
  have hsumN := MathlibAux.sum_inv_sq_Icc_one_le_two N
  have hsumX := MathlibAux.sum_inv_sq_Icc_one_le_two X
  calc
    ‖∫ t in a..b,
        (selbergFirstMomentRightTriplePolynomial N X t - 1)‖ ≤
        ∑ p ∈ S.erase i0,
          2 * ‖selbergFirstMomentRightTripleCoeff X p‖ /
            |selbergShortDirichletTripleFrequency p| := by
      simpa only [selbergFirstMomentRightTriplePolynomial, S, i0] using hbase
    _ ≤ ∑ p ∈ S.erase i0, major p := hterm
    _ ≤ ∑ p ∈ S, major p := hextend
    _ = (2 / Real.log 2) *
          ((∑ m ∈ Finset.Icc 1 N, (((m : ℝ) ^ 2))⁻¹) *
            ((∑ d ∈ Finset.Icc 1 X, (((d : ℝ) ^ 2))⁻¹) *
              (∑ l ∈ Finset.Icc 1 X, (((l : ℝ) ^ 2))⁻¹))) := hfactor
    _ ≤ (2 / Real.log 2) * (2 * (2 * 2)) := by
      gcongr
    _ = 16 / Real.log 2 := by ring

end HardyTheorem
