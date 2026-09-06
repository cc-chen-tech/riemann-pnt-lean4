import HardyTheorem.SelbergSqrtZetaSignedRationalLocalSeparationArithmetic
import HardyTheorem.SelbergSqrtZetaSignedRationalReducedRatio

/-!
# Pointwise reduced-ratio separation in the signed Selberg support

The global spacing `1 / (N * X^2)` ignores the reduced numerator and
denominator of the distinguished rational key.  For `q = a / b`, the
determinant against any other supported key gives the sharper pointwise
logarithmic spacing

`1 / (1 + X * min (a * N) b)`.

This is the geometric input needed before the local-separation weighted energy
can be reorganized ray by ray.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem

private theorem one_div_nat_min_add_one_le_abs_sub_div_max
    {x y : ℕ} (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) :
    1 / (((min x y + 1 : ℕ) : ℝ)) ≤
      |(x : ℝ) - (y : ℝ)| / max (x : ℝ) (y : ℝ) := by
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · have hstep : x + 1 ≤ y := Nat.succ_le_iff.mpr hxy
    have hstepR : (x : ℝ) + 1 ≤ (y : ℝ) := by exact_mod_cast hstep
    have hnonpos : (x : ℝ) - (y : ℝ) ≤ 0 := by linarith
    rw [Nat.min_eq_left hxy.le, max_eq_right (by exact_mod_cast hxy.le),
      abs_of_nonpos hnonpos]
    rw [neg_sub]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    push_cast
    nlinarith [show (0 : ℝ) ≤ x by positivity]
  · have hstep : y + 1 ≤ x := Nat.succ_le_iff.mpr hyx
    have hstepR : (y : ℝ) + 1 ≤ (x : ℝ) := by exact_mod_cast hstep
    have hnonneg : 0 ≤ (x : ℝ) - (y : ℝ) := by linarith
    rw [Nat.min_eq_right hyx.le, max_eq_left (by exact_mod_cast hyx.le),
      abs_of_nonneg hnonneg]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    push_cast
    nlinarith [show (0 : ℝ) ≤ y by positivity]

/-- A reduced key `a / b` is logarithmically separated from every distinct
supported rational key by its own numerator/denominator scale, rather than by
the global `N * X^2` scale. -/
theorem
    one_div_one_add_X_mul_min_le_abs_sub_frequency_reduced_of_mem
    {N X a b : ℕ} {r : ℚ}
    (ha : 0 < a) (hb : 0 < b)
    (hr : r ∈ selbergSqrtZetaSignedRationalSupport N X)
    (hne : (a : ℚ) / (b : ℚ) ≠ r) :
    1 / (((X * min (a * N) b + 1 : ℕ) : ℝ)) ≤
      |selbergSqrtZetaSignedRationalFrequency ((a : ℚ) / (b : ℚ)) -
        selbergSqrtZetaSignedRationalFrequency r| := by
  classical
  rcases Finset.mem_image.mp hr with ⟨p, hp, rfl⟩
  rcases Finset.mem_product.mp hp with ⟨hpm, hpdl⟩
  rcases Finset.mem_product.mp hpdl with ⟨hpd, hpl⟩
  have hpmI := Finset.mem_Icc.mp hpm
  have hpdI := Finset.mem_Icc.mp hpd
  have hplI := Finset.mem_Icc.mp hpl
  let c : ℕ := p.2.2
  let d : ℕ := p.1 * p.2.1
  have hc : 0 < c := by
    dsimp only [c]
    omega
  have hd : 0 < d := by
    dsimp only [d]
    exact Nat.mul_pos hpmI.1 hpdI.1
  have hc_le : c ≤ X := by simpa only [c] using hplI.2
  have hd_le : d ≤ N * X := by
    dsimp only [d]
    exact Nat.mul_le_mul hpmI.2 hpdI.2
  have hcross : a * d ≠ c * b := by
    intro hcrossEq
    apply hne
    unfold selbergSqrtZetaSignedRationalKey
    apply (div_eq_div_iff
      (by exact_mod_cast hb.ne')
      (by exact_mod_cast hd.ne')).2
    exact_mod_cast hcrossEq
  have had_le : a * d ≤ X * (a * N) := by
    calc
      a * d ≤ a * (N * X) := Nat.mul_le_mul_left a hd_le
      _ = X * (a * N) := by ring
  have hcb_le : c * b ≤ X * b := by
    exact Nat.mul_le_mul_right b hc_le
  have hmin_le :
      min (a * d) (c * b) ≤ X * min (a * N) b := by
    calc
      min (a * d) (c * b) ≤ min (X * (a * N)) (X * b) :=
        min_le_min had_le hcb_le
      _ = X * min (a * N) b := min_mul_mul_left X (a * N) b
  have hrecip :
      1 / (((X * min (a * N) b + 1 : ℕ) : ℝ)) ≤
        1 / (((min (a * d) (c * b) + 1 : ℕ) : ℝ)) := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.add_le_add_right hmin_le 1
  have hdet :=
    one_div_nat_min_add_one_le_abs_sub_div_max
      (Nat.mul_pos ha hd) (Nat.mul_pos hc hb) hcross
  have hlog :=
    MathlibAux.abs_sub_div_max_le_abs_log_div
      (show 0 < ((a * d : ℕ) : ℝ) by positivity)
      (show 0 < ((c * b : ℕ) : ℝ) by positivity)
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hc0 : (c : ℝ) ≠ 0 := by positivity
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hfreqCore :
      Real.log (((a * d : ℕ) : ℝ) / ((c * b : ℕ) : ℝ)) =
        Real.log ((a : ℝ) / (b : ℝ)) -
          Real.log ((c : ℝ) / (d : ℝ)) := by
    push_cast
    rw [Real.log_div (mul_ne_zero ha0 hd0) (mul_ne_zero hc0 hb0),
      Real.log_mul ha0 hd0, Real.log_mul hc0 hb0,
      Real.log_div ha0 hb0, Real.log_div hc0 hd0]
    ring
  have hfreq :
      Real.log (((a * d : ℕ) : ℝ) / ((c * b : ℕ) : ℝ)) =
        selbergSqrtZetaSignedRationalFrequency ((a : ℚ) / (b : ℚ)) -
          selbergSqrtZetaSignedRationalFrequency
            (selbergSqrtZetaSignedRationalKey p) := by
    rw [hfreqCore]
    unfold selbergSqrtZetaSignedRationalFrequency
      selbergSqrtZetaSignedRationalKey
    simp only [c, d, Rat.cast_div, Rat.cast_natCast]
  calc
    1 / (((X * min (a * N) b + 1 : ℕ) : ℝ)) ≤
        1 / (((min (a * d) (c * b) + 1 : ℕ) : ℝ)) := hrecip
    _ ≤ |((a * d : ℕ) : ℝ) - ((c * b : ℕ) : ℝ)| /
          max ((a * d : ℕ) : ℝ) ((c * b : ℕ) : ℝ) := hdet
    _ ≤ |Real.log (((a * d : ℕ) : ℝ) / ((c * b : ℕ) : ℝ))| := hlog
    _ = |selbergSqrtZetaSignedRationalFrequency ((a : ℚ) / (b : ℚ)) -
          selbergSqrtZetaSignedRationalFrequency
            (selbergSqrtZetaSignedRationalKey p)| := by rw [hfreq]

/-- The nearest-neighbour logarithmic separation at a supported reduced key
`a / b` is bounded below by `1 / (1 + X * min (a*N) b)`. -/
theorem one_div_one_add_X_mul_min_le_localFrequencySeparation_reduced
    {N X a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (_hab : Nat.Coprime a b)
    (hQ : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial)
    (_hq : (a : ℚ) / (b : ℚ) ∈
      selbergSqrtZetaSignedRationalSupport N X) :
    1 / (((X * min (a * N) b + 1 : ℕ) : ℝ)) ≤
      PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
        (selbergSqrtZetaSignedRationalSupport N X)
        selbergSqrtZetaSignedRationalFrequency
        ((a : ℚ) / (b : ℚ)) := by
  classical
  let Q := selbergSqrtZetaSignedRationalSupport N X
  have hErase : (Q.erase ((a : ℚ) / (b : ℚ))).Nonempty :=
    hQ.erase_nonempty
  rw [PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation,
    dif_pos hErase, Finset.le_inf'_iff]
  intro r hr
  have hrQ : r ∈ selbergSqrtZetaSignedRationalSupport N X :=
    Finset.mem_of_mem_erase hr
  have hrq : r ≠ (a : ℚ) / (b : ℚ) := (Finset.mem_erase.mp hr).1
  exact
    one_div_one_add_X_mul_min_le_abs_sub_frequency_reduced_of_mem
      ha hb hrQ hrq.symm

/-- Reciprocal form of the reduced local-separation bound. -/
theorem one_div_localFrequencySeparation_le_one_add_X_mul_min_reduced
    {N X a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hQ : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial)
    (hq : (a : ℚ) / (b : ℚ) ∈
      selbergSqrtZetaSignedRationalSupport N X) :
    1 /
        PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
          (selbergSqrtZetaSignedRationalSupport N X)
          selbergSqrtZetaSignedRationalFrequency
          ((a : ℚ) / (b : ℚ)) ≤
      ((X * min (a * N) b + 1 : ℕ) : ℝ) := by
  let Q := selbergSqrtZetaSignedRationalSupport N X
  let omega := selbergSqrtZetaSignedRationalFrequency
  let M : ℝ := ((X * min (a * N) b + 1 : ℕ) : ℝ)
  let delta :=
    PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
      Q omega ((a : ℚ) / (b : ℚ))
  have hM : 0 < M := by
    dsimp only [M]
    positivity
  have hinj : Set.InjOn omega (Q : Set ℚ) := by
    simpa only [Q, omega] using
      selbergSqrtZetaSignedRationalFrequency_injOn N X
  have hdelta : 0 < delta := by
    exact
      PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation_pos
        hQ hq hinj
  have hlocal : 1 / M ≤ delta := by
    simpa only [Q, omega, M, delta] using
      one_div_one_add_X_mul_min_le_localFrequencySeparation_reduced
        ha hb hab hQ hq
  change 1 / delta ≤ M
  apply (div_le_iff₀ hdelta).2
  calc
    (1 : ℝ) = M * (1 / M) := by field_simp [hM.ne']
    _ ≤ M * delta := mul_le_mul_of_nonneg_left hlocal hM.le

/-- One reduced-ratio summand in the local-separation weighted energy is
controlled by its pointwise geometric weight. -/
theorem normSq_div_localFrequencySeparation_le_reducedWeight
    {N X a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hQ : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial)
    (hq : (a : ℚ) / (b : ℚ) ∈
      selbergSqrtZetaSignedRationalSupport N X) :
    Complex.normSq
          (selbergSqrtZetaSignedRationalCoeff N X
            ((a : ℚ) / (b : ℚ))) /
        PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
          (selbergSqrtZetaSignedRationalSupport N X)
          selbergSqrtZetaSignedRationalFrequency
          ((a : ℚ) / (b : ℚ)) ≤
      ((X * min (a * N) b + 1 : ℕ) : ℝ) *
        Complex.normSq
          (selbergSqrtZetaSignedRationalCoeff N X
            ((a : ℚ) / (b : ℚ))) := by
  have hrecip :=
    one_div_localFrequencySeparation_le_one_add_X_mul_min_reduced
      ha hb hab hQ hq
  have hnorm :
      0 ≤ Complex.normSq
        (selbergSqrtZetaSignedRationalCoeff N X
          ((a : ℚ) / (b : ℚ))) :=
    Complex.normSq_nonneg _
  rw [div_eq_mul_inv]
  calc
    Complex.normSq
          (selbergSqrtZetaSignedRationalCoeff N X
            ((a : ℚ) / (b : ℚ))) *
        (PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
          (selbergSqrtZetaSignedRationalSupport N X)
          selbergSqrtZetaSignedRationalFrequency
          ((a : ℚ) / (b : ℚ)))⁻¹ ≤
      Complex.normSq
          (selbergSqrtZetaSignedRationalCoeff N X
            ((a : ℚ) / (b : ℚ))) *
        ((X * min (a * N) b + 1 : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hrecip) hnorm
    _ = ((X * min (a * N) b + 1 : ℕ) : ℝ) *
        Complex.normSq
          (selbergSqrtZetaSignedRationalCoeff N X
            ((a : ℚ) / (b : ℚ))) := by ring

end HardyTheorem
