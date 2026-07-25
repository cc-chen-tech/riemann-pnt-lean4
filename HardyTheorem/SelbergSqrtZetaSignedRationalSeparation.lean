import HardyTheorem.SelbergSqrtZetaSignedRationalCollected
import MathlibAux.LogRatioLowerBound

/-!
# Separation of rational frequencies in the signed Selberg support

Each key is represented by `l / (m*d)` with `m ≤ N` and `d,l ≤ X`.
Distinct keys therefore have cross-products differing by a nonzero integer,
which gives an explicit real separation of at least `1 / (N*X)^2`.
-/

open scoped BigOperators

namespace HardyTheorem

private theorem one_div_sq_nat_mul_le_abs_sub_rationalKey
    {N X : ℕ} {p r : ℕ × (ℕ × ℕ)}
    (hp : p ∈ selbergSqrtZetaSignedPhaseSupport N X)
    (hr : r ∈ selbergSqrtZetaSignedPhaseSupport N X)
    (hne : selbergSqrtZetaSignedRationalKey p ≠
      selbergSqrtZetaSignedRationalKey r) :
    1 / (((N * X : ℕ) : ℝ) ^ 2) ≤
      |(selbergSqrtZetaSignedRationalKey p : ℝ) -
        (selbergSqrtZetaSignedRationalKey r : ℝ)| := by
  rcases Finset.mem_product.mp hp with ⟨hpm, hpdl⟩
  rcases Finset.mem_product.mp hpdl with ⟨hpd, hpl⟩
  rcases Finset.mem_product.mp hr with ⟨hrm, hrdl⟩
  rcases Finset.mem_product.mp hrdl with ⟨hrd, hrl⟩
  have hpmI := Finset.mem_Icc.mp hpm
  have hpdI := Finset.mem_Icc.mp hpd
  have hplI := Finset.mem_Icc.mp hpl
  have hrmI := Finset.mem_Icc.mp hrm
  have hrdI := Finset.mem_Icc.mp hrd
  have hrlI := Finset.mem_Icc.mp hrl
  let a : ℕ := p.2.2
  let b : ℕ := p.1 * p.2.1
  let c : ℕ := r.2.2
  let d : ℕ := r.1 * r.2.1
  have ha : 0 < a := by simpa only [a] using hplI.1
  have hb : 0 < b := by
    dsimp only [b]
    exact Nat.mul_pos hpmI.1 hpdI.1
  have hc : 0 < c := by simpa only [c] using hrlI.1
  have hd : 0 < d := by
    dsimp only [d]
    exact Nat.mul_pos hrmI.1 hrdI.1
  have hb_le : b ≤ N * X := by
    dsimp only [b]
    exact Nat.mul_le_mul hpmI.2 hpdI.2
  have hd_le : d ≤ N * X := by
    dsimp only [d]
    exact Nat.mul_le_mul hrmI.2 hrdI.2
  have hcross : a * d ≠ c * b := by
    intro hcrossEq
    apply hne
    unfold selbergSqrtZetaSignedRationalKey
    apply (div_eq_div_iff
      (by exact_mod_cast hb.ne')
      (by exact_mod_cast hd.ne')).2
    exact_mod_cast hcrossEq
  have hnum :
      (1 : ℝ) ≤ |((a * d : ℕ) : ℝ) - ((c * b : ℕ) : ℝ)| := by
    rcases lt_or_gt_of_ne hcross with hlt | hgt
    · have hstep : a * d + 1 ≤ c * b := Nat.succ_le_iff.mpr hlt
      have hstepR :
          (((a * d : ℕ) : ℝ) + 1) ≤ ((c * b : ℕ) : ℝ) := by
        exact_mod_cast hstep
      have hnonpos :
          ((a * d : ℕ) : ℝ) - ((c * b : ℕ) : ℝ) ≤ 0 := by
        linarith
      rw [abs_of_nonpos hnonpos]
      linarith
    · have hstep : c * b + 1 ≤ a * d := Nat.succ_le_iff.mpr hgt
      have hstepR :
          (((c * b : ℕ) : ℝ) + 1) ≤ ((a * d : ℕ) : ℝ) := by
        exact_mod_cast hstep
      have hnonneg :
          0 ≤ ((a * d : ℕ) : ℝ) - ((c * b : ℕ) : ℝ) := by
        linarith
      rw [abs_of_nonneg hnonneg]
      linarith
  have hden : 0 < (b : ℝ) * (d : ℝ) := by positivity
  have hden_le :
      (b : ℝ) * (d : ℝ) ≤ (((N * X : ℕ) : ℝ) ^ 2) := by
    have hbdNat : b * d ≤ (N * X) ^ 2 := by
      calc
        b * d ≤ (N * X) * (N * X) :=
          Nat.mul_le_mul hb_le hd_le
        _ = (N * X) ^ 2 := by ring
    exact_mod_cast hbdNat
  have hfrac :
      |(a : ℝ) / (b : ℝ) - (c : ℝ) / (d : ℝ)| =
        |((a * d : ℕ) : ℝ) - ((c * b : ℕ) : ℝ)| /
          ((b : ℝ) * (d : ℝ)) := by
    have hid :
        (a : ℝ) / (b : ℝ) - (c : ℝ) / (d : ℝ) =
          (((a * d : ℕ) : ℝ) - ((c * b : ℕ) : ℝ)) /
            ((b : ℝ) * (d : ℝ)) := by
      push_cast
      field_simp [show (b : ℝ) ≠ 0 by positivity,
        show (d : ℝ) ≠ 0 by positivity]
    rw [hid, abs_div, abs_of_pos hden]
  have hrecip :
      1 / (((N * X : ℕ) : ℝ) ^ 2) ≤
        1 / ((b : ℝ) * (d : ℝ)) :=
    one_div_le_one_div_of_le hden hden_le
  have hnumDiv :
      1 / ((b : ℝ) * (d : ℝ)) ≤
        |((a * d : ℕ) : ℝ) - ((c * b : ℕ) : ℝ)| /
          ((b : ℝ) * (d : ℝ)) :=
    div_le_div_of_nonneg_right hnum hden.le
  calc
    1 / (((N * X : ℕ) : ℝ) ^ 2) ≤
        1 / ((b : ℝ) * (d : ℝ)) := hrecip
    _ ≤ |((a * d : ℕ) : ℝ) - ((c * b : ℕ) : ℝ)| /
          ((b : ℝ) * (d : ℝ)) := hnumDiv
    _ = |(a : ℝ) / (b : ℝ) - (c : ℝ) / (d : ℝ)| := hfrac.symm
    _ = |(selbergSqrtZetaSignedRationalKey p : ℝ) -
          (selbergSqrtZetaSignedRationalKey r : ℝ)| := by
      simp only [selbergSqrtZetaSignedRationalKey, a, b, c, d,
        Rat.cast_div, Rat.cast_natCast]

/-- Any two distinct rational keys in the collected signed support are
separated in `ℝ` by at least `1 / (N*X)^2`. -/
theorem
    one_div_sq_nat_mul_le_abs_sub_of_mem_selbergSqrtZetaSignedRationalSupport
    {N X : ℕ} {q r : ℚ}
    (hq : q ∈ selbergSqrtZetaSignedRationalSupport N X)
    (hr : r ∈ selbergSqrtZetaSignedRationalSupport N X)
    (hne : q ≠ r) :
    1 / (((N * X : ℕ) : ℝ) ^ 2) ≤
      |(q : ℝ) - (r : ℝ)| := by
  classical
  rcases Finset.mem_image.mp hq with ⟨p, hp, hpq⟩
  rcases Finset.mem_image.mp hr with ⟨s, hs, hsr⟩
  subst q
  subst r
  exact one_div_sq_nat_mul_le_abs_sub_rationalKey hp hs hne

private theorem one_div_nat_mul_sq_le_abs_sub_rationalFrequency
    {N X : ℕ} {p r : ℕ × (ℕ × ℕ)}
    (hp : p ∈ selbergSqrtZetaSignedPhaseSupport N X)
    (hr : r ∈ selbergSqrtZetaSignedPhaseSupport N X)
    (hne : selbergSqrtZetaSignedRationalKey p ≠
      selbergSqrtZetaSignedRationalKey r) :
    1 / ((N * X ^ 2 : ℕ) : ℝ) ≤
      |selbergSqrtZetaSignedRationalFrequency
          (selbergSqrtZetaSignedRationalKey p) -
        selbergSqrtZetaSignedRationalFrequency
          (selbergSqrtZetaSignedRationalKey r)| := by
  rcases Finset.mem_product.mp hp with ⟨hpm, hpdl⟩
  rcases Finset.mem_product.mp hpdl with ⟨hpd, hpl⟩
  rcases Finset.mem_product.mp hr with ⟨hrm, hrdl⟩
  rcases Finset.mem_product.mp hrdl with ⟨hrd, hrl⟩
  have hpmI := Finset.mem_Icc.mp hpm
  have hpdI := Finset.mem_Icc.mp hpd
  have hplI := Finset.mem_Icc.mp hpl
  have hrmI := Finset.mem_Icc.mp hrm
  have hrdI := Finset.mem_Icc.mp hrd
  have hrlI := Finset.mem_Icc.mp hrl
  let a : ℕ := p.2.2
  let b : ℕ := p.1 * p.2.1
  let c : ℕ := r.2.2
  let d : ℕ := r.1 * r.2.1
  have ha : 0 < a := by simpa only [a] using hplI.1
  have hb : 0 < b := by
    dsimp only [b]
    exact Nat.mul_pos hpmI.1 hpdI.1
  have hc : 0 < c := by simpa only [c] using hrlI.1
  have hd : 0 < d := by
    dsimp only [d]
    exact Nat.mul_pos hrmI.1 hrdI.1
  have hb_le : b ≤ N * X := by
    dsimp only [b]
    exact Nat.mul_le_mul hpmI.2 hpdI.2
  have hd_le : d ≤ N * X := by
    dsimp only [d]
    exact Nat.mul_le_mul hrmI.2 hrdI.2
  have hcross : a * d ≠ c * b := by
    intro hcrossEq
    apply hne
    unfold selbergSqrtZetaSignedRationalKey
    apply (div_eq_div_iff
      (by exact_mod_cast hb.ne')
      (by exact_mod_cast hd.ne')).2
    exact_mod_cast hcrossEq
  have hnum :
      (1 : ℝ) ≤ |((a * d : ℕ) : ℝ) - ((c * b : ℕ) : ℝ)| := by
    rcases lt_or_gt_of_ne hcross with hlt | hgt
    · have hstep : a * d + 1 ≤ c * b := Nat.succ_le_iff.mpr hlt
      have hstepR :
          (((a * d : ℕ) : ℝ) + 1) ≤ ((c * b : ℕ) : ℝ) := by
        exact_mod_cast hstep
      have hnonpos :
          ((a * d : ℕ) : ℝ) - ((c * b : ℕ) : ℝ) ≤ 0 := by
        linarith
      rw [abs_of_nonpos hnonpos]
      linarith
    · have hstep : c * b + 1 ≤ a * d := Nat.succ_le_iff.mpr hgt
      have hstepR :
          (((c * b : ℕ) : ℝ) + 1) ≤ ((a * d : ℕ) : ℝ) := by
        exact_mod_cast hstep
      have hnonneg :
          0 ≤ ((a * d : ℕ) : ℝ) - ((c * b : ℕ) : ℝ) := by
        linarith
      rw [abs_of_nonneg hnonneg]
      linarith
  have had_le : a * d ≤ N * X ^ 2 := by
    calc
      a * d ≤ X * (N * X) := Nat.mul_le_mul hplI.2 hd_le
      _ = N * X ^ 2 := by ring
  have hcb_le : c * b ≤ N * X ^ 2 := by
    calc
      c * b ≤ X * (N * X) := Nat.mul_le_mul hrlI.2 hb_le
      _ = N * X ^ 2 := by ring
  have hx : 0 < ((a * d : ℕ) : ℝ) := by positivity
  have hy : 0 < ((c * b : ℕ) : ℝ) := by positivity
  have hmaxPos :
      0 < max (((a * d : ℕ) : ℝ)) (((c * b : ℕ) : ℝ)) :=
    lt_max_of_lt_left hx
  have hmaxLe :
      max (((a * d : ℕ) : ℝ)) (((c * b : ℕ) : ℝ)) ≤
        ((N * X ^ 2 : ℕ) : ℝ) := by
    apply max_le
    · exact_mod_cast had_le
    · exact_mod_cast hcb_le
  have hrecip :
      1 / ((N * X ^ 2 : ℕ) : ℝ) ≤
        1 / max (((a * d : ℕ) : ℝ)) (((c * b : ℕ) : ℝ)) :=
    one_div_le_one_div_of_le hmaxPos hmaxLe
  have hnumDiv :
      1 / max (((a * d : ℕ) : ℝ)) (((c * b : ℕ) : ℝ)) ≤
        |((a * d : ℕ) : ℝ) - ((c * b : ℕ) : ℝ)| /
          max (((a * d : ℕ) : ℝ)) (((c * b : ℕ) : ℝ)) :=
    div_le_div_of_nonneg_right hnum hmaxPos.le
  have hlog :=
    MathlibAux.abs_sub_div_max_le_abs_log_div hx hy
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
        selbergSqrtZetaSignedRationalFrequency
            (selbergSqrtZetaSignedRationalKey p) -
          selbergSqrtZetaSignedRationalFrequency
            (selbergSqrtZetaSignedRationalKey r) := by
    rw [hfreqCore]
    unfold selbergSqrtZetaSignedRationalFrequency
      selbergSqrtZetaSignedRationalKey
    simp only [a, b, c, d, Rat.cast_div, Rat.cast_natCast]
  calc
    1 / ((N * X ^ 2 : ℕ) : ℝ) ≤
        1 / max (((a * d : ℕ) : ℝ)) (((c * b : ℕ) : ℝ)) := hrecip
    _ ≤ |((a * d : ℕ) : ℝ) - ((c * b : ℕ) : ℝ)| /
          max (((a * d : ℕ) : ℝ)) (((c * b : ℕ) : ℝ)) := hnumDiv
    _ ≤ |Real.log (((a * d : ℕ) : ℝ) / ((c * b : ℕ) : ℝ))| := hlog
    _ = |selbergSqrtZetaSignedRationalFrequency
            (selbergSqrtZetaSignedRationalKey p) -
          selbergSqrtZetaSignedRationalFrequency
            (selbergSqrtZetaSignedRationalKey r)| := by rw [hfreq]

/-- Distinct collected rational keys have logarithmic frequencies separated
by at least `1 / (N*X^2)`.  This stronger logarithmic spacing is the form
used in near-stationary frequency counting. -/
theorem
    one_div_nat_mul_sq_le_abs_sub_frequency_of_mem_selbergSqrtZetaSignedRationalSupport
    {N X : ℕ} {q r : ℚ}
    (hq : q ∈ selbergSqrtZetaSignedRationalSupport N X)
    (hr : r ∈ selbergSqrtZetaSignedRationalSupport N X)
    (hne : q ≠ r) :
    1 / ((N * X ^ 2 : ℕ) : ℝ) ≤
      |selbergSqrtZetaSignedRationalFrequency q -
        selbergSqrtZetaSignedRationalFrequency r| := by
  classical
  rcases Finset.mem_image.mp hq with ⟨p, hp, hpq⟩
  rcases Finset.mem_image.mp hr with ⟨s, hs, hsr⟩
  subst q
  subst r
  exact one_div_nat_mul_sq_le_abs_sub_rationalFrequency hp hs hne

/-- Frequencies lying strictly within half the uniform logarithmic spacing
of a real center.  For `xi = -deriv thetaModel t`, this is the exceptional
near-stationary rational-frequency set. -/
noncomputable def selbergSqrtZetaSignedNearFrequencySupport
    (N X : ℕ) (xi : ℝ) : Finset ℚ :=
  (selbergSqrtZetaSignedRationalSupport N X).filter
    (fun q =>
      |selbergSqrtZetaSignedRationalFrequency q - xi| <
        1 / (2 * ((N * X ^ 2 : ℕ) : ℝ)))

/-- A half-spacing neighborhood of any real center contains at most one
collected rational frequency. -/
theorem card_selbergSqrtZetaSignedNearFrequencySupport_le_one
    {N X : ℕ} (hN : 0 < N) (hX : 0 < X) (xi : ℝ) :
    (selbergSqrtZetaSignedNearFrequencySupport N X xi).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro q hq r hr
  by_contra hne
  have hqData := Finset.mem_filter.mp hq
  have hrData := Finset.mem_filter.mp hr
  have hsep :=
    one_div_nat_mul_sq_le_abs_sub_frequency_of_mem_selbergSqrtZetaSignedRationalSupport
      hqData.1 hrData.1 hne
  let M : ℝ := ((N * X ^ 2 : ℕ) : ℝ)
  have hM : 0 < M := by
    dsimp only [M]
    exact_mod_cast Nat.mul_pos hN (pow_pos hX 2)
  have htri :
      |selbergSqrtZetaSignedRationalFrequency q -
          selbergSqrtZetaSignedRationalFrequency r| ≤
        |selbergSqrtZetaSignedRationalFrequency q - xi| +
          |selbergSqrtZetaSignedRationalFrequency r - xi| := by
    calc
      |selbergSqrtZetaSignedRationalFrequency q -
          selbergSqrtZetaSignedRationalFrequency r| =
          |(selbergSqrtZetaSignedRationalFrequency q - xi) +
            (xi - selbergSqrtZetaSignedRationalFrequency r)| := by ring
      _ ≤ |selbergSqrtZetaSignedRationalFrequency q - xi| +
          |xi - selbergSqrtZetaSignedRationalFrequency r| :=
        abs_add_le _ _
      _ = |selbergSqrtZetaSignedRationalFrequency q - xi| +
          |selbergSqrtZetaSignedRationalFrequency r - xi| := by
        rw [abs_sub_comm xi]
  have hradius :
      1 / (2 * M) + 1 / (2 * M) = 1 / M := by
    field_simp [hM.ne']
    ring
  have hnear :
      |selbergSqrtZetaSignedRationalFrequency q - xi| +
          |selbergSqrtZetaSignedRationalFrequency r - xi| <
        1 / M := by
    calc
      |selbergSqrtZetaSignedRationalFrequency q - xi| +
          |selbergSqrtZetaSignedRationalFrequency r - xi| <
          1 / (2 * M) + 1 / (2 * M) := by
        exact add_lt_add hqData.2 hrData.2
      _ = 1 / M := hradius
  have hlt :
      |selbergSqrtZetaSignedRationalFrequency q -
          selbergSqrtZetaSignedRationalFrequency r| <
        1 / M :=
    htri.trans_lt hnear
  exact (not_lt_of_ge (by simpa only [M] using hsep)) hlt

/-- The exceptional collected frequencies lying within half the uniform
spacing of the stationary center `-thetaModel'(t)`. -/
noncomputable def selbergSqrtZetaSignedNearStationarySupport
    (N X : ℕ) (t : ℝ) : Finset ℚ :=
  selbergSqrtZetaSignedNearFrequencySupport N X (-deriv thetaModel t)

/-- At any height there is at most one collected rational frequency within
half the uniform spacing of stationary phase. -/
theorem card_selbergSqrtZetaSignedNearStationarySupport_le_one
    {N X : ℕ} (hN : 0 < N) (hX : 0 < X) (t : ℝ) :
    (selbergSqrtZetaSignedNearStationarySupport N X t).card ≤ 1 := by
  exact card_selbergSqrtZetaSignedNearFrequencySupport_le_one
    hN hX (-deriv thetaModel t)

/-- Every supported frequency outside the exceptional stationary
neighborhood has tangent frequency at least half the uniform spacing. -/
theorem
    one_div_two_mul_nat_mul_sq_le_abs_thetaDerivative_add_frequency_of_mem_not_near
    {N X : ℕ} {q : ℚ} {t : ℝ}
    (hq : q ∈ selbergSqrtZetaSignedRationalSupport N X)
    (hqfar : q ∉ selbergSqrtZetaSignedNearStationarySupport N X t) :
    1 / (2 * ((N * X ^ 2 : ℕ) : ℝ)) ≤
      |deriv thetaModel t + selbergSqrtZetaSignedRationalFrequency q| := by
  unfold selbergSqrtZetaSignedNearStationarySupport
    selbergSqrtZetaSignedNearFrequencySupport at hqfar
  simp only [Finset.mem_filter, hq, true_and, not_lt] at hqfar
  simpa only [sub_neg_eq_add, add_comm] using hqfar

end HardyTheorem
