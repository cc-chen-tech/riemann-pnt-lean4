import MathlibAux.GcdLcmLogQuadratic
import Mathlib.NumberTheory.Harmonic.Bounds

open scoped BigOperators

namespace MathlibAux

private theorem Icc_one_filter_dvd_eq_image_mul
    {N d : ℕ} (hd : 0 < d) :
    (Finset.Icc 1 N).filter (fun n => d ∣ n) =
      (Finset.Icc 1 (N / d)).image (fun k => d * k) := by
  classical
  ext n
  constructor
  · intro hn
    rcases Finset.mem_filter.mp hn with ⟨hnIcc, hdvd⟩
    rcases hdvd with ⟨k, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Nat.pos_of_mul_pos_left (Finset.mem_Icc.mp hnIcc).1
    · rw [Nat.le_div_iff_mul_le hd]
      simpa [Nat.mul_comm] using (Finset.mem_Icc.mp hnIcc).2
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      constructor
      · exact Nat.mul_pos hd (Finset.mem_Icc.mp hk).1
      · have hkUpper : k * d ≤ N :=
          (Nat.le_div_iff_mul_le hd).mp (Finset.mem_Icc.mp hk).2
        simpa [Nat.mul_comm] using hkUpper
    · exact dvd_mul_right d k

/-- The reciprocal mass of the positive multiples of `d` up to `N` is
exactly `H_(N/d) / d`. -/
theorem sum_inv_multiples_eq_inv_mul_harmonic
    {N d : ℕ} (hd : 0 < d) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), (n : ℝ)⁻¹) =
      (d : ℝ)⁻¹ * (harmonic (N / d) : ℝ) := by
  classical
  rw [Icc_one_filter_dvd_eq_image_mul hd]
  have hinj : Set.InjOn (fun k : ℕ => d * k) (Finset.Icc 1 (N / d)) := by
    intro a _ha b _hb hab
    exact Nat.mul_left_cancel hd hab
  calc
    (∑ n ∈ (Finset.Icc 1 (N / d)).image (fun k => d * k), (n : ℝ)⁻¹) =
        ∑ k ∈ Finset.Icc 1 (N / d), ((d * k : ℕ) : ℝ)⁻¹ := by
      exact Finset.sum_image hinj
    _ = ∑ k ∈ Finset.Icc 1 (N / d), (d : ℝ)⁻¹ * (k : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro k _hk
      simp only [Nat.cast_mul, mul_inv_rev]
      ring
    _ = (d : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 (N / d), (k : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
    _ = (d : ℝ)⁻¹ * (harmonic (N / d) : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]

private theorem harmonic_natCast_mono {m n : ℕ} (hmn : m ≤ n) :
    (harmonic m : ℝ) ≤ (harmonic n : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right hmn) (fun _ _ _ => by positivity)

private theorem harmonic_natCast_nonneg (n : ℕ) :
    0 ≤ (harmonic n : ℝ) := by
  simpa using harmonic_natCast_mono (Nat.zero_le n)

/-- The exact harmonic majorant needed after reciprocal-LCM
diagonalization is at most a cubic logarithm. -/
theorem sum_inv_mul_harmonic_sq_le_log_cube
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 N,
        (d : ℝ)⁻¹ * (harmonic (N / d) : ℝ) ^ 2) ≤
      (1 + Real.log N) ^ 3 := by
  have hH : (harmonic N : ℝ) ≤ 1 + Real.log N :=
    harmonic_le_one_add_log N
  have hH0 : 0 ≤ (harmonic N : ℝ) := harmonic_natCast_nonneg N
  have hlog0 : 0 ≤ Real.log N := by
    apply Real.log_nonneg
    exact_mod_cast hN
  calc
    (∑ d ∈ Finset.Icc 1 N,
        (d : ℝ)⁻¹ * (harmonic (N / d) : ℝ) ^ 2) ≤
        ∑ d ∈ Finset.Icc 1 N,
          (d : ℝ)⁻¹ * (harmonic N : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      have hdiv : N / d ≤ N := Nat.div_le_self N d
      have hmono := harmonic_natCast_mono hdiv
      have hsmall0 := harmonic_natCast_nonneg (N / d)
      gcongr
    _ = (harmonic N : ℝ) ^ 3 := by
      rw [← Finset.sum_mul]
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]
      ring
    _ ≤ (1 + Real.log N) ^ 3 := by
      gcongr

private theorem log_gcd_le_log_upper
    {N r s : ℕ} (hr : r ∈ Finset.Icc 1 N) :
    Real.log (Nat.gcd r s) ≤ Real.log N := by
  have hgcdPos : 0 < Nat.gcd r s :=
    Nat.gcd_pos_of_pos_left s (Finset.mem_Icc.mp hr).1
  apply Real.log_le_log (by exact_mod_cast hgcdPos)
  exact_mod_cast (Nat.gcd_le_left s (Finset.mem_Icc.mp hr).1).trans
    (Finset.mem_Icc.mp hr).2

private theorem abs_log_kernel_le
    {N r s : ℕ} (c : ℝ)
    (hr : r ∈ Finset.Icc 1 N) (hs : s ∈ Finset.Icc 1 N) :
    |c + 2 * Real.log (Nat.gcd r s) - Real.log r - Real.log s| ≤
      |c| + 4 * Real.log N := by
  have hrPos : 0 < r := (Finset.mem_Icc.mp hr).1
  have hsPos : 0 < s := (Finset.mem_Icc.mp hs).1
  have hgcdPos : 0 < Nat.gcd r s := Nat.gcd_pos_of_pos_left s hrPos
  have hlogr0 : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hrPos)
  have hlogs0 : 0 ≤ Real.log s := Real.log_nonneg (by exact_mod_cast hsPos)
  have hlogg0 : 0 ≤ Real.log (Nat.gcd r s) :=
    Real.log_nonneg (by exact_mod_cast hgcdPos)
  have hlogr : Real.log r ≤ Real.log N := by
    apply Real.log_le_log (by exact_mod_cast hrPos)
    exact_mod_cast (Finset.mem_Icc.mp hr).2
  have hlogs : Real.log s ≤ Real.log N := by
    apply Real.log_le_log (by exact_mod_cast hsPos)
    exact_mod_cast (Finset.mem_Icc.mp hs).2
  have hlogg := log_gcd_le_log_upper (s := s) hr
  calc
    |c + 2 * Real.log (Nat.gcd r s) - Real.log r - Real.log s| ≤
        |c| + |2 * Real.log (Nat.gcd r s)| + |Real.log r| + |Real.log s| := by
      calc
        _ ≤ |c + 2 * Real.log (Nat.gcd r s) - Real.log r| +
              |Real.log s| := abs_sub _ _
        _ ≤ |c + 2 * Real.log (Nat.gcd r s)| + |Real.log r| +
              |Real.log s| := by gcongr; exact abs_sub _ _
        _ ≤ |c| + |2 * Real.log (Nat.gcd r s)| + |Real.log r| +
              |Real.log s| := by gcongr; exact abs_add_le _ _
    _ = |c| + 2 * Real.log (Nat.gcd r s) + Real.log r + Real.log s := by
      rw [abs_of_nonneg hlogr0, abs_of_nonneg hlogs0,
        abs_of_nonneg (mul_nonneg (by norm_num) hlogg0)]
    _ ≤ |c| + 4 * Real.log N := by linarith

/-- F6 in exact harmonic form.  This proof estimates the original logarithmic
kernel directly, so it does not require an Euler-product formula for
`gcdLogWeight`. -/
theorem abs_sum_reciprocal_lcm_log_kernel_le_harmonic
    (a : ℕ → ℝ) (N : ℕ) (c : ℝ) (hN : 2 ≤ N)
    (ha : ∀ n ∈ Finset.Icc 1 N, |a n| ≤ 1) :
    |∑ r ∈ Finset.Icc 1 N, ∑ s ∈ Finset.Icc 1 N,
        a r * a s * (Nat.lcm r s : ℝ)⁻¹ *
          (c + 2 * Real.log (Nat.gcd r s) - Real.log r - Real.log s)| ≤
      (|c| + 4 * Real.log N) *
        ∑ d ∈ Finset.Icc 1 N,
          (d : ℝ)⁻¹ * (harmonic (N / d) : ℝ) ^ 2 := by
  classical
  let I := Finset.Icc 1 N
  let C := |c| + 4 * Real.log N
  have hN1 : 1 ≤ N := hN.trans' (by norm_num)
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hterm : ∀ r ∈ I, ∀ s ∈ I,
      |a r * a s * (Nat.lcm r s : ℝ)⁻¹ *
          (c + 2 * Real.log (Nat.gcd r s) - Real.log r - Real.log s)| ≤
        C * (Nat.lcm r s : ℝ)⁻¹ := by
    intro r hr s hs
    have hlcm0 : 0 ≤ (Nat.lcm r s : ℝ)⁻¹ := by positivity
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hlcm0]
    have hkernel := abs_log_kernel_le c hr hs
    have har := ha r hr
    have has := ha s hs
    calc
      |a r| * |a s| * (Nat.lcm r s : ℝ)⁻¹ *
          |c + 2 * Real.log (Nat.gcd r s) - Real.log r - Real.log s| ≤
          1 * 1 * (Nat.lcm r s : ℝ)⁻¹ * C := by gcongr
      _ = C * (Nat.lcm r s : ℝ)⁻¹ := by ring
  have htriangle :
      |∑ r ∈ I, ∑ s ∈ I,
          a r * a s * (Nat.lcm r s : ℝ)⁻¹ *
            (c + 2 * Real.log (Nat.gcd r s) - Real.log r - Real.log s)| ≤
        C * ∑ r ∈ I, ∑ s ∈ I, (Nat.lcm r s : ℝ)⁻¹ := by
    calc
      _ ≤ ∑ r ∈ I, |∑ s ∈ I,
          a r * a s * (Nat.lcm r s : ℝ)⁻¹ *
            (c + 2 * Real.log (Nat.gcd r s) - Real.log r - Real.log s)| :=
        Finset.abs_sum_le_sum_abs _ I
      _ ≤ ∑ r ∈ I, ∑ s ∈ I,
          |a r * a s * (Nat.lcm r s : ℝ)⁻¹ *
            (c + 2 * Real.log (Nat.gcd r s) - Real.log r - Real.log s)| := by
        apply Finset.sum_le_sum
        intro r hr
        exact Finset.abs_sum_le_sum_abs _ I
      _ ≤ ∑ r ∈ I, ∑ s ∈ I,
          C * (Nat.lcm r s : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro r hr
        apply Finset.sum_le_sum
        intro s hs
        exact hterm r hr s hs
      _ = C * ∑ r ∈ I, ∑ s ∈ I,
          (Nat.lcm r s : ℝ)⁻¹ := by
        simp_rw [Finset.mul_sum]
  have hdiag :
      (∑ r ∈ I, ∑ s ∈ I, (Nat.lcm r s : ℝ)⁻¹) =
        ∑ d ∈ I, (Nat.totient d : ℝ) *
          (∑ r ∈ I.filter (fun r => d ∣ r), (r : ℝ)⁻¹) ^ 2 := by
    simpa only [one_mul] using
      (sum_reciprocal_lcm_quadratic_eq_totient_squares
        (fun _ => (1 : ℝ)) N)
  have hmass :
      (∑ d ∈ I, (Nat.totient d : ℝ) *
          (∑ r ∈ I.filter (fun r => d ∣ r), (r : ℝ)⁻¹) ^ 2) ≤
        ∑ d ∈ I, (d : ℝ)⁻¹ *
          (harmonic (N / d) : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro d hd
    have hdPos : 0 < d := (Finset.mem_Icc.mp hd).1
    rw [sum_inv_multiples_eq_inv_mul_harmonic hdPos]
    have hphi : (Nat.totient d : ℝ) ≤ d := by
      exact_mod_cast d.totient_le
    have hdR : 0 < (d : ℝ) := by positivity
    have hcoeff : (Nat.totient d : ℝ) * (d : ℝ)⁻¹ ≤ 1 := by
      exact mul_inv_le_one_of_le₀ hphi (le_of_lt hdR)
    have hrest0 : 0 ≤ (d : ℝ)⁻¹ * (harmonic (N / d) : ℝ) ^ 2 := by
      positivity
    calc
      (Nat.totient d : ℝ) *
          ((d : ℝ)⁻¹ * (harmonic (N / d) : ℝ)) ^ 2 =
          ((Nat.totient d : ℝ) * (d : ℝ)⁻¹) *
            ((d : ℝ)⁻¹ * (harmonic (N / d) : ℝ) ^ 2) := by ring
      _ ≤ 1 * ((d : ℝ)⁻¹ * (harmonic (N / d) : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hcoeff hrest0
      _ = _ := by ring
  calc
    _ ≤ C * ∑ r ∈ I, ∑ s ∈ I, (Nat.lcm r s : ℝ)⁻¹ := htriangle
    _ = C * ∑ d ∈ I, (Nat.totient d : ℝ) *
          (∑ r ∈ I.filter (fun r => d ∣ r), (r : ℝ)⁻¹) ^ 2 := by rw [hdiag]
    _ ≤ C * ∑ d ∈ I, (d : ℝ)⁻¹ *
          (harmonic (N / d) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hmass hC0
    _ = _ := by rfl

/-- Closed logarithmic-cube form of F6.  The factor `4` is slightly sharper
than the factor `6` allowed in the research ledger. -/
theorem abs_sum_reciprocal_lcm_log_kernel_le_log_cube
    (a : ℕ → ℝ) (N : ℕ) (c : ℝ) (hN : 2 ≤ N)
    (ha : ∀ n ∈ Finset.Icc 1 N, |a n| ≤ 1) :
    |∑ r ∈ Finset.Icc 1 N, ∑ s ∈ Finset.Icc 1 N,
        a r * a s * (Nat.lcm r s : ℝ)⁻¹ *
          (c + 2 * Real.log (Nat.gcd r s) - Real.log r - Real.log s)| ≤
      (|c| + 4 * Real.log N) * (1 + Real.log N) ^ 3 := by
  have hfinite := abs_sum_reciprocal_lcm_log_kernel_le_harmonic a N c hN ha
  have hcube := sum_inv_mul_harmonic_sq_le_log_cube N (by omega)
  have hfactor : 0 ≤ |c| + 4 * Real.log N := by
    have : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    positivity
  exact hfinite.trans (mul_le_mul_of_nonneg_left hcube hfactor)

/-- The coefficient `6` formulation recorded as F6 in the research ledger.
It follows from the sharper coefficient `4` bound above. -/
theorem abs_sum_reciprocal_lcm_log_kernel_le_log_cube_six
    (a : ℕ → ℝ) (N : ℕ) (c : ℝ) (hN : 2 ≤ N)
    (ha : ∀ n ∈ Finset.Icc 1 N, |a n| ≤ 1) :
    |∑ r ∈ Finset.Icc 1 N, ∑ s ∈ Finset.Icc 1 N,
        a r * a s * (Nat.lcm r s : ℝ)⁻¹ *
          (c + 2 * Real.log (Nat.gcd r s) - Real.log r - Real.log s)| ≤
      (|c| + 6 * Real.log N) * (1 + Real.log N) ^ 3 := by
  have hfour := abs_sum_reciprocal_lcm_log_kernel_le_log_cube a N c hN ha
  have hlog0 : 0 ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  calc
    _ ≤ (|c| + 4 * Real.log N) * (1 + Real.log N) ^ 3 := hfour
    _ ≤ (|c| + 6 * Real.log N) * (1 + Real.log N) ^ 3 := by
      gcongr
      norm_num

end MathlibAux
