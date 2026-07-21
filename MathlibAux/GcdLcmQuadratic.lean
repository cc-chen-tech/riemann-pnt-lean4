import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace MathlibAux

private theorem natCast_lcm_inv_eq_gcd_mul_inv_mul_inv
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    (Nat.lcm r s : ℝ)⁻¹ =
      (Nat.gcd r s : ℝ) * (r : ℝ)⁻¹ * (s : ℝ)⁻¹ := by
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  have hs0 : (s : ℝ) ≠ 0 := by positivity
  have hlcm0 : (Nat.lcm r s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.lcm_pos hr hs))
  have hprod :
      (Nat.gcd r s : ℝ) * (Nat.lcm r s : ℝ) = (r : ℝ) * (s : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm r s
  field_simp
  nlinarith

private theorem natCast_gcd_eq_sum_totient_commonDivisors
    {M r s : ℕ} (hr : r ∈ Finset.Icc 1 M) :
    (Nat.gcd r s : ℝ) =
      ∑ d ∈ (Finset.Icc 1 M).filter (fun d => d ∣ r ∧ d ∣ s),
        (Nat.totient d : ℝ) := by
  classical
  have hrPos : 0 < r := (Finset.mem_Icc.mp hr).1
  have hgcdPos : 0 < Nat.gcd r s := Nat.gcd_pos_of_pos_left s hrPos
  have hset :
      (Finset.Icc 1 M).filter (fun d => d ∣ r ∧ d ∣ s) =
        (Nat.gcd r s).divisors := by
    ext d
    constructor
    · intro hd
      rcases Finset.mem_filter.mp hd with ⟨_hdBox, hdr, hds⟩
      exact Nat.mem_divisors.mpr
        ⟨Nat.dvd_gcd hdr hds, Nat.ne_of_gt hgcdPos⟩
    · intro hd
      rcases Nat.mem_divisors.mp hd with ⟨hdgcd, _hgcd0⟩
      have hdr : d ∣ r := hdgcd.trans (Nat.gcd_dvd_left r s)
      have hds : d ∣ s := hdgcd.trans (Nat.gcd_dvd_right r s)
      have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hdgcd hgcdPos
      have hdM : d ≤ M :=
        (Nat.le_of_dvd hrPos hdr).trans (Finset.mem_Icc.mp hr).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hdPos, hdM⟩, hdr, hds⟩
  rw [hset]
  exact_mod_cast (Nat.sum_totient (Nat.gcd r s)).symm

private theorem sum_common_divisor_kernel_eq_weighted_squares
    (I : Finset ℕ) (w b : ℕ → ℝ) :
    (∑ r ∈ I, ∑ s ∈ I,
        ∑ d ∈ I.filter (fun d => d ∣ r ∧ d ∣ s),
          w d * b r * b s) =
      ∑ d ∈ I, w d *
        (∑ r ∈ I.filter (fun r => d ∣ r), b r) ^ 2 := by
  classical
  calc
    (∑ r ∈ I, ∑ s ∈ I,
        ∑ d ∈ I.filter (fun d => d ∣ r ∧ d ∣ s),
          w d * b r * b s) =
        ∑ r ∈ I, ∑ s ∈ I, ∑ d ∈ I,
          if d ∣ r ∧ d ∣ s then w d * b r * b s else 0 := by
      simp_rw [Finset.sum_filter]
    _ = ∑ d ∈ I, ∑ r ∈ I, ∑ s ∈ I,
          if d ∣ r ∧ d ∣ s then w d * b r * b s else 0 := by
      calc
        (∑ r ∈ I, ∑ s ∈ I, ∑ d ∈ I,
            if d ∣ r ∧ d ∣ s then w d * b r * b s else 0) =
            ∑ r ∈ I, ∑ d ∈ I, ∑ s ∈ I,
              if d ∣ r ∧ d ∣ s then w d * b r * b s else 0 := by
          apply Finset.sum_congr rfl
          intro r _hr
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = ∑ d ∈ I,
        ∑ r ∈ I.filter (fun r => d ∣ r),
          ∑ s ∈ I.filter (fun s => d ∣ s), w d * b r * b s := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases hdr : d ∣ r
      · simp only [hdr, true_and, if_true]
        rw [Finset.sum_filter]
      · simp [hdr]
    _ = ∑ d ∈ I, w d *
        (∑ r ∈ I.filter (fun r => d ∣ r), b r) ^ 2 := by
      apply Finset.sum_congr rfl
      intro d _hd
      calc
        (∑ r ∈ I.filter (fun r => d ∣ r),
            ∑ s ∈ I.filter (fun s => d ∣ s), w d * b r * b s) =
            ∑ r ∈ I.filter (fun r => d ∣ r),
              (w d * b r) *
                ∑ s ∈ I.filter (fun s => d ∣ s), b s := by
          apply Finset.sum_congr rfl
          intro r _hr
          rw [Finset.mul_sum]
        _ = (∑ r ∈ I.filter (fun r => d ∣ r), w d * b r) *
              ∑ s ∈ I.filter (fun s => d ∣ s), b s := by
          rw [Finset.sum_mul]
        _ = w d * (∑ r ∈ I.filter (fun r => d ∣ r), b r) *
              ∑ s ∈ I.filter (fun s => d ∣ s), b s := by
          congr 1
          rw [Finset.mul_sum]
        _ = w d * (∑ r ∈ I.filter (fun r => d ∣ r), b r) ^ 2 := by
          rw [pow_two]
          ring

/-- The reciprocal-lcm quadratic form on a finite positive interval is the
sum of its Euler-totient divisor components. -/
theorem sum_reciprocal_lcm_quadratic_eq_totient_squares
    (a : ℕ → ℝ) (M : ℕ) :
    (∑ r ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 M,
        a r * a s * (Nat.lcm r s : ℝ)⁻¹) =
      ∑ d ∈ Finset.Icc 1 M, (Nat.totient d : ℝ) *
        (∑ r ∈ (Finset.Icc 1 M).filter (fun r => d ∣ r),
          a r * (r : ℝ)⁻¹) ^ 2 := by
  classical
  let I := Finset.Icc 1 M
  let b : ℕ → ℝ := fun r => a r * (r : ℝ)⁻¹
  calc
    (∑ r ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 M,
        a r * a s * (Nat.lcm r s : ℝ)⁻¹) =
        ∑ r ∈ I, ∑ s ∈ I,
          ∑ d ∈ I.filter (fun d => d ∣ r ∧ d ∣ s),
            (Nat.totient d : ℝ) * b r * b s := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      have hrPos : 0 < r := (Finset.mem_Icc.mp hr).1
      have hsPos : 0 < s := (Finset.mem_Icc.mp hs).1
      calc
        a r * a s * (Nat.lcm r s : ℝ)⁻¹ =
            (Nat.gcd r s : ℝ) * b r * b s := by
          rw [natCast_lcm_inv_eq_gcd_mul_inv_mul_inv hrPos hsPos]
          simp only [b]
          ring
        _ = (∑ d ∈ I.filter (fun d => d ∣ r ∧ d ∣ s),
              (Nat.totient d : ℝ)) * b r * b s := by
          rw [natCast_gcd_eq_sum_totient_commonDivisors hr]
        _ = ∑ d ∈ I.filter (fun d => d ∣ r ∧ d ∣ s),
              (Nat.totient d : ℝ) * b r * b s := by
          rw [Finset.sum_mul, Finset.sum_mul]
    _ = ∑ d ∈ I, (Nat.totient d : ℝ) *
        (∑ r ∈ I.filter (fun r => d ∣ r), b r) ^ 2 :=
      sum_common_divisor_kernel_eq_weighted_squares I
        (fun d => (Nat.totient d : ℝ)) b
    _ = ∑ d ∈ Finset.Icc 1 M, (Nat.totient d : ℝ) *
        (∑ r ∈ (Finset.Icc 1 M).filter (fun r => d ∣ r),
          a r * (r : ℝ)⁻¹) ^ 2 := by
      rfl

end MathlibAux
