import MathlibAux.GcdLcmQuadratic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta BigOperators

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

private theorem sum_common_divisor_kernel_eq_weighted_products
    (I : Finset ℕ) (w b c : ℕ → ℝ) :
    (∑ r ∈ I, ∑ s ∈ I,
        ∑ d ∈ I.filter (fun d => d ∣ r ∧ d ∣ s),
          w d * b r * c s) =
      ∑ d ∈ I, w d *
        (∑ r ∈ I.filter (fun r => d ∣ r), b r) *
          (∑ s ∈ I.filter (fun s => d ∣ s), c s) := by
  classical
  calc
    _ = ∑ r ∈ I, ∑ s ∈ I, ∑ d ∈ I,
          if d ∣ r ∧ d ∣ s then w d * b r * c s else 0 := by
      simp_rw [Finset.sum_filter]
    _ = ∑ d ∈ I, ∑ r ∈ I, ∑ s ∈ I,
          if d ∣ r ∧ d ∣ s then w d * b r * c s else 0 := by
      calc
        _ = ∑ r ∈ I, ∑ d ∈ I, ∑ s ∈ I,
              if d ∣ r ∧ d ∣ s then w d * b r * c s else 0 := by
          apply Finset.sum_congr rfl
          intro r _hr
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = ∑ d ∈ I,
        ∑ r ∈ I.filter (fun r => d ∣ r),
          ∑ s ∈ I.filter (fun s => d ∣ s), w d * b r * c s := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases hdr : d ∣ r
      · simp only [hdr, true_and, if_true]
        rw [Finset.sum_filter]
      · simp [hdr]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _hd
      calc
        (∑ r ∈ I.filter (fun r => d ∣ r),
            ∑ s ∈ I.filter (fun s => d ∣ s), w d * b r * c s) =
            ∑ r ∈ I.filter (fun r => d ∣ r),
              (w d * b r) * ∑ s ∈ I.filter (fun s => d ∣ s), c s := by
          apply Finset.sum_congr rfl
          intro r _hr
          rw [Finset.mul_sum]
        _ = (∑ r ∈ I.filter (fun r => d ∣ r), w d * b r) *
              ∑ s ∈ I.filter (fun s => d ∣ s), c s := by
          rw [Finset.sum_mul]
        _ = w d * (∑ r ∈ I.filter (fun r => d ∣ r), b r) *
              ∑ s ∈ I.filter (fun s => d ∣ s), c s := by
          congr 1
          rw [Finset.mul_sum]

private theorem sum_sum_mul_const
    (I : Finset ℕ) (f : ℕ → ℕ → ℝ) (c : ℝ) :
    (∑ r ∈ I, ∑ s ∈ I, f r s * c) =
      (∑ r ∈ I, ∑ s ∈ I, f r s) * c := by
  simp_rw [Finset.sum_mul]

/-- Bilinear polarization of the reciprocal-LCM quadratic form. -/
theorem sum_reciprocal_lcm_bilinear_eq_totient_products
    (a b : ℕ → ℝ) (M : ℕ) :
    (∑ r ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 M,
        a r * b s * (Nat.lcm r s : ℝ)⁻¹) =
      ∑ d ∈ Finset.Icc 1 M, (Nat.totient d : ℝ) *
        (∑ r ∈ (Finset.Icc 1 M).filter (fun r => d ∣ r),
          a r * (r : ℝ)⁻¹) *
        (∑ s ∈ (Finset.Icc 1 M).filter (fun s => d ∣ s),
          b s * (s : ℝ)⁻¹) := by
  classical
  let I := Finset.Icc 1 M
  let ar : ℕ → ℝ := fun r => a r * (r : ℝ)⁻¹
  let bs : ℕ → ℝ := fun s => b s * (s : ℝ)⁻¹
  calc
    _ = ∑ r ∈ I, ∑ s ∈ I,
        ∑ d ∈ I.filter (fun d => d ∣ r ∧ d ∣ s),
          (Nat.totient d : ℝ) * ar r * bs s := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      have hrPos : 0 < r := (Finset.mem_Icc.mp hr).1
      have hsPos : 0 < s := (Finset.mem_Icc.mp hs).1
      rw [natCast_lcm_inv_eq_gcd_mul_inv_mul_inv hrPos hsPos]
      have hgcd := Nat.sum_totient (Nat.gcd r s)
      have hset :
          I.filter (fun d => d ∣ r ∧ d ∣ s) = (Nat.gcd r s).divisors := by
        ext d
        constructor
        · intro hd
          rcases Finset.mem_filter.mp hd with ⟨_hdI, hdr, hds⟩
          exact Nat.mem_divisors.mpr
            ⟨Nat.dvd_gcd hdr hds, Nat.ne_of_gt (Nat.gcd_pos_of_pos_left s hrPos)⟩
        · intro hd
          rcases Nat.mem_divisors.mp hd with ⟨hdg, hg0⟩
          have hdr := hdg.trans (Nat.gcd_dvd_left r s)
          have hds := hdg.trans (Nat.gcd_dvd_right r s)
          have hdPos := Nat.pos_of_dvd_of_pos hdg (Nat.gcd_pos_of_pos_left s hrPos)
          have hdM := (Nat.le_of_dvd hrPos hdr).trans (Finset.mem_Icc.mp hr).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdPos, hdM⟩, hdr, hds⟩
      rw [hset]
      change a r * b s * ((Nat.gcd r s : ℝ) * (r : ℝ)⁻¹ * (s : ℝ)⁻¹) = _
      rw [show (Nat.gcd r s : ℝ) =
        ∑ d ∈ (Nat.gcd r s).divisors, (Nat.totient d : ℝ) by exact_mod_cast hgcd.symm]
      calc
        a r * b s *
            ((∑ d ∈ (Nat.gcd r s).divisors, (Nat.totient d : ℝ)) *
              (r : ℝ)⁻¹ * (s : ℝ)⁻¹) =
            (∑ d ∈ (Nat.gcd r s).divisors, (Nat.totient d : ℝ)) *
              ar r * bs s := by dsimp [ar, bs]; ring
        _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]
    _ = ∑ d ∈ I, (Nat.totient d : ℝ) *
        (∑ r ∈ I.filter (fun r => d ∣ r), ar r) *
          (∑ s ∈ I.filter (fun s => d ∣ s), bs s) :=
      sum_common_divisor_kernel_eq_weighted_products I
        (fun d => (Nat.totient d : ℝ)) ar bs
    _ = _ := by rfl

private noncomputable def natMulLog : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ) * Real.log n, by simp⟩

/-- Möbius inverse of `n ↦ n log n`, the logarithmic gcd weight. -/
noncomputable def gcdLogWeight (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) * natMulLog) n

/-- Expanded divisor formula `sum_{k|n} mu(n/k) k log k`. -/
theorem gcdLogWeight_eq_sum (n : ℕ) :
    gcdLogWeight n =
      ∑ k ∈ n.divisors,
        (ArithmeticFunction.moebius (n / k) : ℝ) * (k : ℝ) * Real.log k := by
  unfold gcdLogWeight
  rw [ArithmeticFunction.mul_apply]
  change (∑ x ∈ n.divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.1 : ℝ) *
        ((x.2 : ℝ) * Real.log x.2)) = _
  simpa only [mul_assoc] using
    (Nat.sum_divisorsAntidiagonal'
      (n := n) (fun x y ↦ (ArithmeticFunction.moebius x : ℝ) *
        ((y : ℝ) * Real.log y)))

/-- Möbius inversion in the exact finite form used by the gcd-log kernel. -/
theorem sum_gcdLogWeight_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, gcdLogWeight d = (n : ℝ) * Real.log n := by
  unfold gcdLogWeight
  rw [← ArithmeticFunction.coe_zeta_mul_apply]
  rw [← mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul]
  rfl

@[simp] theorem gcdLogWeight_one : gcdLogWeight 1 = 0 := by
  simpa using sum_gcdLogWeight_divisors 1

theorem gcdLogWeight_two : gcdLogWeight 2 = 2 * Real.log 2 := by
  have h := sum_gcdLogWeight_divisors 2
  norm_num at h ⊢
  simpa using h

/-- One logarithmic index in the reciprocal-LCM form. -/
theorem sum_reciprocal_lcm_log_left_eq_totient_products
    (a : ℕ → ℝ) (M : ℕ) :
    (∑ r ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 M,
        a r * a s * (Nat.lcm r s : ℝ)⁻¹ * Real.log r) =
      ∑ d ∈ Finset.Icc 1 M, (Nat.totient d : ℝ) *
        (∑ r ∈ (Finset.Icc 1 M).filter (fun r => d ∣ r),
          a r * Real.log r * (r : ℝ)⁻¹) *
        (∑ s ∈ (Finset.Icc 1 M).filter (fun s => d ∣ s),
          a s * (s : ℝ)⁻¹) := by
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    sum_reciprocal_lcm_bilinear_eq_totient_products
      (fun r => a r * Real.log r) a M

/-- The gcd-log reciprocal-LCM form is a divisor square with `gcdLogWeight`. -/
theorem sum_reciprocal_lcm_log_gcd_eq_gcdLogWeight_squares
    (a : ℕ → ℝ) (M : ℕ) :
    (∑ r ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 M,
        a r * a s * (Nat.lcm r s : ℝ)⁻¹ * Real.log (Nat.gcd r s)) =
      ∑ d ∈ Finset.Icc 1 M, gcdLogWeight d *
        (∑ r ∈ (Finset.Icc 1 M).filter (fun r => d ∣ r),
          a r * (r : ℝ)⁻¹) ^ 2 := by
  classical
  let I := Finset.Icc 1 M
  let ar : ℕ → ℝ := fun r => a r * (r : ℝ)⁻¹
  calc
    _ = ∑ r ∈ I, ∑ s ∈ I,
        ∑ d ∈ I.filter (fun d => d ∣ r ∧ d ∣ s),
          gcdLogWeight d * ar r * ar s := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      have hrPos : 0 < r := (Finset.mem_Icc.mp hr).1
      have hsPos : 0 < s := (Finset.mem_Icc.mp hs).1
      rw [natCast_lcm_inv_eq_gcd_mul_inv_mul_inv hrPos hsPos]
      have hset :
          I.filter (fun d => d ∣ r ∧ d ∣ s) = (Nat.gcd r s).divisors := by
        ext d
        constructor
        · intro hd
          rcases Finset.mem_filter.mp hd with ⟨_hdI, hdr, hds⟩
          exact Nat.mem_divisors.mpr
            ⟨Nat.dvd_gcd hdr hds, Nat.ne_of_gt (Nat.gcd_pos_of_pos_left s hrPos)⟩
        · intro hd
          rcases Nat.mem_divisors.mp hd with ⟨hdg, hg0⟩
          have hdr := hdg.trans (Nat.gcd_dvd_left r s)
          have hds := hdg.trans (Nat.gcd_dvd_right r s)
          have hdPos := Nat.pos_of_dvd_of_pos hdg (Nat.gcd_pos_of_pos_left s hrPos)
          have hdM := (Nat.le_of_dvd hrPos hdr).trans (Finset.mem_Icc.mp hr).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdPos, hdM⟩, hdr, hds⟩
      rw [hset]
      calc
        a r * a s * ((Nat.gcd r s : ℝ) * (r : ℝ)⁻¹ * (s : ℝ)⁻¹) *
            Real.log (Nat.gcd r s) =
            (∑ d ∈ (Nat.gcd r s).divisors, gcdLogWeight d) * ar r * ar s := by
          rw [sum_gcdLogWeight_divisors]
          dsimp [ar]
          ring
        _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]
    _ = ∑ d ∈ I, gcdLogWeight d *
        (∑ r ∈ I.filter (fun r => d ∣ r), ar r) *
          (∑ s ∈ I.filter (fun s => d ∣ s), ar s) :=
      sum_common_divisor_kernel_eq_weighted_products I gcdLogWeight ar ar
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _hd
      simp only [I, ar, pow_two]
      ring

/-- Exact finite diagonalization of the full LCM-log kernel. -/
theorem sum_reciprocal_lcm_log_kernel_eq
    (a : ℕ → ℝ) (M : ℕ) (c : ℝ) :
    (∑ r ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 M,
        a r * a s * (Nat.lcm r s : ℝ)⁻¹ *
          (c + 2 * Real.log (Nat.gcd r s) - Real.log r - Real.log s)) =
      ∑ d ∈ Finset.Icc 1 M, (
        (c * (Nat.totient d : ℝ) + 2 * gcdLogWeight d) *
          (∑ r ∈ (Finset.Icc 1 M).filter (fun r => d ∣ r),
            a r * (r : ℝ)⁻¹) ^ 2 -
        2 * (Nat.totient d : ℝ) *
          (∑ r ∈ (Finset.Icc 1 M).filter (fun r => d ∣ r),
            a r * (r : ℝ)⁻¹) *
          (∑ r ∈ (Finset.Icc 1 M).filter (fun r => d ∣ r),
            a r * Real.log r * (r : ℝ)⁻¹)) := by
  classical
  have hbase := sum_reciprocal_lcm_quadratic_eq_totient_squares a M
  have hgcd := sum_reciprocal_lcm_log_gcd_eq_gcdLogWeight_squares a M
  have hleft := sum_reciprocal_lcm_log_left_eq_totient_products a M
  have hright :
      (∑ r ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 M,
          a r * a s * (Nat.lcm r s : ℝ)⁻¹ * Real.log s) =
        ∑ d ∈ Finset.Icc 1 M, (Nat.totient d : ℝ) *
          (∑ r ∈ (Finset.Icc 1 M).filter (fun r => d ∣ r),
            a r * (r : ℝ)⁻¹) *
          (∑ s ∈ (Finset.Icc 1 M).filter (fun s => d ∣ s),
            a s * Real.log s * (s : ℝ)⁻¹) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      sum_reciprocal_lcm_bilinear_eq_totient_products
        a (fun s => a s * Real.log s) M
  ring_nf
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_sum_mul_const, sum_sum_mul_const, hbase, hgcd, hleft, hright]
  rw [Finset.sum_mul, Finset.sum_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  ring

end MathlibAux
