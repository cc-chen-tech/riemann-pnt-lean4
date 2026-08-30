import HardyTheorem.AFEExplicitPoissonPrimalSum
import HardyTheorem.AFEExplicitPoissonFiniteTail
import HardyTheorem.AFEExplicitPoissonSqrtBands
import HardyTheorem.AFEExplicitPoissonCriticalEndpoints
import HardyTheorem.AFEExplicitPoissonInnerSum

/-! The complete finite-cutoff budget, before any limit in the upper cutoff. -/

open Complex

namespace HardyTheorem.AFE

noncomputable def explicitPoissonCriticalFiniteConstant (C₁ C₂ : ℝ) : ℝ :=
  6 + 5 * (12 * (4 * C₁ + 2) / Real.sqrt (Real.pi / 2) +
    4 * (1 + 4 * C₁) / Real.pi) +
    4 * explicitPoissonFarConstant C₁ C₂ (1 / 2) / Real.pi ^ 2 +
    (3 + 24 * C₁) / Real.pi

private theorem sum_Icc_split (f : ℕ → ℂ) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    (∑ n ∈ Finset.Icc a c, f n) =
      (∑ n ∈ Finset.Icc a b, f n) + ∑ n ∈ Finset.Icc (b + 1) c, f n := by
  have hset : Finset.Icc a c = Finset.Icc a b ∪ Finset.Icc (b + 1) c := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc a b) (Finset.Icc (b + 1) c) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    simp only [Finset.mem_Icc] at hn hm
    omega
  rw [hset, Finset.sum_union hdisj]

private theorem norm_signed_modes_sub_gamma_le
    (f : ℤ → ℂ) (G : ℕ → ℂ) (p : ℂ) {K M : ℕ} (hK : 6 ≤ K) (hM : K + 3 ≤ M) :
    ‖(∑' k : ℤ, f k) - p - (∑ m ∈ Finset.Icc 1 K, G m)‖ ≤
      ‖f 0 - p‖ + (∑ m ∈ Finset.Icc 1 M, ‖f (m : ℤ)‖) +
      (∑ m ∈ Finset.Icc 1 (K - 2), ‖f (-(m : ℤ)) - G m‖) +
      (∑ m ∈ Finset.Icc (K - 1) (K + 3), ‖f (-(m : ℤ))‖) +
      (∑ m ∈ Finset.Icc (K - 1) K, ‖G m‖) +
      (∑ m ∈ Finset.Icc (K + 4) M, ‖f (-(m : ℤ))‖) +
      ‖(∑' k : ℤ, f k) - f 0 - (∑ m ∈ Finset.Icc 1 M, f (m : ℤ)) -
        (∑ m ∈ Finset.Icc 1 M, f (-(m : ℤ)))‖ := by
  let P := ∑ m ∈ Finset.Icc 1 M, f (m : ℤ)
  let A := ∑ m ∈ Finset.Icc 1 (K - 2), (f (-(m : ℤ)) - G m)
  let B := ∑ m ∈ Finset.Icc (K - 1) (K + 3), f (-(m : ℤ))
  let C := ∑ m ∈ Finset.Icc (K - 1) K, G m
  let D := ∑ m ∈ Finset.Icc (K + 4) M, f (-(m : ℤ))
  let E := (∑' k : ℤ, f k) - f 0 - P - ∑ m ∈ Finset.Icc 1 M, f (-(m : ℤ))
  have hQ : (∑ m ∈ Finset.Icc 1 M, f (-(m : ℤ))) =
      (∑ m ∈ Finset.Icc 1 (K - 2), f (-(m : ℤ))) + B + D := by
    rw [sum_Icc_split _ (b := K - 2) (by omega) (by omega)]
    rw [show K - 2 + 1 = K - 1 by omega,
      sum_Icc_split _ (b := K + 3) (by omega) hM]
    dsimp only [B, D]
    ring
  have hG : (∑ m ∈ Finset.Icc 1 K, G m) =
      (∑ m ∈ Finset.Icc 1 (K - 2), G m) + C := by
    rw [sum_Icc_split _ (b := K - 2) (by omega) (by omega),
      show K - 2 + 1 = K - 1 by omega]
  have hid : (∑' k : ℤ, f k) - p - (∑ m ∈ Finset.Icc 1 K, G m) =
      (f 0 - p) + P + A + B - C + D + E := by
    dsimp only [E, A]
    rw [hQ, hG, Finset.sum_sub_distrib]
    ring
  rw [hid]
  have hnorm : ‖(f 0 - p) + P + A + B - C + D + E‖ ≤
      ‖f 0 - p‖ + ‖P‖ + ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖E‖ := by
    have h1 := norm_add_le (f 0 - p) P
    have h2 := norm_add_le ((f 0 - p) + P) A
    have h3 := norm_add_le ((f 0 - p) + P + A) B
    have h4 := norm_sub_le ((f 0 - p) + P + A + B) C
    have h5 := norm_add_le ((f 0 - p) + P + A + B - C) D
    have h6 := norm_add_le ((f 0 - p) + P + A + B - C + D) E
    linarith
  exact hnorm.trans (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add le_rfl (norm_sum_le _ _)) (norm_sum_le _ _))
    (norm_sum_le _ _)) (norm_sum_le _ _)) (norm_sum_le _ _)) le_rfl)

/-- The actual primal finite sum, pole subtraction and dual Gamma sum obey
the complete explicit budget.  All analytic component estimates are proved
internally; the only remaining cutoff dependence is the displayed decay. -/
theorem norm_dirichlet_sum_sub_pole_sub_dualGamma_le
    {C₁ C₂ t : ℝ} {K N : ℕ}
    (hK : 6 ≤ K) (hN : 2 * K ≤ N)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t)
    (htU : t ≤ 2 * Real.pi * ((K : ℝ) + 1) ^ 2)
    (hfar : 2 * t ≤ 2 * Real.pi * (N : ℝ))
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂) :
    let s : ℂ := (1 / 2 : ℂ) + I * t
    let M := Nat.ceil (t / (Real.pi * K))
    ‖((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - (N : ℂ) ^ (1 - s) / (1 - s)) -
        (∑ n ∈ Finset.Icc 1 K, (n : ℂ) ^ (-s)) -
        (∑ m ∈ Finset.Icc 1 K, poissonGammaTerm (1 / 2) t m)‖ ≤
      explicitPoissonCriticalFiniteConstant C₁ C₂ * (K : ℝ) ^ (-(1 / 2) : ℝ) *
          (1 + Real.log M) +
        ((K : ℝ) - 1 + (4 / Real.pi) * (harmonic (K - 2) : ℝ)) *
          (N : ℝ) ^ (-(1 / 2) : ℝ) := by
  let s : ℂ := (1 / 2 : ℂ) + I * t
  let M := Nat.ceil (t / (Real.pi * K))
  let f := explicitPoissonMode (1 / 2) ((K : ℝ) + 1) N t
  let G := poissonGammaTerm (1 / 2) t
  let p : ℂ := (N : ℂ) ^ (1 - s) / (1 - s)
  let R := (K : ℝ) ^ (-(1 / 2) : ℝ)
  let Z := (N : ℝ) ^ (-(1 / 2) : ℝ)
  let H := (harmonic (K - 2) : ℝ)
  let L := 1 + Real.log M
  let S := 12 * (4 * C₁ + 2) / Real.sqrt (Real.pi / 2) + 4 * (1 + 4 * C₁) / Real.pi
  let F := explicitPoissonFarConstant C₁ C₂ (1 / 2)
  let D := 6 + 5 * S + 4 * F / Real.pi ^ 2
  have hK6 : 6 ≤ (K : ℝ) := by exact_mod_cast hK
  have hNR : 2 * (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hKN : K + 1 ≤ N := by omega
  have ht0 : 0 ≤ t := (show 0 ≤ 2 * Real.pi * (K : ℝ) ^ 2 by positivity).trans htL
  have hM : 2 * K ≤ M := (sqrt_heightCell_frequency_cutoff hK htL htU).1
  have hL1 : 1 ≤ L := by
    have hM1 : 1 ≤ (M : ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
    have := Real.log_nonneg hM1
    dsimp only [L]
    linarith
  have hHL : H ≤ L := by
    have hlog : Real.log ((K - 2 : ℕ) : ℝ) ≤ Real.log M :=
      Real.log_le_log (by exact_mod_cast (show 0 < K - 2 by omega))
        (by exact_mod_cast (show K - 2 ≤ M by omega))
    exact (harmonic_le_one_add_log (K - 2)).trans (add_le_add le_rfl hlog)
  have hz := norm_explicitPoissonZeroMode_critical_sqrt_sub_main_le hK hNR htL
  have hp := sum_norm_explicitPoissonMode_positive_le_log M (sigma := (1 / 2 : ℝ))
    (by norm_num) (show 1 < (K : ℝ) + 1 by linarith)
    (show (K : ℝ) + 1 ≤ (N : ℝ) by exact_mod_cast hKN) ht0 hC₁0 hC₁
  simp only [show (K : ℝ) + 1 - 1 = (K : ℝ) by ring] at hp
  have hi := sum_norm_explicitPoissonMode_inner_sqrt_sub_gamma_le
    (sigma := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (show 3 ≤ K by omega)
    hKN htL hfar hC₁0 hC₁
  have he := sum_norm_explicitPoissonMode_five_sqrt_endpoints_le
    (sigma := (1 / 2 : ℝ)) (by norm_num) hK hNR htL htU hC₁0 hC₁
  have hg := sum_norm_poissonGammaTerm_two_endpoints_le t hK
  have ha := sum_norm_explicitPoissonMode_sqrt_above_le_log
    (sigma := (1 / 2 : ℝ)) (by norm_num) hK hNR htL htU hC₁0 hC₁
  have ht := norm_explicitPoisson_tsum_sub_finite_modes_le
    (sigma := (1 / 2 : ℝ)) (by norm_num) hK hNR htL htU hC₁0 hC₂0 hC₁ hC₂
  have hraw := norm_signed_modes_sub_gamma_le f G p hK (show K + 3 ≤ M by omega)
  have hnum := hraw.trans (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add hz hp) hi) he) hg) ha) ht)
  have hD0 : 0 ≤ D := by dsimp only [D, S, F, explicitPoissonFarConstant]; positivity
  have hDL : D * R ≤ D * R * L := le_mul_of_one_le_right (by positivity) hL1
  have hinnerL : ((3 + 8 * C₁) / Real.pi) * R * H ≤
      ((3 + 8 * C₁) / Real.pi) * R * L :=
    mul_le_mul_of_nonneg_left hHL (by dsimp only [R]; positivity)
  have hbound : ‖(∑' k : ℤ, f k) - p - ∑ m ∈ Finset.Icc 1 K, G m‖ ≤
      explicitPoissonCriticalFiniteConstant C₁ C₂ * R * L +
        ((K : ℝ) - 1 + (4 / Real.pi) * H) * Z := by
    calc
      _ ≤ (2 * R + Z) + (8 * C₁ * R / Real.pi) * L +
          (((3 + 8 * C₁) / Real.pi) * R * H +
            (((K - 2 : ℕ) : ℝ) + (4 / Real.pi) * H) * Z) +
          5 * S * R + 4 * R + (8 * C₁ * R / Real.pi) * L +
          4 * F * R / Real.pi ^ 2 := hnum
      _ = D * R + (16 * C₁ / Real.pi) * R * L +
          ((3 + 8 * C₁) / Real.pi) * R * H +
          ((K : ℝ) - 1 + (4 / Real.pi) * H) * Z := by
        rw [Nat.cast_sub (by omega : 2 ≤ K), Nat.cast_ofNat]
        dsimp only [D]
        ring
      _ ≤ D * R * L + (16 * C₁ / Real.pi) * R * L +
          ((3 + 8 * C₁) / Real.pi) * R * L +
          ((K : ℝ) - 1 + (4 / Real.pi) * H) * Z :=
        add_le_add (add_le_add (add_le_add hDL le_rfl) hinnerL) le_rfl
      _ = _ := by dsimp only [D, S, F, explicitPoissonCriticalFiniteConstant]; ring
  have hprimal := dirichlet_sum_sub_pole_eq_explicitPoisson_tsum
    (1 / 2) t (show 1 ≤ K by omega) hKN
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hprimal
  dsimp only
  rw [hprimal]
  exact hbound

end HardyTheorem.AFE
