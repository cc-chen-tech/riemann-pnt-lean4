import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.Harmonic.Bounds

open Complex Filter Topology

namespace PrimeNumberTheorem

/-- The remainder after subtracting `1` from an elementary factor in the
canonical product for `1 / Gamma`. -/
noncomputable def gammaCanonicalRemainder (n : ℕ) (z : ℂ) : ℂ :=
  (1 + z / (n + 1)) * Complex.exp (-z / (n + 1)) - 1

/-- The elementary factor in the canonical product for `1 / Gamma`. -/
noncomputable def gammaCanonicalFactor (n : ℕ) (z : ℂ) : ℂ :=
  1 + gammaCanonicalRemainder n z

private theorem norm_gammaCanonicalFactor_sub_one_le {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ‖(1 + u) * Complex.exp (-u) - 1‖ ≤ 3 * ‖u‖ ^ 2 := by
  have hneg : ‖-u‖ ≤ 1 := by simpa using hu
  have hrem : ‖Complex.exp (-u) - 1 - (-u)‖ ≤ ‖u‖ ^ 2 := by
    simpa using Complex.norm_exp_sub_one_sub_id_le hneg
  have hlin : ‖Complex.exp (-u) - 1‖ ≤ 2 * ‖u‖ := by
    simpa using Complex.norm_exp_sub_one_le hneg
  rw [show (1 + u) * Complex.exp (-u) - 1 =
      (Complex.exp (-u) - 1 - (-u)) -
        (-u) * (Complex.exp (-u) - 1) by ring]
  calc
    _ ≤ ‖Complex.exp (-u) - 1 - (-u)‖ +
        ‖(-u) * (Complex.exp (-u) - 1)‖ := norm_sub_le _ _
    _ ≤ ‖u‖ ^ 2 + ‖u‖ * (2 * ‖u‖) := by
      rw [norm_mul, norm_neg]
      exact add_le_add hrem (mul_le_mul_of_nonneg_left hlin (norm_nonneg _))
    _ = 3 * ‖u‖ ^ 2 := by ring

private theorem gammaCanonicalFactor_bound_aux {K : Set ℂ} (hK : IsCompact K) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ᶠ n in atTop, ∀ z ∈ K, ‖gammaCanonicalRemainder n z‖ ≤ u n := by
  have hf : ContinuousOn (fun z : ℂ => ‖z‖) K := by fun_prop
  obtain ⟨M, hM⟩ := bddAbove_def.mp (IsCompact.bddAbove_image hK hf)
  let A : ℝ := 3 * |M| ^ 2
  refine ⟨fun n : ℕ => ‖(A : ℂ) / ((n : ℂ) + 1) ^ 2‖, ?_, ?_⟩
  · simpa using summable_pow_div_add (A : ℂ) 2 1 one_lt_two
  · filter_upwards [eventually_ge_atTop ⌈|M|⌉₊] with n hn z hz
    have hzM : ‖z‖ ≤ |M| := (hM ‖z‖ ⟨z, hz, rfl⟩).trans (le_abs_self M)
    have hMn : |M| ≤ (n + 1 : ℝ) := by
      have hceil : |M| ≤ (⌈|M|⌉₊ : ℝ) := Nat.le_ceil |M|
      exact hceil.trans (by exact_mod_cast hn.trans (Nat.le_succ n))
    have hden : 0 < (n + 1 : ℝ) := by positivity
    have hu : ‖z / ((n + 1 : ℕ) : ℂ)‖ ≤ 1 := by
      rw [norm_div, Complex.norm_natCast]
      simpa only [Nat.cast_add, Nat.cast_one] using
        (div_le_one hden).mpr (hzM.trans hMn)
    have hmain := norm_gammaCanonicalFactor_sub_one_le hu
    rw [gammaCanonicalRemainder]
    have hmain' :
        ‖(1 + z / ((n : ℂ) + 1)) * Complex.exp (-z / ((n : ℂ) + 1)) - 1‖ ≤
          3 * ‖z / ((n : ℂ) + 1)‖ ^ 2 := by
      simpa [Nat.cast_add, Nat.cast_one, neg_div] using hmain
    refine hmain'.trans ?_
    have hA : 0 ≤ A := by dsimp [A]; positivity
    simp only [norm_div, norm_pow]
    rw [show ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 by
        rw [← ofReal_natCast, ← ofReal_one, ← ofReal_add, norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by positivity)],
      show ‖(A : ℂ)‖ = A by simpa using abs_of_nonneg hA]
    dsimp [A]
    have hsq : ‖z‖ ^ 2 ≤ |M| ^ 2 := by nlinarith [norm_nonneg z, abs_nonneg M]
    have hden0 : 0 ≤ (n + 1 : ℝ) ^ 2 := sq_nonneg _
    calc
      3 * (‖z‖ / (n + 1 : ℝ)) ^ 2 =
          3 * ‖z‖ ^ 2 / (n + 1 : ℝ) ^ 2 := by
        field_simp [hden.ne']
      _ ≤ 3 * |M| ^ 2 / (n + 1 : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq (by norm_num)) hden0
      _ = 3 * |M| ^ 2 / ((n : ℝ) + 1) ^ 2 := rfl

theorem multipliableLocallyUniformlyOn_gammaCanonicalFactor :
    MultipliableLocallyUniformlyOn gammaCanonicalFactor Set.univ := by
  refine ⟨fun z => ∏' n, gammaCanonicalFactor n z, ?_⟩
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _hK hcompact
  obtain ⟨u, hu, hbound⟩ := gammaCanonicalFactor_bound_aux hcompact
  exact Summable.hasProdUniformlyOn_nat_one_add hcompact hu hbound fun n => by
    change ContinuousOn (fun z : ℂ =>
      (1 + z / (n + 1)) * Complex.exp (-z / (n + 1)) - 1) K
    fun_prop

private theorem prod_gammaCanonicalFactor_eq (z : ℂ) (n : ℕ) :
    (∏ j ∈ Finset.range n, gammaCanonicalFactor j z) =
      (∏ j ∈ Finset.range n, (1 + z / ((j + 1 : ℕ) : ℂ))) *
        Complex.exp (-((harmonic n : ℚ) : ℂ) * z) := by
  induction n with
  | zero => simp [harmonic_zero]
  | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ih, harmonic_succ]
      simp only [gammaCanonicalFactor, gammaCanonicalRemainder]
      rw [show -((((harmonic n + (↑(n + 1))⁻¹ : ℚ) : ℂ))) * z =
          -((harmonic n : ℚ) : ℂ) * z + -z / ((n + 1 : ℕ) : ℂ) by
        have hk : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero n
        push_cast
        field_simp [hk]
        ring]
      rw [Complex.exp_add]
      push_cast
      ring

private theorem prod_one_add_div_eq (z : ℂ) (n : ℕ) :
    (∏ j ∈ Finset.range n, (1 + z / ((j + 1 : ℕ) : ℂ))) =
      (∏ j ∈ Finset.range n, (z + ((j + 1 : ℕ) : ℂ))) /
        ((Nat.factorial n : ℕ) : ℂ) := by
  calc
    (∏ j ∈ Finset.range n, (1 + z / ((j + 1 : ℕ) : ℂ))) =
        ∏ j ∈ Finset.range n,
          (z + ((j + 1 : ℕ) : ℂ)) / ((j + 1 : ℕ) : ℂ) := by
      apply Finset.prod_congr rfl
      intro j _hj
      have hj : (((j + 1 : ℕ) : ℂ)) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero j
      field_simp [hj]
      ring
    _ = (∏ j ∈ Finset.range n, (z + ((j + 1 : ℕ) : ℂ))) /
        ∏ j ∈ Finset.range n, (((j + 1 : ℕ) : ℂ)) :=
      Finset.prod_div_distrib _ _
    _ = (∏ j ∈ Finset.range n, (z + ((j + 1 : ℕ) : ℂ))) /
        ((Nat.factorial n : ℕ) : ℂ) := by
      congr 1
      rw [← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]

private theorem prod_range_gamma_shift (z : ℂ) (n : ℕ) :
    (∏ j ∈ Finset.range (n + 1), (z + (j : ℂ))) =
      z * ∏ j ∈ Finset.range n, (z + ((j + 1 : ℕ) : ℂ)) := by
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
  ring

private theorem inv_GammaSeq_mul_cpow_eq
    {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    (Complex.GammaSeq z n)⁻¹ * (n : ℂ) ^ z =
      z * ∏ j ∈ Finset.range n, (1 + z / ((j + 1 : ℕ) : ℂ)) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hpow : (n : ℂ) ^ z ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn))
  have hfac : (((Nat.factorial n : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hshift :
      (∏ j ∈ Finset.range n, (z + ((j + 1 : ℕ) : ℂ))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hjpos : 0 < (j + 1 : ℝ) := by positivity
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  rw [Complex.GammaSeq, prod_range_gamma_shift, prod_one_add_div_eq]
  field_simp [hz0, hpow, hfac, hshift]

private theorem canonicalPartialProduct_eq
    {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    z * Complex.exp (Real.eulerMascheroniConstant * z) *
        (∏ j ∈ Finset.range n, gammaCanonicalFactor j z) =
      (Complex.GammaSeq z n)⁻¹ *
        Complex.exp (((Real.eulerMascheroniConstant : ℂ) -
          ((harmonic n : ℚ) : ℂ) + Real.log n) * z) := by
  rw [prod_gammaCanonicalFactor_eq]
  have hseq := inv_GammaSeq_mul_cpow_eq hz hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hcpow : (n : ℂ) ^ z = Complex.exp ((Real.log n : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero hnC]
    have hncast : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
    rw [hncast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  calc
    z * Complex.exp (Real.eulerMascheroniConstant * z) *
        ((∏ j ∈ Finset.range n, (1 + z / ((j + 1 : ℕ) : ℂ))) *
          Complex.exp (-((harmonic n : ℚ) : ℂ) * z)) =
      (z * ∏ j ∈ Finset.range n, (1 + z / ((j + 1 : ℕ) : ℂ))) *
        (Complex.exp (Real.eulerMascheroniConstant * z) *
          Complex.exp (-((harmonic n : ℚ) : ℂ) * z)) := by ring
    _ = ((Complex.GammaSeq z n)⁻¹ * (n : ℂ) ^ z) *
        (Complex.exp (Real.eulerMascheroniConstant * z) *
          Complex.exp (-((harmonic n : ℚ) : ℂ) * z)) := by rw [hseq]
    _ = (Complex.GammaSeq z n)⁻¹ *
        Complex.exp (((Real.eulerMascheroniConstant : ℂ) -
          ((harmonic n : ℚ) : ℂ) + Real.log n) * z) := by
      rw [hcpow, ← Complex.exp_add]
      rw [show (Complex.GammaSeq z n)⁻¹ *
          Complex.exp ((Real.log n : ℂ) * z) *
            Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z +
              -((harmonic n : ℚ) : ℂ) * z) =
          (Complex.GammaSeq z n)⁻¹ *
            (Complex.exp ((Real.log n : ℂ) * z) *
              Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z +
                -((harmonic n : ℚ) : ℂ) * z)) by ring]
      rw [← Complex.exp_add]
      congr 2
      ring

/-- Weierstrass' canonical product for the reciprocal Gamma function, on the
right half-plane where Euler's `GammaSeq` limit can be used directly. -/
theorem gammaCanonicalProduct_eq_one_div_Gamma {z : ℂ} (hz : 0 < z.re) :
    z * Complex.exp (Real.eulerMascheroniConstant * z) *
        (∏' n : ℕ, gammaCanonicalFactor n z) = (Complex.Gamma z)⁻¹ := by
  have hGamma : Complex.Gamma z ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    linarith
  have hm :=
    multipliableLocallyUniformlyOn_gammaCanonicalFactor.multipliable
      (Set.mem_univ z)
  have hprod : Tendsto
      (fun n : ℕ => ∏ j ∈ Finset.range n, gammaCanonicalFactor j z)
      atTop (𝓝 (∏' j : ℕ, gammaCanonicalFactor j z)) :=
    (hm.hasProd_iff_tendsto_nat).mp ((hm.hasProd_iff).mpr rfl)
  have hleft : Tendsto
      (fun n : ℕ => z * Complex.exp (Real.eulerMascheroniConstant * z) *
        (∏ j ∈ Finset.range n, gammaCanonicalFactor j z))
      atTop (𝓝 (z * Complex.exp (Real.eulerMascheroniConstant * z) *
        (∏' j : ℕ, gammaCanonicalFactor j z))) :=
    (tendsto_const_nhds.mul tendsto_const_nhds).mul hprod
  have hcReal : Tendsto
      (fun n : ℕ => Real.eulerMascheroniConstant -
        (harmonic n : ℝ) + Real.log n) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => Real.eulerMascheroniConstant)
        atTop (𝓝 Real.eulerMascheroniConstant) := tendsto_const_nhds
    have h := hconst.sub Real.tendsto_harmonic_sub_log
    convert h using 1
    all_goals ring
  have hc : Tendsto
      (fun n : ℕ => (Real.eulerMascheroniConstant : ℂ) -
        ((harmonic n : ℚ) : ℂ) + ((Real.log (n : ℝ) : ℝ) : ℂ))
      atTop (𝓝 0) := by
    have h : Tendsto
        (fun n : ℕ => (((Real.eulerMascheroniConstant -
          (harmonic n : ℝ) + Real.log n) : ℝ) : ℂ)) atTop (𝓝 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp hcReal
    convert h using 1
    funext n
    push_cast
    rfl
  have hexp : Tendsto
      (fun n : ℕ => Complex.exp (((Real.eulerMascheroniConstant : ℂ) -
        ((harmonic n : ℚ) : ℂ) + ((Real.log (n : ℝ) : ℝ) : ℂ)) * z))
      atTop (𝓝 1) := by
    have hmul : Tendsto
        (fun n : ℕ => ((Real.eulerMascheroniConstant : ℂ) -
          ((harmonic n : ℚ) : ℂ) + ((Real.log (n : ℝ) : ℝ) : ℂ)) * z)
        atTop (𝓝 0) := by
      simpa only [zero_mul] using hc.mul_const z
    have h := (Complex.continuous_exp.tendsto 0).comp hmul
    convert h using 1
    simp
  have hright : Tendsto
      (fun n : ℕ => (Complex.GammaSeq z n)⁻¹ *
        Complex.exp (((Real.eulerMascheroniConstant : ℂ) -
          ((harmonic n : ℚ) : ℂ) + ((Real.log (n : ℝ) : ℝ) : ℂ)) * z))
      atTop (𝓝 ((Complex.Gamma z)⁻¹)) := by
    simpa using (Complex.GammaSeq_tendsto_Gamma z).inv₀ hGamma |>.mul hexp
  have hright' := hright.congr' (by
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact (canonicalPartialProduct_eq hz hn).symm)
  exact tendsto_nhds_unique hleft hright'

/-- The summand in Gauss' series for the digamma function. -/
noncomputable def digammaGaussTerm (z : ℂ) (n : ℕ) : ℂ :=
  (((n + 1 : ℕ) : ℂ))⁻¹ - (z + ((n + 1 : ℕ) : ℂ))⁻¹

private theorem digammaGaussTerm_eq {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    digammaGaussTerm z n =
      z / (((n + 1 : ℕ) : ℂ) * (z + ((n + 1 : ℕ) : ℂ))) := by
  have hk : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hzk : z + ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  simp only [digammaGaussTerm]
  field_simp [hk, hzk]
  ring

theorem norm_digammaGaussTerm_le_one_div
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ‖digammaGaussTerm z n‖ ≤ 1 / (n + 1 : ℝ) := by
  let k : ℂ := ((n + 1 : ℕ) : ℂ)
  have hkpos : 0 < (n + 1 : ℝ) := by positivity
  have hnorm : ‖z‖ ≤ ‖z + k‖ := by
    apply (sq_le_sq₀ (norm_nonneg z) (norm_nonneg (z + k))).mp
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply, k]
    nlinarith
  rw [digammaGaussTerm_eq hz, norm_div, norm_mul]
  rw [show ‖(((n + 1 : ℕ) : ℂ))‖ = (n + 1 : ℝ) by
    rw [Complex.norm_natCast]
    norm_num]
  have hzkpos : 0 < ‖z + k‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hre := congrArg Complex.re h
    simp [k] at hre
    linarith
  calc
    ‖z‖ / ((n + 1 : ℝ) * ‖z + k‖) ≤
        ‖z + k‖ / ((n + 1 : ℝ) * ‖z + k‖) :=
      div_le_div_of_nonneg_right hnorm (by positivity)
    _ = 1 / (n + 1 : ℝ) := by field_simp [hkpos.ne', hzkpos.ne']

theorem norm_digammaGaussTerm_le_norm_div_sq
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ‖digammaGaussTerm z n‖ ≤ ‖z‖ / (n + 1 : ℝ) ^ 2 := by
  let k : ℂ := ((n + 1 : ℕ) : ℂ)
  have hkpos : 0 < (n + 1 : ℝ) := by positivity
  have hkNorm : (n + 1 : ℝ) ≤ ‖z + k‖ := by
    have hre : (n + 1 : ℝ) ≤ (z + k).re := by
      dsimp [k]
      simp
      exact hz.le
    exact hre.trans (le_abs_self _ |>.trans (Complex.abs_re_le_norm _))
  rw [digammaGaussTerm_eq hz, norm_div, norm_mul]
  rw [show ‖(((n + 1 : ℕ) : ℂ))‖ = (n + 1 : ℝ) by
    rw [Complex.norm_natCast]
    norm_num]
  dsimp [k] at hkNorm
  push_cast at hkNorm
  exact div_le_div_of_nonneg_left (norm_nonneg z) (sq_pos_of_pos hkpos)
    (by simpa [pow_two] using mul_le_mul_of_nonneg_left hkNorm hkpos.le)

private theorem gammaCanonicalFactor_ne_zero
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) : gammaCanonicalFactor n z ≠ 0 := by
  have hlin : 1 + z / (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have hre' : 1 + z.re / (n + 1 : ℝ) = 0 := by
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
      rw [show ((n + 1 : ℕ) : ℂ) = ((n + 1 : ℝ) : ℂ) by norm_num,
        Complex.div_ofReal_re] at hre
      simpa only [Nat.cast_add, Nat.cast_one] using hre
    have : 0 < 1 + z.re / (n + 1 : ℝ) := by positivity
    exact this.ne' hre'
  rw [show gammaCanonicalFactor n z =
      (1 + z / (((n + 1 : ℕ) : ℂ))) *
        Complex.exp (-z / (((n + 1 : ℕ) : ℂ))) by
    simp only [gammaCanonicalFactor, gammaCanonicalRemainder]
    push_cast
    ring]
  exact mul_ne_zero hlin (Complex.exp_ne_zero _)

private theorem logDeriv_gammaCanonicalFactor
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    logDeriv (gammaCanonicalFactor n) z = -digammaGaussTerm z n := by
  let k : ℂ := ((n + 1 : ℕ) : ℂ)
  have hk : k ≠ 0 := by
    dsimp [k]
    exact_mod_cast Nat.succ_ne_zero n
  have hlin : 1 + z / k ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have hre' : 1 + z.re / (n + 1 : ℝ) = 0 := by
      dsimp [k] at hre
      rw [show ((n + 1 : ℕ) : ℂ) = ((n + 1 : ℝ) : ℂ) by norm_num,
        Complex.div_ofReal_re] at hre
      simpa only [Nat.cast_add, Nat.cast_one] using hre
    have hkpos : 0 < (n + 1 : ℝ) := by positivity
    have : 0 < 1 + z.re / (n + 1 : ℝ) := by positivity
    exact this.ne' hre'
  have hfactor : gammaCanonicalFactor n =
      fun w : ℂ => (1 + w / k) * Complex.exp (-w / k) := by
    funext w
    simp [gammaCanonicalFactor, gammaCanonicalRemainder, k]
  rw [hfactor, logDeriv_mul
    (f := fun w : ℂ => 1 + w / k)
    (g := fun w : ℂ => Complex.exp (-w / k))
    z hlin (Complex.exp_ne_zero _) (by fun_prop) (by fun_prop)]
  simp only [logDeriv_apply]
  rw [show deriv (fun w : ℂ => 1 + w / k) z = 1 / k by
      convert ((hasDerivAt_const z 1).add ((hasDerivAt_id z).div_const k)).deriv using 1
      all_goals simp]
  rw [show deriv (fun w : ℂ => Complex.exp (-w / k)) z =
      (-1 / k) * Complex.exp (-z / k) by
      convert (((hasDerivAt_neg z).div_const k).cexp).deriv using 1
      all_goals ring]
  simp only [digammaGaussTerm]
  field_simp [hk, hlin]
  ring

theorem summable_digammaGaussTerm {z : ℂ} (hz : 0 < z.re) :
    Summable (digammaGaussTerm z) := by
  have hmajor := summable_pow_div_add z 2 1 one_lt_two
  apply Summable.of_norm_bounded hmajor
  intro n
  let k : ℂ := ((n + 1 : ℕ) : ℂ)
  have hk : k ≠ 0 := by
    dsimp [k]
    exact_mod_cast Nat.succ_ne_zero n
  have hzk : z + k ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [k] at hre
    simp at hre
    linarith
  have hkpos : 0 < (n + 1 : ℝ) := by positivity
  have hkNorm : (n + 1 : ℝ) ≤ ‖z + k‖ := by
    have hre : (n + 1 : ℝ) ≤ (z + k).re := by
      dsimp [k]
      simp
      exact hz.le
    exact hre.trans (le_abs_self _ |>.trans (Complex.abs_re_le_norm _))
  rw [show digammaGaussTerm z n = z / (k * (z + k)) by
    change k⁻¹ - (z + k)⁻¹ = z / (k * (z + k))
    field_simp [hk, hzk]
    ring]
  rw [norm_div, norm_mul]
  have hden : 0 < (n + 1 : ℝ) ^ 2 := sq_pos_of_pos hkpos
  have hbound :
      ‖z‖ / (‖k‖ * ‖z + k‖) ≤ ‖z‖ / (n + 1 : ℝ) ^ 2 := by
    rw [show ‖k‖ = (n + 1 : ℝ) by
      dsimp [k]
      rw [Complex.norm_natCast]
      norm_num]
    exact div_le_div_of_nonneg_left (norm_nonneg z) hden
      (by simpa [pow_two] using mul_le_mul_of_nonneg_left hkNorm hkpos.le)
  refine hbound.trans_eq ?_
  rw [norm_div, norm_pow]
  congr 2
  have hnorm : ‖(n : ℂ) + (1 : ℂ)‖ = (n : ℝ) + 1 := by
    rw [← ofReal_natCast, ← ofReal_one, ← ofReal_add, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  convert hnorm.symm using 1
  all_goals norm_num

private theorem tsum_one_div_nat_add_sq_le {N : ℕ} (hN : 0 < N) :
    (∑' n : ℕ, 1 / (N + n + 1 : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by
  let f : ℕ → ℝ := fun n => 1 / (N + n : ℝ)
  let g : ℕ → ℝ := fun n => f n - f (n + 1)
  have hdenTop : Tendsto (fun n : ℕ => (N + n : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono'
      (l := atTop) (f₁ := fun n : ℕ => (n : ℝ))
    · exact Eventually.of_forall fun n => by
        norm_num
    · exact tendsto_natCast_atTop_atTop
  have hf0 : Tendsto f atTop (𝓝 0) := by
    dsimp [f]
    exact tendsto_const_nhds.div_atTop hdenTop
  have hg_nonneg : ∀ n, 0 ≤ g n := by
    intro n
    dsimp [g, f]
    have hpos : 0 < (N + n : ℝ) := by positivity
    have hle : (N + n : ℝ) ≤ N + (n + 1 : ℕ) := by
      norm_num
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hpos hle)
  have hgHas : HasSum g (1 / (N : ℝ)) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hg_nonneg]
    have htel : (fun m : ℕ => ∑ n ∈ Finset.range m, g n) =
        fun m => f 0 - f m := by
      funext m
      exact Finset.sum_range_sub' f m
    rw [htel]
    simpa [f] using hf0.const_sub (1 / (N : ℝ))
  have hp : Summable (fun n : ℕ => 1 / (N + n + 1 : ℝ) ^ 2) := by
    have h := summable_pow_div_add (1 : ℝ) 2 (N + 1) one_lt_two
    apply h.congr
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    congr 2
    push_cast
    ring
  have hpoint : ∀ n : ℕ, 1 / (N + n + 1 : ℝ) ^ 2 ≤ g n := by
    intro n
    dsimp [g, f]
    have hA : 0 < (N + n : ℝ) := by positivity
    have hB : 0 < (N + n + 1 : ℝ) := by positivity
    have hgEq :
        1 / (N + n : ℝ) - 1 / (N + (n + 1 : ℕ) : ℝ) =
          1 / ((N + n : ℝ) * (N + n + 1 : ℝ)) := by
      push_cast
      field_simp [hA.ne', hB.ne']
      ring
    rw [hgEq]
    apply one_div_le_one_div_of_le (mul_pos hA hB)
    nlinarith
  calc
    (∑' n : ℕ, 1 / (N + n + 1 : ℝ) ^ 2) ≤ ∑' n : ℕ, g n :=
      Summable.tsum_le_tsum hpoint hp hgHas.summable
    _ = 1 / (N : ℝ) := hgHas.tsum_eq

theorem summable_norm_digammaGaussTerm {z : ℂ} (hz : 0 < z.re) :
    Summable (fun n : ℕ => ‖digammaGaussTerm z n‖) := by
  have hmajorC := summable_pow_div_add z 2 1 one_lt_two
  have hmajor : Summable (fun n : ℕ => ‖z‖ / (n + 1 : ℝ) ^ 2) := by
    apply hmajorC.congr
    intro n
    rw [norm_div, norm_pow]
    have hnorm : ‖(n : ℂ) + (1 : ℂ)‖ = (n : ℝ) + 1 := by
      rw [← ofReal_natCast, ← ofReal_one, ← ofReal_add, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    norm_num only [Nat.cast_one]
    rw [hnorm]
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => norm_digammaGaussTerm_le_norm_div_sq hz n) hmajor

theorem norm_tsum_digammaGaussTerm_le {z : ℂ} (hz : 0 < z.re)
    {N : ℕ} (hN : 0 < N) :
    ‖∑' n : ℕ, digammaGaussTerm z n‖ ≤
      (harmonic N : ℝ) + ‖z‖ / (N : ℝ) := by
  have hsNorm := summable_norm_digammaGaussTerm hz
  have hnormTsum := norm_tsum_le_tsum_norm hsNorm
  have hsplit := hsNorm.sum_add_tsum_nat_add N
  have hfinite :
      (∑ n ∈ Finset.range N, ‖digammaGaussTerm z n‖) ≤ (harmonic N : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, 1 / (n + 1 : ℝ) := by
        exact Finset.sum_le_sum fun n _hn => norm_digammaGaussTerm_le_one_div hz n
      _ = (harmonic N : ℝ) := by
        rw [harmonic]
        push_cast
        simp [one_div]
  have hsTail : Summable
      (fun n : ℕ => ‖digammaGaussTerm z (n + N)‖) :=
    (summable_nat_add_iff N).mpr hsNorm
  have hpTail : Summable
      (fun n : ℕ => ‖z‖ * (1 / (N + n + 1 : ℝ) ^ 2)) := by
    have hp := summable_pow_div_add (1 : ℝ) 2 (N + 1) one_lt_two
    have hp' : Summable (fun n : ℕ => 1 / (N + n + 1 : ℝ) ^ 2) := by
      apply hp.congr
      intro n
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      congr 2
      push_cast
      ring
    exact hp'.mul_left ‖z‖
  have htail :
      (∑' n : ℕ, ‖digammaGaussTerm z (n + N)‖) ≤
        ‖z‖ / (N : ℝ) := by
    calc
      _ ≤ ∑' n : ℕ, ‖z‖ * (1 / (N + n + 1 : ℝ) ^ 2) := by
        apply Summable.tsum_le_tsum _ hsTail hpTail
        intro n
        have h := norm_digammaGaussTerm_le_norm_div_sq hz (n + N)
        convert h using 1
        all_goals (push_cast; ring)
      _ = ‖z‖ * (∑' n : ℕ, 1 / (N + n + 1 : ℝ) ^ 2) := tsum_mul_left
      _ ≤ ‖z‖ * (1 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (tsum_one_div_nat_add_sq_le hN) (norm_nonneg z)
      _ = ‖z‖ / (N : ℝ) := by ring
  calc
    ‖∑' n : ℕ, digammaGaussTerm z n‖ ≤
        ∑' n : ℕ, ‖digammaGaussTerm z n‖ := hnormTsum
    _ = (∑ n ∈ Finset.range N, ‖digammaGaussTerm z n‖) +
        ∑' n : ℕ, ‖digammaGaussTerm z (n + N)‖ := hsplit.symm
    _ ≤ (harmonic N : ℝ) + ‖z‖ / (N : ℝ) := add_le_add hfinite htail

/-- Gauss' convergent series for the complex digamma function on the right
half-plane.  This supplies the representation missing from Mathlib's current
`Digamma` module. -/
theorem digamma_eq_gauss_series {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z =
      -Real.eulerMascheroniConstant - z⁻¹ + ∑' n : ℕ, digammaGaussTerm z n := by
  let P : ℂ → ℂ := fun w => ∏' n : ℕ, gammaCanonicalFactor n w
  let F : ℂ → ℂ := fun w =>
    w * Complex.exp (Real.eulerMascheroniConstant * w) * P w
  let G : ℂ → ℂ := fun w => (Complex.Gamma w)⁻¹
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hGamma : Complex.Gamma z ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    linarith
  have hPne : P z ≠ 0 := by
    intro hzero
    have hproduct := gammaCanonicalProduct_eq_one_div_Gamma hz
    apply inv_ne_zero hGamma
    rw [← hproduct]
    simp [P, hzero]
  have hPdiff : DifferentiableAt ℂ P z := by
    have hloc :=
      multipliableLocallyUniformlyOn_gammaCanonicalFactor.hasProdLocallyUniformlyOn
        |>.tendstoLocallyUniformlyOn_finsetRange
    have hdiff : DifferentiableOn ℂ P Set.univ := by
      apply hloc.differentiableOn _ isOpen_univ
      filter_upwards with n
      apply Differentiable.differentiableOn
      apply Differentiable.fun_finset_prod
      intro i _hi
      rw [show gammaCanonicalFactor i = fun w : ℂ =>
          (1 + w / ((i + 1 : ℕ) : ℂ)) *
            Complex.exp (-w / ((i + 1 : ℕ) : ℂ)) by
        funext w
        simp only [gammaCanonicalFactor, gammaCanonicalRemainder]
        push_cast
        ring]
      fun_prop
    exact hdiff.differentiableAt Filter.univ_mem
  have hsumLD : Summable
      (fun n : ℕ => logDeriv (gammaCanonicalFactor n) z) := by
    apply (summable_digammaGaussTerm hz).neg.congr
    intro n
    exact (logDeriv_gammaCanonicalFactor hz n).symm
  have hlogP : logDeriv P z =
      ∑' n : ℕ, logDeriv (gammaCanonicalFactor n) z := by
    dsimp [P]
    apply logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z)
    · exact gammaCanonicalFactor_ne_zero hz
    · intro n
      apply Differentiable.differentiableOn
      rw [show gammaCanonicalFactor n = fun w : ℂ =>
          (1 + w / ((n + 1 : ℕ) : ℂ)) *
            Complex.exp (-w / ((n + 1 : ℕ) : ℂ)) by
        funext w
        simp only [gammaCanonicalFactor, gammaCanonicalRemainder]
        push_cast
        ring]
      fun_prop
    · exact hsumLD
    · exact multipliableLocallyUniformlyOn_gammaCanonicalFactor
    · exact hPne
  have htsum :
      (∑' n : ℕ, logDeriv (gammaCanonicalFactor n) z) =
        -(∑' n : ℕ, digammaGaussTerm z n) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro n
    exact logDeriv_gammaCanonicalFactor hz n
  have hnhds : {w : ℂ | 0 < w.re} ∈ 𝓝 z := by
    exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have heq : F =ᶠ[𝓝 z] G := by
    filter_upwards [hnhds] with w hw
    exact gammaCanonicalProduct_eq_one_div_Gamma hw
  have hlogEq : logDeriv F z = logDeriv G z := by
    simp only [logDeriv_apply]
    rw [heq.deriv_eq, heq.self_of_nhds]
  have hexpLog :
      logDeriv (fun w : ℂ =>
        Complex.exp (Real.eulerMascheroniConstant * w)) z =
        Real.eulerMascheroniConstant := by
    change logDeriv (Complex.exp ∘
      fun w : ℂ => Real.eulerMascheroniConstant * w) z = _
    rw [logDeriv_comp Complex.differentiableAt_exp (by fun_prop),
      Complex.logDeriv_exp]
    rw [show deriv (fun w : ℂ => Real.eulerMascheroniConstant * w) z =
        (Real.eulerMascheroniConstant : ℂ) by
      convert ((hasDerivAt_id z).const_mul
        (Real.eulerMascheroniConstant : ℂ)).deriv using 1
      all_goals simp]
    simp
  have hlogF : logDeriv F z =
      z⁻¹ + Real.eulerMascheroniConstant + logDeriv P z := by
    dsimp [F]
    rw [logDeriv_mul
      (f := fun w : ℂ => w *
        Complex.exp (Real.eulerMascheroniConstant * w))
      (g := P) z
      (mul_ne_zero hz0 (Complex.exp_ne_zero _)) hPne
      ((differentiableAt_id.mul (by fun_prop))) hPdiff]
    rw [logDeriv_mul
      (f := fun w : ℂ => w)
      (g := fun w : ℂ => Complex.exp (Real.eulerMascheroniConstant * w))
      z hz0 (Complex.exp_ne_zero _)
      differentiableAt_id (by fun_prop), logDeriv_id', hexpLog]
    simp only [one_div]
  have hGdiff : DifferentiableAt ℂ Complex.Gamma z :=
    Complex.differentiableAt_Gamma z (by
      intro m hm
      have hre := congrArg Complex.re hm
      simp at hre
      linarith)
  have hlogG : logDeriv G z = -Complex.digamma z := by
    dsimp [G]
    change logDeriv ((fun w : ℂ => w⁻¹) ∘ Complex.Gamma) z = _
    rw [logDeriv_comp (differentiableAt_inv hGamma) hGdiff,
      logDeriv_inv, Complex.digamma_def]
    rw [logDeriv_apply]
    ring
  rw [hlogF, hlogP, htsum, hlogG] at hlogEq
  linear_combination hlogEq

/-- A quantitative logarithmic-growth bound for digamma on `Re z >= 1`.
The constants are deliberately coarse; the logarithmic dependence is the
feature needed for contour decay. -/
theorem norm_digamma_le_log {z : ℂ} (hz : 1 ≤ z.re) :
    ‖Complex.digamma z‖ ≤
      ‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 + Real.log (‖z‖ + 1) := by
  have hzpos : 0 < z.re := zero_lt_one.trans_le hz
  have hnormz : 1 ≤ ‖z‖ := by
    exact hz.trans (le_abs_self z.re |>.trans (Complex.abs_re_le_norm z))
  let N : ℕ := ⌈‖z‖⌉₊
  have hN : 0 < N := Nat.ceil_pos.mpr (zero_lt_one.trans_le hnormz)
  have hzN : ‖z‖ ≤ (N : ℝ) := by
    exact Nat.le_ceil ‖z‖
  have hratio : ‖z‖ / (N : ℝ) ≤ 1 := by
    exact (div_le_one (Nat.cast_pos.mpr hN)).mpr hzN
  have hNlt : (N : ℝ) < ‖z‖ + 1 := Nat.ceil_lt_add_one (norm_nonneg z)
  have hlogN : Real.log (N : ℝ) ≤ Real.log (‖z‖ + 1) := by
    exact (Real.strictMonoOn_log.le_iff_le
      (Set.mem_Ioi.mpr (Nat.cast_pos.mpr hN))
      (Set.mem_Ioi.mpr (by positivity))).mpr hNlt.le
  have hharm : (harmonic N : ℝ) ≤ 1 + Real.log (‖z‖ + 1) := by
    exact (harmonic_le_one_add_log N).trans (by linarith)
  have hseries : ‖∑' n : ℕ, digammaGaussTerm z n‖ ≤
      2 + Real.log (‖z‖ + 1) := by
    exact (norm_tsum_digammaGaussTerm_le hzpos hN).trans (by linarith)
  have hinv : ‖z⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hnormz
  rw [digamma_eq_gauss_series hzpos]
  calc
    ‖-(Real.eulerMascheroniConstant : ℂ) - z⁻¹ +
        ∑' n : ℕ, digammaGaussTerm z n‖ ≤
      ‖(Real.eulerMascheroniConstant : ℂ)‖ + ‖z⁻¹‖ +
        ‖∑' n : ℕ, digammaGaussTerm z n‖ := by
      calc
        _ ≤ ‖-(Real.eulerMascheroniConstant : ℂ) - z⁻¹‖ +
            ‖∑' n : ℕ, digammaGaussTerm z n‖ := norm_add_le _ _
        _ ≤ (‖(Real.eulerMascheroniConstant : ℂ)‖ + ‖z⁻¹‖) +
            ‖∑' n : ℕ, digammaGaussTerm z n‖ := by
          apply add_le_add _ le_rfl
          calc
            ‖-(Real.eulerMascheroniConstant : ℂ) - z⁻¹‖ ≤
                ‖-(Real.eulerMascheroniConstant : ℂ)‖ + ‖z⁻¹‖ :=
              norm_sub_le _ _
            _ = ‖(Real.eulerMascheroniConstant : ℂ)‖ + ‖z⁻¹‖ := by
              rw [norm_neg]
    _ ≤ ‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
        Real.log (‖z‖ + 1) := by
      calc
        _ ≤ (‖(Real.eulerMascheroniConstant : ℂ)‖ + 1) +
            (2 + Real.log (‖z‖ + 1)) :=
          add_le_add (add_le_add le_rfl hinv) hseries
        _ = _ := by ring

end PrimeNumberTheorem
