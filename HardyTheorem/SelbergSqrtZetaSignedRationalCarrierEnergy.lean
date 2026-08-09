import HardyTheorem.SelbergSqrtZetaSignedRationalCarrierDecomposition
import HardyTheorem.SelbergSqrtZetaSignedReducedPairCompleteCancellation
import HardyTheorem.SelbergSqrtZetaSignedReducedRayBoundaryTaperEnergy
import HardyTheorem.SelbergSqrtZetaInverseCoeffBound

/-!
# Energy control for the distinguished rational carrier

When the zeta cutoff contains the taper box, the `(1,1)` reduced ray has no
boundary scales.  Consequently the exact rational carrier coefficient is the
complete ratio coefficient.  This isolates the remaining arithmetic input as
the signed high-product energy, without reintroducing the vacuous split-energy
bound.
-/

open scoped BigOperators

namespace HardyTheorem

/-- The ratio-one fiber in the positive taper box is exactly the integer
diagonal.  This avoids estimating the distinguished carrier through the
energy of every rational frequency. -/
theorem selbergSqrtZetaCompleteRatioCoeff_one_eq_diagonal
    (X : ℕ) :
    selbergSqrtZetaCompleteRatioCoeff X 1 =
      ∑ d ∈ Finset.Icc 1 X,
        selbergSqrtZetaCompleteNumeratorCoeff X d *
          selbergSqrtZetaCompleteDenominatorCoeff X d := by
  classical
  unfold selbergSqrtZetaCompleteRatioCoeff
    selbergSqrtZetaCompleteRatioFiber
  symm
  refine Finset.sum_bij (fun d _hd => (d, d)) ?_ ?_ ?_ ?_
  · intro d hd
    have hdPos : 0 < d := (Finset.mem_Icc.mp hd).1
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr ⟨hd, hd⟩
    · simp [selbergSqrtZetaCompleteRatioKey, hdPos.ne']
  · intro d _hd e _he hde
    exact congrArg Prod.fst hde
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpBox := Finset.mem_product.mp hp'.1
    have hp2Pos : 0 < p.2 := (Finset.mem_Icc.mp hpBox.2).1
    have hdiagQ : (p.1 : ℚ) = (p.2 : ℚ) := by
      exact (div_eq_one_iff_eq (by exact_mod_cast hp2Pos.ne')).mp hp'.2
    have hdiag : p.1 = p.2 := by exact_mod_cast hdiagQ
    exact ⟨p.1, hpBox.1, by ext <;> simp [hdiag]⟩
  · intro d _hd
    rfl

/-- Expanding both complete taper factors turns the ratio-one carrier into
one signed harmonic sum.  The two linear tapers combine before any absolute
value is taken. -/
theorem selbergSqrtZetaCompleteRatioCoeff_one_eq_tapered_diagonal
    (X : ℕ) :
    selbergSqrtZetaCompleteRatioCoeff X 1 =
      ∑ d ∈ Finset.Icc 1 X,
        (d : ℝ)⁻¹ * selbergSqrtZetaCoeff d *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            selbergSqrtZetaCoeff) d) *
          (1 - (Real.log d / Real.log X) ^ 2) := by
  rw [selbergSqrtZetaCompleteRatioCoeff_one_eq_diagonal]
  apply Finset.sum_congr rfl
  intro d hd
  have hdPos : (0 : ℝ) < d := by
    exact_mod_cast (Finset.mem_Icc.mp hd).1
  unfold selbergSqrtZetaCompleteNumeratorCoeff
    selbergSqrtZetaCompleteDenominatorCoeff
  rw [selbergSqrtZetaFullTapered_apply,
    zeta_mul_selbergSqrtZetaFullTapered_apply]
  field_simp [hdPos.ne']
  rw [Real.sq_sqrt hdPos.le]
  ring

/-- The distinguished ratio-one coefficient grows at most harmonically.
The estimate is direct on the exact signed diagonal and does not pass through
the energy of the other rational frequencies. -/
theorem abs_selbergSqrtZetaCompleteRatioCoeff_one_le_harmonic
    {X : ℕ} (hX : 2 ≤ X) :
    |selbergSqrtZetaCompleteRatioCoeff X 1| ≤ (harmonic X : ℝ) := by
  rw [selbergSqrtZetaCompleteRatioCoeff_one_eq_tapered_diagonal]
  calc
    |∑ d ∈ Finset.Icc 1 X,
        (d : ℝ)⁻¹ * selbergSqrtZetaCoeff d *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            selbergSqrtZetaCoeff) d) *
          (1 - (Real.log d / Real.log X) ^ 2)| ≤
        ∑ d ∈ Finset.Icc 1 X,
          |(d : ℝ)⁻¹ * selbergSqrtZetaCoeff d *
            (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              selbergSqrtZetaCoeff) d) *
            (1 - (Real.log d / Real.log X) ^ 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 X, (d : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdX : d ≤ X := (Finset.mem_Icc.mp hd).2
      have hdPos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
      have hlogX : 0 < Real.log (X : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < X by omega))
      have hlogd : 0 ≤ Real.log (d : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hd1)
      have hlogLe : Real.log (d : ℝ) ≤ Real.log (X : ℝ) :=
        Real.log_le_log hdPos (by exact_mod_cast hdX)
      have hratio0 : 0 ≤ Real.log (d : ℝ) / Real.log (X : ℝ) :=
        div_nonneg hlogd hlogX.le
      have hratio1 : Real.log (d : ℝ) / Real.log (X : ℝ) ≤ 1 :=
        (div_le_one hlogX).2 hlogLe
      have htaper0 :
          0 ≤ 1 - (Real.log (d : ℝ) / Real.log (X : ℝ)) ^ 2 := by
        nlinarith [sq_nonneg
          (1 - Real.log (d : ℝ) / Real.log (X : ℝ))]
      have htaper1 :
          |1 - (Real.log (d : ℝ) / Real.log (X : ℝ)) ^ 2| ≤ 1 := by
        rw [abs_of_nonneg htaper0]
        nlinarith [sq_nonneg
          (Real.log (d : ℝ) / Real.log (X : ℝ))]
      rw [abs_mul, abs_mul, abs_mul, abs_inv, abs_of_pos hdPos]
      calc
        (d : ℝ)⁻¹ * |selbergSqrtZetaCoeff d| *
              |(((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
                selbergSqrtZetaCoeff) d)| *
              |1 - (Real.log (d : ℝ) / Real.log (X : ℝ)) ^ 2| ≤
            (d : ℝ)⁻¹ * 1 * 1 * 1 := by
          gcongr
          · exact abs_selbergSqrtZetaCoeff_le_one d
          · exact abs_zeta_mul_selbergSqrtZetaCoeff_le_one d
        _ = (d : ℝ)⁻¹ := by ring
    _ = (harmonic X : ℝ) := by
      rw [show (harmonic X : ℝ) =
          ∑ d ∈ Finset.Icc 1 X, (d : ℝ)⁻¹ by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
          Rat.cast_natCast]]

/-- The `(1,1)` reduced ray has no boundary defect once the zeta cutoff
contains the taper box. -/
theorem selbergSqrtZetaSignedReducedRayBoundaryTerm_one_one_eq_zero
    {N X : ℕ} (hX : 2 ≤ X) (hNX : X ≤ N) :
    selbergSqrtZetaSignedReducedRayBoundaryTerm N X 1 1 = 0 := by
  have hN : 1 ≤ N := by omega
  have hXleNX : X ≤ N * X := by
    calc
      X = 1 * X := by simp
      _ ≤ N * X := Nat.mul_le_mul_right X hN
  have hbound :=
    selbergSqrtZetaSignedReducedRayBoundaryTerm_sq_le_four_mul_harmonicTail_sq_mul_harmonic_mul_sq_div_log_sq
      (N := N) (X := X) (a := 1) (b := 1) hX
  simp [Nat.min_eq_right hNX, Nat.min_eq_left hXleNX] at hbound
  nlinarith [sq_nonneg
    (selbergSqrtZetaSignedReducedRayBoundaryTerm N X 1 1)]

/-- With no boundary defect, the exact rational carrier is precisely the
complete ratio coefficient at ratio one. -/
theorem selbergSqrtZetaSignedRationalCoeff_one_eq_completeRatioCoeff
    {N X : ℕ} (hX : 2 ≤ X) (hNX : X ≤ N) :
    selbergSqrtZetaSignedRationalCoeff N X 1 =
      (selbergSqrtZetaCompleteRatioCoeff X 1 : ℂ) := by
  rw [selbergSqrtZetaSignedRationalCoeff_one_eq_complete_add_boundary]
  rw [selbergSqrtZetaSignedReducedRayBoundaryTerm_one_one_eq_zero hX hNX]
  simp only [add_zero]
  have hcomplete :=
    selbergSqrtZetaCompleteRatioCoeff_reduced_eq_completeTerm
      (N := N) (X := X) (a := 1) (b := 1)
      hNX (by omega) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hcomplete
  rw [hcomplete]

/-- The distinguished rational carrier has at most logarithmic size.  This
bound uses the exact diagonal formula rather than the total rational-frequency
energy. -/
theorem norm_selbergSqrtZetaSignedRationalCoeff_one_le_one_add_log
    {N X : ℕ} (hX : 2 ≤ X) (hNX : X ≤ N) :
    ‖selbergSqrtZetaSignedRationalCoeff N X 1‖ ≤
      1 + Real.log X := by
  rw [selbergSqrtZetaSignedRationalCoeff_one_eq_completeRatioCoeff hX hNX,
    Complex.norm_real, Real.norm_eq_abs]
  exact (abs_selbergSqrtZetaCompleteRatioCoeff_one_le_harmonic hX).trans
    (harmonic_le_one_add_log X)

/-- After the Hardy-phase oscillation is used, the complete carrier costs at
most `(1 + log X) * 32 / log T`. -/
theorem
    norm_selbergSqrtZetaSignedRationalCarrier_le_one_add_log_mul_thirtytwo_div_log
    {N X : ℕ} (hX : 2 ≤ X) (hNX : X ≤ N)
    {T t H : ℝ} (hT : 1 < T) (hTt : T ≤ t) (hH : 0 ≤ H)
    (hpi : 2 * Real.log (2 * Real.pi) ≤ Real.log T)
    (hwindow : 4 * H ≤ T * Real.log T) :
    ‖selbergSqrtZetaSignedRationalCoeff N X 1 *
        thetaFrequencyShortIntegral 0 H t‖ ≤
      (1 + Real.log X) * (32 / Real.log T) := by
  have hfactor : 0 ≤ 32 / Real.log T := by
    exact div_nonneg (by norm_num) (Real.log_pos hT).le
  exact
    (norm_selbergSqrtZetaSignedRationalCarrier_le_thirtytwo_div_log
      N X hT hTt hH hpi hwindow).trans
      (mul_le_mul_of_nonneg_right
        (norm_selbergSqrtZetaSignedRationalCoeff_one_le_one_add_log hX hNX)
        hfactor)

/-- Pointwise, the full signed rational short model is bounded by the
explicit logarithmic carrier budget plus only the genuine noncarrier
remainder. -/
theorem norm_selbergSqrtZetaSignedRationalShortModel_le_log_carrier_add_noncarrier
    {T t H : ℝ} {X : ℕ}
    (hcutoff : 1 ≤ firstZetaApproximationCutoff T) (hX : 2 ≤ X)
    (hXN : X ≤ firstZetaApproximationCutoff T)
    (hT : 1 < T) (hTt : T ≤ t) (hH : 0 ≤ H)
    (hpi : 2 * Real.log (2 * Real.pi) ≤ Real.log T)
    (hwindow : 4 * H ≤ T * Real.log T) :
    ‖selbergSqrtZetaSignedRationalShortModel T X H t‖ ≤
      (1 + Real.log X) * (32 / Real.log T) +
        ‖selbergSqrtZetaSignedRationalNoncarrierShortModel T X H t‖ := by
  rw [selbergSqrtZetaSignedRationalShortModel_eq_carrier_add_noncarrier
    hcutoff (by omega)]
  exact (norm_add_le _ _).trans
    (add_le_add
      (norm_selbergSqrtZetaSignedRationalCarrier_le_one_add_log_mul_thirtytwo_div_log
        hX hXN hT hTt hH hpi hwindow)
      le_rfl)

/-- The carrier square is controlled by the proved low-product constant plus
the explicit signed high-product tail.  No split-energy smallness assumption
is used. -/
theorem
    normSq_selbergSqrtZetaSignedRationalCoeff_one_le_nineteen_fourths_add_high
    {N X : ℕ} (hNX : X ≤ N) (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) :
    Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X 1) ≤
      (19 : ℝ) / 4 + selbergSqrtZetaCompleteProductHighEnergy X := by
  have hXtwo : 2 ≤ X := by omega
  have hone : (1 : ℚ) ∈ selbergSqrtZetaCompleteRatioSupport X := by
    unfold selbergSqrtZetaCompleteRatioSupport
      selbergSqrtZetaCompletePairSupport
      selbergSqrtZetaCompleteIndexSupport
    apply Finset.mem_image.mpr
    refine ⟨(1, 1), ?_, ?_⟩
    · simp [hX.le]
    · simp [selbergSqrtZetaCompleteRatioKey]
  have hsingle :
      selbergSqrtZetaCompleteRatioCoeff X 1 ^ 2 ≤
        ∑ q ∈ selbergSqrtZetaCompleteRatioSupport X,
          selbergSqrtZetaCompleteRatioCoeff X q ^ 2 := by
    exact Finset.single_le_sum (fun q _hq => sq_nonneg _) hone
  calc
    Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X 1) =
        selbergSqrtZetaCompleteRatioCoeff X 1 ^ 2 := by
      rw [selbergSqrtZetaSignedRationalCoeff_one_eq_completeRatioCoeff
        hXtwo hNX]
      simp [Complex.normSq]
      ring
    _ ≤ ∑ q ∈ selbergSqrtZetaCompleteRatioSupport X,
          selbergSqrtZetaCompleteRatioCoeff X q ^ 2 := hsingle
    _ = ∑ n ∈ selbergSqrtZetaCompleteProductSupport X,
          selbergSqrtZetaCompleteProductCoeff X n ^ 2 :=
      sum_sq_selbergSqrtZetaCompleteRatioCoeff_eq_productCoeff X
    _ ≤ (19 : ℝ) / 4 + selbergSqrtZetaCompleteProductHighEnergy X :=
      sum_sq_selbergSqrtZetaCompleteProductCoeff_le_nineteen_fourths_add_high
        hX hlarge

end HardyTheorem
