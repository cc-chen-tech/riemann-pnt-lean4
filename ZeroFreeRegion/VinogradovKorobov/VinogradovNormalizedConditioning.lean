import ZeroFreeRegion.VinogradovKorobov.VinogradovResidueConditioning
import Mathlib.Analysis.MeanInequalities

open scoped BigOperators NNReal

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Squared `L²` mass of a coefficient sequence in one residue class. -/
def vinogradovResidueMassSq
    (Q X : ℕ) [NeZero Q] (ξ : ZMod Q) (coefficient : Fin X → ℂ) : ℝ≥0 :=
  ∑ m ∈ vinogradovResidueClassFinset Q X ξ, ‖coefficient m‖₊ ^ 2

/-- `L²` mass of a coefficient sequence in one residue class. -/
def vinogradovResidueMass
    (Q X : ℕ) [NeZero Q] (ξ : ZMod Q) (coefficient : Fin X → ℂ) : ℝ≥0 :=
  NNReal.sqrt (vinogradovResidueMassSq Q X ξ coefficient)

/-- A coefficient-weighted finite sum in one residue class.  The phase is
kept arbitrary so that the conditioning lemma is independent of the later
choice of a Weyl phase. -/
def vinogradovResidueWeightedSum
    (Q X : ℕ) [NeZero Q] (ξ : ZMod Q)
    (coefficient phase : Fin X → ℂ) : ℂ :=
  vinogradovResidueClassSum Q X ξ fun m ↦ coefficient m * phase m

/-- Norm of the weighted residue sum divided by its coefficient `L²` mass.
It is defined to be zero when that mass vanishes. -/
def vinogradovNormalizedResidueNorm
    (Q X : ℕ) [NeZero Q] (ξ : ZMod Q)
    (coefficient phase : Fin X → ℂ) : ℝ≥0 :=
  ‖vinogradovResidueWeightedSum Q X ξ coefficient phase‖₊ /
    vinogradovResidueMass Q X ξ coefficient

/-- Zero coefficient mass forces every coefficient, and hence every weighted
summand, in that residue class to vanish. -/
theorem vinogradovResidueWeightedSum_eq_zero_of_mass_eq_zero
    (Q X : ℕ) [NeZero Q] (ξ : ZMod Q)
    (coefficient phase : Fin X → ℂ)
    (hmass : vinogradovResidueMass Q X ξ coefficient = 0) :
    vinogradovResidueWeightedSum Q X ξ coefficient phase = 0 := by
  have hsq : vinogradovResidueMassSq Q X ξ coefficient = 0 := by
    rw [vinogradovResidueMass] at hmass
    exact NNReal.sqrt_eq_zero.mp hmass
  have hcoefficient : ∀ m ∈ vinogradovResidueClassFinset Q X ξ,
      coefficient m = 0 := by
    intro m hm
    have hterm : ‖coefficient m‖₊ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ zero_le _).mp hsq m hm
    simpa using hterm
  unfold vinogradovResidueWeightedSum vinogradovResidueClassSum
  apply Finset.sum_eq_zero
  intro m hm
  simp [hcoefficient m hm]

/-- Multiplying the normalized residue norm by its mass recovers the norm of
the original weighted sum, including the zero-mass edge case. -/
theorem vinogradovResidueMass_mul_normalizedResidueNorm
    (Q X : ℕ) [NeZero Q] (ξ : ZMod Q)
    (coefficient phase : Fin X → ℂ) :
    vinogradovResidueMass Q X ξ coefficient *
        vinogradovNormalizedResidueNorm Q X ξ coefficient phase =
      ‖vinogradovResidueWeightedSum Q X ξ coefficient phase‖₊ := by
  by_cases hmass : vinogradovResidueMass Q X ξ coefficient = 0
  · have hsum := vinogradovResidueWeightedSum_eq_zero_of_mass_eq_zero
      Q X ξ coefficient phase hmass
    simp [vinogradovNormalizedResidueNorm, hmass, hsum]
  · unfold vinogradovNormalizedResidueNorm
    exact mul_div_cancel₀ _ hmass

/-- The squared mass of a coarse prime-power residue class is the sum of the
squared masses of all compatible finer classes. -/
theorem vinogradovResidueMassSq_eq_sum_refinement
    (p a b X : ℕ) (hab : a ≤ b)
    [NeZero (p ^ a)] [NeZero (p ^ b)]
    (ξ : ZMod (p ^ a)) (coefficient : Fin X → ℂ) :
    vinogradovResidueMassSq (p ^ a) X ξ coefficient =
      ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
        ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
        vinogradovResidueMassSq (p ^ b) X z coefficient := by
  let S := vinogradovResidueClassFinset (p ^ a) X ξ
  let T := Finset.univ.filter fun z : ZMod (p ^ b) ↦
    ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ
  let residue := fun m : Fin X ↦ ((m.val + 1 : ℕ) : ZMod (p ^ b))
  have hmaps : ∀ m ∈ S, residue m ∈ T := by
    intro m hm
    have hm' : ((m.val + 1 : ℕ) : ZMod (p ^ a)) = ξ := by
      simpa [S] using hm
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [ZMod.castHom_apply,
      ZMod.cast_natCast (pow_dvd_pow p hab)]
    exact hm'
  calc
    vinogradovResidueMassSq (p ^ a) X ξ coefficient =
        ∑ m ∈ S, ‖coefficient m‖₊ ^ 2 := rfl
    _ = ∑ z ∈ T, ∑ m ∈ S with residue m = z, ‖coefficient m‖₊ ^ 2 := by
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    _ = ∑ z ∈ T, vinogradovResidueMassSq (p ^ b) X z coefficient := by
      apply Finset.sum_congr rfl
      intro z hz
      unfold vinogradovResidueMassSq
      rw [show S = vinogradovResidueClassFinset (p ^ a) X ξ from rfl]
      rw [show residue =
        (fun m : Fin X ↦ ((m.val + 1 : ℕ) : ZMod (p ^ b))) from rfl]
      rw [vinogradovResidueClassFinset_filter_refinement p a b X hab ξ z
        (Finset.mem_filter.mp hz).2]

/-- The corresponding square-root masses satisfy Wooley's identity
`sum rho_b(z)^2 = rho_a(ξ)^2`. -/
theorem sum_vinogradovResidueMass_sq_eq
    (p a b X : ℕ) (hab : a ≤ b)
    [NeZero (p ^ a)] [NeZero (p ^ b)]
    (ξ : ZMod (p ^ a)) (coefficient : Fin X → ℂ) :
    (∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
      ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
      vinogradovResidueMass (p ^ b) X z coefficient ^ 2) =
        vinogradovResidueMass (p ^ a) X ξ coefficient ^ 2 := by
  simpa [vinogradovResidueMass] using
    (vinogradovResidueMassSq_eq_sum_refinement
      p a b X hab ξ coefficient).symm

/-- Weighted power-mean inequality for a finite family.  This is the second
Holder input in Wooley's normalized residue-conditioning inequality. -/
theorem NNReal.pow_weighted_sum_le
    {ι : Type*} (S : Finset ι) (weight value : ι → ℝ≥0)
    (w : ℕ) (hw : 1 ≤ w) :
    (∑ i ∈ S, weight i * value i) ^ w ≤
      (∑ i ∈ S, weight i) ^ (w - 1) *
        ∑ i ∈ S, weight i * value i ^ w := by
  have hwr : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hwpos : (0 : ℝ) < (w : ℝ) := lt_of_lt_of_le zero_lt_one hwr
  have h := NNReal.inner_le_weight_mul_Lp S hwr weight value
  have hpow := NNReal.rpow_le_rpow h (Nat.cast_nonneg w)
  rw [NNReal.rpow_natCast] at hpow
  rw [NNReal.mul_rpow, ← NNReal.rpow_mul, ← NNReal.rpow_mul] at hpow
  have hinv_mul : (w : ℝ)⁻¹ * (w : ℝ) = 1 := inv_mul_cancel₀ hwpos.ne'
  have hsub_mul : (1 - (w : ℝ)⁻¹) * (w : ℝ) = (w - 1 : ℕ) := by
    rw [sub_mul, one_mul, hinv_mul]
    symm
    simpa using
      (Nat.cast_sub hw : ((w - 1 : ℕ) : ℝ) = (w : ℝ) - ((1 : ℕ) : ℝ))
  simpa [hsub_mul, hinv_mul, NNReal.rpow_natCast] using hpow

/-- Three-factor Holder bound in the exact integer-power form used in
equation (6.11) of Wooley's efficient congruencing argument. -/
theorem NNReal.pow_two_mul_sum_le_card_mul_mass_mul_moment
    {ι : Type*} (S : Finset ι) (mass value : ι → ℝ≥0)
    (w : ℕ) (hw : 1 ≤ w) :
    (∑ i ∈ S, mass i * value i) ^ (2 * w) ≤
      (S.card : ℝ≥0) ^ w *
        (∑ i ∈ S, mass i ^ 2) ^ (w - 1) *
          ∑ i ∈ S, mass i ^ 2 * value i ^ (2 * w) := by
  have hcauchy :
      (∑ i ∈ S, mass i * value i) ^ (2 * w) ≤
        (S.card : ℝ≥0) ^ w *
          (∑ i ∈ S, mass i ^ 2 * value i ^ 2) ^ w := by
    calc
      (∑ i ∈ S, mass i * value i) ^ (2 * w) =
          ((∑ i ∈ S, mass i * value i) ^ 2) ^ w := by rw [pow_mul]
      _ ≤ ((S.card : ℝ≥0) *
          ∑ i ∈ S, (mass i * value i) ^ 2) ^ w := by
        gcongr
        exact sq_sum_le_card_mul_sum_sq
      _ = (S.card : ℝ≥0) ^ w *
          (∑ i ∈ S, mass i ^ 2 * value i ^ 2) ^ w := by
        rw [mul_pow]
        congr 2
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_pow]
  have hweighted := NNReal.pow_weighted_sum_le S
    (fun i ↦ mass i ^ 2) (fun i ↦ value i ^ 2) w hw
  calc
    (∑ i ∈ S, mass i * value i) ^ (2 * w) ≤
        (S.card : ℝ≥0) ^ w *
          (∑ i ∈ S, mass i ^ 2 * value i ^ 2) ^ w := hcauchy
    _ ≤ (S.card : ℝ≥0) ^ w *
        ((∑ i ∈ S, mass i ^ 2) ^ (w - 1) *
          ∑ i ∈ S, mass i ^ 2 * (value i ^ 2) ^ w) := by
      exact mul_le_mul_of_nonneg_left hweighted (zero_le _)
    _ = (S.card : ℝ≥0) ^ w *
        (∑ i ∈ S, mass i ^ 2) ^ (w - 1) *
          ∑ i ∈ S, mass i ^ 2 * value i ^ (2 * w) := by
      rw [mul_assoc]
      congr 2
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_mul]

/-- Cancelling the common positive mass power in the scaled Holder estimate
produces the normalized `rho^2 |f|^(2w)` form. -/
theorem NNReal.normalized_moment_le_of_scaled
    (coarseMass coarseValue constant moment : ℝ≥0)
    (w : ℕ) (hw : 1 ≤ w)
    (hscaled :
      (coarseMass * coarseValue) ^ (2 * w) ≤
        constant * (coarseMass ^ 2) ^ (w - 1) * moment) :
    coarseMass ^ 2 * coarseValue ^ (2 * w) ≤ constant * moment := by
  by_cases hmass : coarseMass = 0
  · simp [hmass]
  have hmass_pos : 0 < coarseMass := pos_iff_ne_zero.mpr hmass
  have hfactor_pos : 0 < coarseMass ^ (2 * (w - 1)) := pow_pos hmass_pos _
  apply le_of_mul_le_mul_left ?_ hfactor_pos
  calc
    coarseMass ^ (2 * (w - 1)) *
        (coarseMass ^ 2 * coarseValue ^ (2 * w)) =
      (coarseMass * coarseValue) ^ (2 * w) := by
        have hexponent : 2 * (w - 1) + 2 = 2 * w := by omega
        rw [mul_pow]
        calc
          coarseMass ^ (2 * (w - 1)) *
              (coarseMass ^ 2 * coarseValue ^ (2 * w)) =
            (coarseMass ^ (2 * (w - 1)) * coarseMass ^ 2) *
              coarseValue ^ (2 * w) := by ac_rfl
          _ = coarseMass ^ (2 * (w - 1) + 2) *
              coarseValue ^ (2 * w) := by rw [pow_add]
          _ = coarseMass ^ (2 * w) * coarseValue ^ (2 * w) := by
            rw [hexponent]
    _ ≤ constant * (coarseMass ^ 2) ^ (w - 1) * moment := hscaled
    _ = coarseMass ^ (2 * (w - 1)) * (constant * moment) := by
      rw [← pow_mul]
      ac_rfl

/-- Normalized finite Holder inequality.  If the coarse mass squared is the
sum of the fine mass squares and the coarse normalized sum is dominated by
the mass-weighted fine normalized sums, then the normalized moment satisfies
Wooley's conditioning bound. -/
theorem NNReal.normalized_moment_le
    {ι : Type*} (S : Finset ι) (mass value : ι → ℝ≥0)
    (coarseMass coarseValue : ℝ≥0) (w : ℕ) (hw : 1 ≤ w)
    (hsum : coarseMass * coarseValue ≤ ∑ i ∈ S, mass i * value i)
    (hmass : ∑ i ∈ S, mass i ^ 2 = coarseMass ^ 2) :
    coarseMass ^ 2 * coarseValue ^ (2 * w) ≤
      (S.card : ℝ≥0) ^ w *
        ∑ i ∈ S, mass i ^ 2 * value i ^ (2 * w) := by
  apply NNReal.normalized_moment_le_of_scaled coarseMass coarseValue
    ((S.card : ℝ≥0) ^ w)
    (∑ i ∈ S, mass i ^ 2 * value i ^ (2 * w)) w hw
  calc
    (coarseMass * coarseValue) ^ (2 * w) ≤
        (∑ i ∈ S, mass i * value i) ^ (2 * w) := by gcongr
    _ ≤ (S.card : ℝ≥0) ^ w *
        (∑ i ∈ S, mass i ^ 2) ^ (w - 1) *
          ∑ i ∈ S, mass i ^ 2 * value i ^ (2 * w) :=
      NNReal.pow_two_mul_sum_le_card_mul_mass_mul_moment S mass value w hw
    _ = (S.card : ℝ≥0) ^ w *
        (coarseMass ^ 2) ^ (w - 1) *
          ∑ i ∈ S, mass i ^ 2 * value i ^ (2 * w) := by rw [hmass]

/-- Prime-power specialization of normalized residue conditioning.  This is
the finite algebraic content of Wooley's Lemma 6.2: the cardinality factor is
exactly `(p^(b-a))^w`. -/
theorem NNReal.normalized_primePower_refinement
    (p a b : ℕ) (hp : 0 < p) (hab : a ≤ b)
    [NeZero (p ^ a)] [NeZero (p ^ b)]
    (ξ : ZMod (p ^ a))
    (mass value : ZMod (p ^ b) → ℝ≥0)
    (coarseMass coarseValue : ℝ≥0) (w : ℕ) (hw : 1 ≤ w)
    (hsum : coarseMass * coarseValue ≤
      ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
        ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
        mass z * value z)
    (hmass :
      ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
        ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
        mass z ^ 2 = coarseMass ^ 2) :
    coarseMass ^ 2 * coarseValue ^ (2 * w) ≤
      (((p ^ (b - a) : ℕ) : ℝ≥0) ^ w) *
        ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
          ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
          mass z ^ 2 * value z ^ (2 * w) := by
  simpa only [card_zmod_primePower_castHom_fiber p a b hp hab ξ] using
    (NNReal.normalized_moment_le
      (Finset.univ.filter fun z : ZMod (p ^ b) ↦
        ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ)
      mass value coarseMass coarseValue w hw hsum hmass)

/-- The coarse normalized weighted sum is controlled by the mass-weighted
normalized sums over all compatible finer residue classes. -/
theorem vinogradovResidueMass_mul_normalizedResidueNorm_le_refinement
    (p a b X : ℕ) (hab : a ≤ b)
    [NeZero (p ^ a)] [NeZero (p ^ b)]
    (ξ : ZMod (p ^ a)) (coefficient phase : Fin X → ℂ) :
    vinogradovResidueMass (p ^ a) X ξ coefficient *
        vinogradovNormalizedResidueNorm (p ^ a) X ξ coefficient phase ≤
      ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
        ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
        vinogradovResidueMass (p ^ b) X z coefficient *
          vinogradovNormalizedResidueNorm (p ^ b) X z coefficient phase := by
  let T := Finset.univ.filter fun z : ZMod (p ^ b) ↦
    ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ
  calc
    vinogradovResidueMass (p ^ a) X ξ coefficient *
        vinogradovNormalizedResidueNorm (p ^ a) X ξ coefficient phase =
      ‖vinogradovResidueWeightedSum (p ^ a) X ξ coefficient phase‖₊ :=
        vinogradovResidueMass_mul_normalizedResidueNorm
          (p ^ a) X ξ coefficient phase
    _ = ‖∑ z ∈ T,
        vinogradovResidueWeightedSum (p ^ b) X z coefficient phase‖₊ := by
      apply congrArg (fun u : ℂ ↦ ‖u‖₊)
      exact vinogradovResidueClassSum_eq_sum_refinement
        p a b X hab ξ (fun m ↦ coefficient m * phase m)
    _ ≤ ∑ z ∈ T,
        ‖vinogradovResidueWeightedSum (p ^ b) X z coefficient phase‖₊ := by
      apply nnnorm_sum_le
    _ = ∑ z ∈ T, vinogradovResidueMass (p ^ b) X z coefficient *
        vinogradovNormalizedResidueNorm (p ^ b) X z coefficient phase := by
      apply Finset.sum_congr rfl
      intro z hz
      exact (vinogradovResidueMass_mul_normalizedResidueNorm
        (p ^ b) X z coefficient phase).symm

/-- Fully instantiated finite residue-conditioning inequality in the form of
Wooley's Lemma 6.2.  It applies to arbitrary finite complex coefficients and
arbitrary phases; the exact loss is `(p^(b-a))^w`. -/
theorem normalized_vinogradovResidueNorm_primePower_refinement
    (p a b X : ℕ) (hp : 0 < p) (hab : a ≤ b)
    [NeZero (p ^ a)] [NeZero (p ^ b)]
    (ξ : ZMod (p ^ a)) (coefficient phase : Fin X → ℂ)
    (w : ℕ) (hw : 1 ≤ w) :
    vinogradovResidueMass (p ^ a) X ξ coefficient ^ 2 *
        vinogradovNormalizedResidueNorm (p ^ a) X ξ coefficient phase ^ (2 * w) ≤
      (((p ^ (b - a) : ℕ) : ℝ≥0) ^ w) *
        ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
          ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
          vinogradovResidueMass (p ^ b) X z coefficient ^ 2 *
            vinogradovNormalizedResidueNorm (p ^ b) X z coefficient phase ^ (2 * w) := by
  apply NNReal.normalized_primePower_refinement p a b hp hab ξ
    (fun z ↦ vinogradovResidueMass (p ^ b) X z coefficient)
    (fun z ↦ vinogradovNormalizedResidueNorm (p ^ b) X z coefficient phase)
    (vinogradovResidueMass (p ^ a) X ξ coefficient)
    (vinogradovNormalizedResidueNorm (p ^ a) X ξ coefficient phase)
    w hw
  · exact vinogradovResidueMass_mul_normalizedResidueNorm_le_refinement
      p a b X hab ξ coefficient phase
  · exact sum_vinogradovResidueMass_sq_eq p a b X hab ξ coefficient

end

end ZeroFreeRegion.VinogradovKorobov
