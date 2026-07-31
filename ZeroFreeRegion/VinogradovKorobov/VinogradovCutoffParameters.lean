import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedDecomposition
import ZeroFreeRegion.VinogradovKorobov.VinogradovCompleteBase
import ZeroFreeRegion.VinogradovKorobov.VinogradovShiftedTerminal

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Prime-independent arithmetic hypotheses for the cutoff recurrence when
the residual block length is written as `Y = p^y`. -/
structure VinogradovCutoffExponentParameters
    (a b g k r t y : ℕ) : Prop where
  r_pos : 0 < r
  t_pos : 0 < t
  cutoff_le : g ≤ b
  split_le_degree : r ≤ k
  scale_pos : 0 < b
  center_scale_le : ∀ gamma < g, gamma ≤ a
  elimination_budget : ∀ gamma < g,
    gamma * (k - r) + a * r ≤ (k - r + 1) * b
  tail_budget : (k - r + 1) * b ≤ a * (r + 1)
  scale_le : ∀ gamma < g,
    b + y ≤ a + vinogradovFarScale k r a b gamma

/-- The explicit right-hand side of the cutoff recurrence after writing
`Y = p^y`.  Naming it keeps parameter schedules independent of the analytic
definition of the normalized moments. -/
noncomputable def normalizedVinogradovCutoffRecurrenceBound
    (p a b g k r t y : ℕ) [Fact p.Prime] : ℝ := by
  exact
    (((p ^ a : ℕ) : ℝ) ^ (2 * r - 1)) *
      (((p ^ b : ℕ) : ℝ) ^ (2 * t - 1)) *
        (((∑ gamma ∈ Finset.range g,
          (vinogradovCenterPairExactScaleSet p a b gamma).card *
            (‖normalizedVinogradovMomentMod
              (p ^ vinogradovFarScale k r a b gamma) r r
                (p ^ vinogradovFarScale k r a b gamma)‖ *
              (((p ^ y : ℕ) : ℝ) ^ (2 * t)))) +
          ∑ gamma ∈ Finset.Ico g b,
            (vinogradovCenterPairExactScaleSet p a b gamma).card *
              ((((p ^ b * p ^ y) ^ (2 * r) *
                (p ^ y) ^ (2 * t) : ℕ)) : ℝ)) +
          (p ^ a : ℕ) *
            ((((p ^ b * p ^ y) ^ (2 * r) *
              (p ^ y) ^ (2 * t) : ℕ)) : ℝ))

/-- The cutoff recurrence follows from purely exponent-level admissibility. -/
theorem norm_normalizedVinogradovMomentMod_le_of_cutoffExponentParameters
    (p a b g k r t y : ℕ) [Fact p.Prime]
    (hkp : k < p)
    (h : VinogradovCutoffExponentParameters a b g k r t y) :
    ‖normalizedVinogradovMomentMod
        (p ^ ((k - r + 1) * b)) k (r + t) (p ^ b * p ^ y)‖ ≤
      normalizedVinogradovCutoffRecurrenceBound p a b g k r t y := by
  unfold normalizedVinogradovCutoffRecurrenceBound
  apply norm_normalizedVinogradovMomentMod_le_cutoffScales_add_trivial
    p a b g k r t (p ^ y)
    h.r_pos h.t_pos h.cutoff_le h.split_le_degree hkp h.scale_pos
    h.center_scale_le h.elimination_budget h.tail_budget
  intro gamma hgamma
  have hexponent := Nat.pow_le_pow_right (Fact.out : p.Prime).pos
    (h.scale_le gamma hgamma)
  simpa only [pow_add] using hexponent

/-- In the quadratic split with `a = b`, `r = t = g = 1`, and `y = b`,
the unique recursive scale is exactly `b`. -/
theorem vinogradovFarScale_quadratic_unitCutoff (b : ℕ) :
    vinogradovFarScale 2 1 b b 0 = b := by
  simp [vinogradovFarScale]
  omega

/-- A concrete nonempty family of cutoff parameters.  It sends a quadratic
moment on length `p^(2b)` to a degree-one moment on the strictly simpler
far-scale branch `p^b`, while retaining honest trivial bounds for the other
center-difference layers. -/
theorem vinogradovQuadraticUnitCutoffExponentParameters
    (b : ℕ) (hb : 0 < b) :
    VinogradovCutoffExponentParameters b b 1 2 1 1 b := by
  refine
    { r_pos := by norm_num
      t_pos := by norm_num
      cutoff_le := by omega
      split_le_degree := by norm_num
      scale_pos := hb
      center_scale_le := ?_
      elimination_budget := ?_
      tail_budget := ?_
      scale_le := ?_ }
  · intro gamma hgamma
    omega
  · intro gamma hgamma
    omega
  · omega
  · intro gamma hgamma
    have hgamma0 : gamma = 0 := by omega
    subst gamma
    simp [vinogradovFarScale]
    omega

/-- Specialized quadratic instance of the cutoff recurrence. -/
theorem norm_normalizedVinogradovMomentMod_le_quadraticUnitCutoff
    (p b : ℕ) [Fact p.Prime] (hkp : 2 < p) (hb : 0 < b) :
    ‖normalizedVinogradovMomentMod
        (p ^ (2 * b)) 2 2 (p ^ b * p ^ b)‖ ≤
      normalizedVinogradovCutoffRecurrenceBound p b b 1 2 1 1 b := by
  simpa using
    norm_normalizedVinogradovMomentMod_le_of_cutoffExponentParameters
      p b b 1 2 1 1 b hkp
        (vinogradovQuadraticUnitCutoffExponentParameters b hb)

/-- Every quadratic far scale with `a = b` is the remaining exponent
`b - gamma`. -/
theorem vinogradovFarScale_quadratic (b gamma : ℕ) :
    vinogradovFarScale 2 1 b b gamma = b - gamma := by
  simp [vinogradovFarScale]
  omega

/-- The useful quadratic family takes the cutoff all the way to `g = b`
and leaves a residual block of length `p`.  Every nonterminal exact scale
then enters the degree-one recurrence, with no intermediate trivial layer. -/
theorem vinogradovQuadraticFullCutoffExponentParameters
    (b : ℕ) (hb : 0 < b) :
    VinogradovCutoffExponentParameters b b b 2 1 1 1 := by
  refine
    { r_pos := by norm_num
      t_pos := by norm_num
      cutoff_le := le_rfl
      split_le_degree := by norm_num
      scale_pos := hb
      center_scale_le := ?_
      elimination_budget := ?_
      tail_budget := ?_
      scale_le := ?_ }
  · intro gamma hgamma
    omega
  · intro gamma hgamma
    omega
  · omega
  · intro gamma hgamma
    rw [vinogradovFarScale_quadratic]
    omega

/-- Quadratic recurrence with every nonterminal center scale active. -/
theorem norm_normalizedVinogradovMomentMod_le_quadraticFullCutoff
    (p b : ℕ) [Fact p.Prime] (hkp : 2 < p) (hb : 0 < b) :
    ‖normalizedVinogradovMomentMod
        (p ^ (2 * b)) 2 2 (p ^ b * p)‖ ≤
      normalizedVinogradovCutoffRecurrenceBound p b b b 2 1 1 1 := by
  simpa using
    norm_normalizedVinogradovMomentMod_le_of_cutoffExponentParameters
      p b b b 2 1 1 1 hkp
        (vinogradovQuadraticFullCutoffExponentParameters b hb)

/-- Explicit closed right-hand side obtained when the equal-scale quadratic
recurrence uses residual block length one. -/
noncomputable def normalizedVinogradovQuadraticAllScalesBound
    (p b : ℕ) : ℝ :=
  ((p ^ b : ℕ) : ℝ) * ((p ^ b : ℕ) : ℝ) *
    ((∑ gamma ∈ Finset.range b,
      (vinogradovCenterPairExactScaleSet p b b gamma).card *
        (((p ^ (b - gamma) : ℕ) : ℝ))) +
      (p ^ b : ℕ))

/-- In the quadratic equal-scale case with residual block length one, every
center layer closes against the exact complete degree-one base moment. -/
theorem norm_normalizedVinogradovMomentMod_le_quadraticAllScales
    (p b : ℕ) [Fact p.Prime] (hkp : 2 < p) (hb : 0 < b) :
    ‖normalizedVinogradovMomentMod
        (p ^ (2 * b)) 2 2 (p ^ b)‖ ≤
      normalizedVinogradovQuadraticAllScalesBound p b := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hrec :=
    norm_normalizedVinogradovMomentMod_le_allScales_self
      p b 2 1 1 1
        (by norm_num) (by norm_num) (by norm_num) hkp hb
        (by
          intro gamma hgamma
          omega)
        (by omega)
        (by
          intro gamma hgamma
          rw [vinogradovFarScale_quadratic]
          have hpow : 1 ≤ p ^ (b - gamma) := by
            exact one_le_pow₀ (Fact.out : p.Prime).one_lt.le
          nlinarith [Nat.zero_le (p ^ b)])
  simpa [normalizedVinogradovQuadraticAllScalesBound,
    vinogradovFarScale_quadratic,
    norm_normalizedVinogradovMomentMod_complete_one] using hrec

/-- The contribution of the `gamma = 0` center-difference stratum already
forces the quadratic all-scales bound to contain the displayed factor, before
any higher scales or the terminal layer are counted. -/
theorem normalizedVinogradovQuadraticAllScalesBound_ge_zeroScale
    (p b : ℕ) [Fact p.Prime] (hb : 0 < b) :
    (((p ^ b : ℕ) : ℝ) ^ 4) *
        ((p ^ b - p ^ (b - 1) : ℕ) : ℝ) ≤
      normalizedVinogradovQuadraticAllScalesBound p b := by
  have hgb : 0 + 1 ≤ b := by omega
  have htermNat :
        (vinogradovCenterPairExactScaleSet p b b 0).card *
            p ^ (b - 0) =
          (p ^ b) ^ 2 * (p ^ b - p ^ (b - 1)) := by
    rw [card_vinogradovCenterPairExactScaleSet p b b 0 hgb]
    simp only [Nat.zero_add, Nat.sub_zero]
    ring
  have hterm :
      ((vinogradovCenterPairExactScaleSet p b b 0).card : ℝ) *
          (((p ^ (b - 0) : ℕ) : ℝ)) =
        (((p ^ b : ℕ) : ℝ) ^ 2) *
          ((p ^ b - p ^ (b - 1) : ℕ) : ℝ) := by
    exact_mod_cast htermNat
  have hzero : 0 ∈ Finset.range b := Finset.mem_range.mpr hb
  have hsum :
      (vinogradovCenterPairExactScaleSet p b b 0).card *
          (((p ^ (b - 0) : ℕ) : ℝ)) ≤
        ∑ gamma ∈ Finset.range b,
          (vinogradovCenterPairExactScaleSet p b b gamma).card *
            (((p ^ (b - gamma) : ℕ) : ℝ)) := by
    exact Finset.single_le_sum
      (s := Finset.range b)
      (f := fun gamma ↦
        ((vinogradovCenterPairExactScaleSet p b b gamma).card : ℝ) *
          (((p ^ (b - gamma) : ℕ) : ℝ)))
      (fun gamma _ ↦ by positivity) hzero
  unfold normalizedVinogradovQuadraticAllScalesBound
  calc
    (((p ^ b : ℕ) : ℝ) ^ 4) *
          ((p ^ b - p ^ (b - 1) : ℕ) : ℝ) =
        ((p ^ b : ℕ) : ℝ) * ((p ^ b : ℕ) : ℝ) *
          (((vinogradovCenterPairExactScaleSet p b b 0).card : ℝ) *
            (((p ^ (b - 0) : ℕ) : ℝ))) := by rw [hterm]; ring
    _ ≤ ((p ^ b : ℕ) : ℝ) * ((p ^ b : ℕ) : ℝ) *
        ((∑ gamma ∈ Finset.range b,
          (vinogradovCenterPairExactScaleSet p b b gamma).card *
            (((p ^ (b - gamma) : ℕ) : ℝ))) +
          (p ^ b : ℕ)) :=
      mul_le_mul_of_nonneg_left
        (hsum.trans (le_add_of_nonneg_right (by positivity))) (by positivity)

/-- The current quadratic all-scales recurrence cannot by itself give a
strict improvement over the ambient fourth-moment bound: its explicit
right-hand side is already at least `(p^b)^4`. -/
theorem normalizedVinogradovQuadraticAllScalesBound_ge_trivial
    (p b : ℕ) [Fact p.Prime] (hb : 0 < b) :
    (((p ^ b : ℕ) : ℝ) ^ 4) ≤
      normalizedVinogradovQuadraticAllScalesBound p b := by
  have hexponent : b - 1 < b := by omega
  have hpow : p ^ (b - 1) < p ^ b :=
    Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt hexponent
  have hdiffNat : 1 ≤ p ^ b - p ^ (b - 1) := by omega
  have hdiff :
      (1 : ℝ) ≤ ((p ^ b - p ^ (b - 1) : ℕ) : ℝ) := by
    exact_mod_cast hdiffNat
  calc
    (((p ^ b : ℕ) : ℝ) ^ 4) =
        (((p ^ b : ℕ) : ℝ) ^ 4) * 1 := by ring
    _ ≤ (((p ^ b : ℕ) : ℝ) ^ 4) *
        ((p ^ b - p ^ (b - 1) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ ≤ normalizedVinogradovQuadraticAllScalesBound p b :=
      normalizedVinogradovQuadraticAllScalesBound_ge_zeroScale p b hb

end

end ZeroFreeRegion.VinogradovKorobov
