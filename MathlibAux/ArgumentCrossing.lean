import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Order.Interval.Finset.Floor
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Order.IntermediateValue

/-!
# Argument variation produces distinct real-part crossings

This file isolates the topological crossing mechanism behind the left-hand side of
Conrey's equation (41).  A nonvanishing complex curve on the unit interval has a
canonical continuous logarithmic lift, normalized by the principal logarithm at
the left endpoint.  Every lifted argument level `π / 2 + kπ` between the endpoint
arguments gives a zero of the real part, and different levels give different
crossing times.

The result deliberately counts crossings only on a zero-free interval.  Applying
it to a curve with zeros requires first partitioning at those zeros; that is the
separate subtraction step represented by `N_{0,η}` in Conrey's argument.
-/

open Complex Set Topology

namespace MathlibAux

private noncomputable def nonzeroCurve (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0) :
    C(unitInterval, {z : ℂ // z ≠ 0}) :=
  ⟨fun t ↦ ⟨gamma t, hne t⟩, gamma.continuous.subtype_mk hne⟩

/-- The continuous logarithmic lift of a nonvanishing complex curve, normalized
by the principal logarithm at the left endpoint. -/
noncomputable def continuousArgumentLift (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0) :
    C(unitInterval, ℂ) :=
  Complex.isCoveringMap_exp.liftPath (nonzeroCurve gamma hne) (Complex.log (gamma 0)) (by
    apply Subtype.ext
    exact (Complex.exp_log (hne 0)).symm)

theorem exp_continuousArgumentLift_eq (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0)
    (t : unitInterval) :
    Complex.exp (continuousArgumentLift gamma hne t) = gamma t := by
  have h := congr_fun (Complex.isCoveringMap_exp.liftPath_lifts
    (nonzeroCurve gamma hne) (Complex.log (gamma 0)) (by
      apply Subtype.ext
      exact (Complex.exp_log (hne 0)).symm)) t
  exact congrArg Subtype.val h

theorem continuousArgumentLift_zero (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0) :
    continuousArgumentLift gamma hne 0 = Complex.log (gamma 0) :=
  Complex.isCoveringMap_exp.liftPath_zero
    (nonzeroCurve gamma hne) (Complex.log (gamma 0)) (by
      apply Subtype.ext
      exact (Complex.exp_log (hne 0)).symm)

/-- The lifted argument levels at which the real part of a complex number vanishes. -/
noncomputable def argumentCrossingLevel (k : ℤ) : ℝ :=
  Real.pi / 2 + k * Real.pi

/-- All half-odd-integer multiples of `π` lying between two argument values. -/
noncomputable def argumentCrossingIndices (alpha beta : ℝ) : Finset ℤ :=
  Finset.Icc
    ⌈(alpha - Real.pi / 2) / Real.pi⌉
    ⌊(beta - Real.pi / 2) / Real.pi⌋

/-- The half-odd-integer argument levels swallowed by a half-open phase bridge
of length `m * π`.  The half-open convention prevents a level at the far
endpoint from being charged both to the bridge and to the next nonzero
component. -/
noncomputable def argumentCrossingBridgeIndices (alpha : ℝ) (m : ℕ) : Finset ℤ :=
  Finset.Ico
    ⌈(alpha - Real.pi / 2) / Real.pi⌉
    ⌈(alpha + m * Real.pi - Real.pi / 2) / Real.pi⌉

@[simp]
theorem mem_argumentCrossingBridgeIndices_iff
    {alpha : ℝ} {m : ℕ} {k : ℤ} :
    k ∈ argumentCrossingBridgeIndices alpha m ↔
      argumentCrossingLevel k ∈ Ico alpha (alpha + m * Real.pi) := by
  rw [argumentCrossingBridgeIndices, ← Int.cast_mem_Ico_iff]
  constructor
  · intro hk
    constructor
    · have h := (div_le_iff₀ Real.pi_pos).mp hk.1
      unfold argumentCrossingLevel
      nlinarith
    · have h := (lt_div_iff₀ Real.pi_pos).mp hk.2
      unfold argumentCrossingLevel
      nlinarith
  · intro hk
    rcases hk with ⟨hkLower, hkUpper⟩
    constructor
    · apply (div_le_iff₀ Real.pi_pos).mpr
      unfold argumentCrossingLevel at hkLower hkUpper
      nlinarith [hkLower]
    · apply (lt_div_iff₀ Real.pi_pos).mpr
      unfold argumentCrossingLevel at hkLower hkUpper
      nlinarith [hkUpper]

/-- A half-open phase bridge of length `m * π` contains exactly `m`
half-odd-integer argument levels, independently of the starting phase. -/
theorem argumentCrossingBridgeIndices_card (alpha : ℝ) (m : ℕ) :
    (argumentCrossingBridgeIndices alpha m).card = m := by
  let x : ℝ := (alpha - Real.pi / 2) / Real.pi
  have hnormalize :
      (alpha + m * Real.pi - Real.pi / 2) / Real.pi = x + m := by
    dsimp [x]
    field_simp [Real.pi_ne_zero]
    ring
  have hceil :
      ⌈(alpha + m * Real.pi - Real.pi / 2) / Real.pi⌉ = ⌈x⌉ + (m : ℤ) := by
    rw [hnormalize, Int.ceil_add_natCast]
  have hle : ⌈x⌉ ≤ ⌈x⌉ + (m : ℤ) := by omega
  have hcardInt :
      ((Finset.Ico ⌈x⌉ (⌈x⌉ + (m : ℤ))).card : ℤ) = m := by
    rw [Int.card_Ico_of_le _ _ hle]
    omega
  rw [argumentCrossingBridgeIndices, show
    ⌈(alpha - Real.pi / 2) / Real.pi⌉ = ⌈x⌉ by rfl, hceil]
  exact_mod_cast hcardInt

@[simp]
theorem mem_argumentCrossingIndices_iff {alpha beta : ℝ} {k : ℤ} :
    k ∈ argumentCrossingIndices alpha beta ↔
      argumentCrossingLevel k ∈ Icc alpha beta := by
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [argumentCrossingIndices]
  constructor
  · intro hk
    have hnormalized : (k : ℝ) ∈
        Icc ((alpha - Real.pi / 2) / Real.pi)
          ((beta - Real.pi / 2) / Real.pi) :=
      Int.cast_mem_Icc_iff.mpr hk
    constructor
    · have h := (div_le_iff₀ hpi).mp hnormalized.1
      unfold argumentCrossingLevel
      nlinarith
    · have h := (le_div_iff₀ hpi).mp hnormalized.2
      unfold argumentCrossingLevel
      nlinarith
  · intro hk
    apply Int.cast_mem_Icc_iff.mp
    constructor
    · apply (div_le_iff₀ hpi).mpr
      unfold argumentCrossingLevel at hk
      nlinarith [hk.1]
    · apply (le_div_iff₀ hpi).mpr
      unfold argumentCrossingLevel at hk
      nlinarith [hk.2]

/-- A real interval of argument length `beta - alpha` contains at least
`(beta - alpha) / π - 1` crossing levels.  The loss of one is the exact
endpoint-rounding cost that must be retained when zero-free components are
later summed. -/
private theorem argumentCrossingIndices_card_lower_bound_of_le {alpha beta : ℝ}
    (hab : alpha ≤ beta) :
    (beta - alpha) / Real.pi - 1 ≤
      (argumentCrossingIndices alpha beta).card := by
  let x : ℝ := (alpha - Real.pi / 2) / Real.pi
  let y : ℝ := (beta - Real.pi / 2) / Real.pi
  let a : ℤ := ⌈x⌉
  let b : ℤ := ⌊y⌋
  have hpi : 0 < Real.pi := Real.pi_pos
  have hxy : x ≤ y := by
    dsimp [x, y]
    exact (div_le_div_iff_of_pos_right hpi).mpr (sub_le_sub_right hab _)
  have hfloor : y < (b : ℝ) + 1 := by
    have := Int.sub_one_lt_floor y
    dsimp [b]
    linarith
  have habInt : a ≤ b + 1 := by
    apply Int.ceil_le.mpr
    simpa using hxy.trans hfloor.le
  have hcardInt :
      ((Finset.Icc a b).card : ℤ) = b + 1 - a :=
    Int.card_Icc_of_le a b habInt
  have hcardReal :
      ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by
    exact_mod_cast hcardInt
  have hceil : (a : ℝ) < x + 1 := by
    simpa [a] using (Int.ceil_lt_add_one x)
  have hnormalize : (beta - alpha) / Real.pi = y - x := by
    dsimp [x, y]
    field_simp [Real.pi_ne_zero]
    ring
  rw [argumentCrossingIndices]
  change (beta - alpha) / Real.pi - 1 ≤ ((Finset.Icc a b).card : ℝ)
  rw [hnormalize, hcardReal]
  linarith

theorem argumentCrossingIndices_card_lower_bound {alpha beta : ℝ} :
    (beta - alpha) / Real.pi - 1 ≤
      (argumentCrossingIndices alpha beta).card := by
  by_cases hab : alpha ≤ beta
  · exact argumentCrossingIndices_card_lower_bound_of_le hab
  · have hdiff : beta - alpha < 0 := sub_neg.mpr (lt_of_not_ge hab)
    have hquot : (beta - alpha) / Real.pi < 0 :=
      div_neg_of_neg_of_pos hdiff Real.pi_pos
    have hcard : 0 ≤ ((argumentCrossingIndices alpha beta).card : ℝ) := by
      positivity
    linarith

/-- Deleting an arbitrary finite family of bad argument levels costs at most
its cardinality.  In particular, the endpoint-rounding loss remains the one
global loss from `argumentCrossingIndices_card_lower_bound`; it is not paid
again for every zero-free component. -/
theorem argumentCrossingIndices_sdiff_card_lower_bound
    {alpha beta : ℝ} (bad : Finset ℤ) :
    (beta - alpha) / Real.pi - 1 - bad.card ≤
      ((argumentCrossingIndices alpha beta) \ bad).card := by
  have hlevels :=
    argumentCrossingIndices_card_lower_bound (alpha := alpha) (beta := beta)
  have hcardNat :
      (argumentCrossingIndices alpha beta).card ≤
        ((argumentCrossingIndices alpha beta) \ bad).card + bad.card :=
    Finset.card_le_card_sdiff_add_card
  have hcardReal :
      ((argumentCrossingIndices alpha beta).card : ℝ) ≤
        (((argumentCrossingIndices alpha beta) \ bad).card : ℝ) + bad.card := by
    exact_mod_cast hcardNat
  linarith

theorem exists_argumentCrossing_of_level_mem_Icc
    (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0) (k : ℤ)
    (hlevel : argumentCrossingLevel k ∈
      Icc (continuousArgumentLift gamma hne 0).im
        (continuousArgumentLift gamma hne 1).im) :
    ∃ t : unitInterval,
      (continuousArgumentLift gamma hne t).im = argumentCrossingLevel k ∧
        (gamma t).re = 0 := by
  let theta : unitInterval → ℝ := fun t ↦ (continuousArgumentLift gamma hne t).im
  have htheta : Continuous theta :=
    Complex.continuous_im.comp (continuousArgumentLift gamma hne).continuous
  rcases intermediate_value_univ (0 : unitInterval) 1 htheta hlevel with ⟨t, ht⟩
  have ht' : (continuousArgumentLift gamma hne t).im = argumentCrossingLevel k := by
    simpa [theta] using ht
  refine ⟨t, ht', ?_⟩
  rw [← exp_continuousArgumentLift_eq gamma hne t, Complex.exp_re, ht',
    argumentCrossingLevel, Real.cos_add_int_mul_pi, Real.cos_pi_div_two, mul_zero,
    mul_zero]

theorem exists_injective_argumentCrossing_times
    (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0) (K : Finset ℤ)
    (hK : ∀ k ∈ K, argumentCrossingLevel k ∈
      Icc (continuousArgumentLift gamma hne 0).im
        (continuousArgumentLift gamma hne 1).im) :
    ∃ tau : ℤ → unitInterval, Set.InjOn tau (K : Set ℤ) ∧
      ∀ k ∈ K,
        (continuousArgumentLift gamma hne (tau k)).im = argumentCrossingLevel k ∧
          (gamma (tau k)).re = 0 := by
  classical
  have hcross : ∀ k : ℤ, k ∈ K → ∃ t : unitInterval,
      (continuousArgumentLift gamma hne t).im = argumentCrossingLevel k ∧
        (gamma t).re = 0 := fun k hk ↦
    exists_argumentCrossing_of_level_mem_Icc gamma hne k (hK k hk)
  let tau : ℤ → unitInterval := fun k ↦ if hk : k ∈ K then Classical.choose (hcross k hk) else 0
  have htau : ∀ k ∈ K,
      (continuousArgumentLift gamma hne (tau k)).im = argumentCrossingLevel k ∧
        (gamma (tau k)).re = 0 := by
    intro k hk
    rw [show tau k = Classical.choose (hcross k hk) by simp [tau, hk]]
    exact Classical.choose_spec (hcross k hk)
  refine ⟨tau, ?_, htau⟩
  intro k hk l hl hkl
  have hlevels : argumentCrossingLevel k = argumentCrossingLevel l := by
    calc
      argumentCrossingLevel k = (continuousArgumentLift gamma hne (tau k)).im :=
        (htau k (by simpa using hk)).1.symm
      _ = (continuousArgumentLift gamma hne (tau l)).im := by rw [hkl]
      _ = argumentCrossingLevel l := (htau l (by simpa using hl)).1
  have hcasts : (k : ℝ) = (l : ℝ) := by
    unfold argumentCrossingLevel at hlevels
    nlinarith [Real.pi_pos]
  exact_mod_cast hcasts

/-- Quantitative zero-free argument crossing: the endpoint argument increase
produces an injectively indexed family of real-part crossings, with only the
single unavoidable endpoint-rounding loss. -/
theorem exists_quantified_argumentCrossing_times
    (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0) :
    ∃ tau : ℤ → unitInterval,
      Set.InjOn tau
          (argumentCrossingIndices
            (continuousArgumentLift gamma hne 0).im
            (continuousArgumentLift gamma hne 1).im : Set ℤ) ∧
        (∀ k ∈ argumentCrossingIndices
            (continuousArgumentLift gamma hne 0).im
            (continuousArgumentLift gamma hne 1).im,
          (continuousArgumentLift gamma hne (tau k)).im =
              argumentCrossingLevel k ∧
            (gamma (tau k)).re = 0) ∧
        ((continuousArgumentLift gamma hne 1).im -
            (continuousArgumentLift gamma hne 0).im) / Real.pi - 1 ≤
          (argumentCrossingIndices
            (continuousArgumentLift gamma hne 0).im
            (continuousArgumentLift gamma hne 1).im).card := by
  let K := argumentCrossingIndices
    (continuousArgumentLift gamma hne 0).im
    (continuousArgumentLift gamma hne 1).im
  have hK : ∀ k ∈ K, argumentCrossingLevel k ∈
      Icc (continuousArgumentLift gamma hne 0).im
        (continuousArgumentLift gamma hne 1).im := by
    intro k hk
    exact mem_argumentCrossingIndices_iff.mp hk
  rcases exists_injective_argumentCrossing_times gamma hne K hK with
    ⟨tau, hinj, htau⟩
  refine ⟨tau, hinj, htau, ?_⟩
  exact argumentCrossingIndices_card_lower_bound

end MathlibAux
