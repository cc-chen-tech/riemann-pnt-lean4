import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible
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
open scoped BigOperators

namespace MathlibAux

/-- A nonvanishing continuous complex-valued curve on a real open interval
admits one continuous logarithm on the whole interval.  This uses the covering
map `exp : ℂ → ℂˣ`; it does not impose the principal logarithm's branch cut. -/
theorem exists_continuousLogOn_Ioo {g : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hg : ContinuousOn g (Ioo a b))
    (hne : ∀ x ∈ Ioo a b, g x ≠ 0) :
    ∃ ell : ℝ → ℂ,
      ContinuousOn ell (Ioo a b) ∧
      ∀ x ∈ Ioo a b, Complex.exp (ell x) = g x := by
  have hnonempty : (Ioo a b).Nonempty := nonempty_Ioo.mpr hab
  have hcontract : ContractibleSpace (Ioo a b) :=
    (convex_Ioo a b).contractibleSpace hnonempty
  have hsimply : IsSimplyConnected (Ioo a b) := by
    change SimplyConnectedSpace (Ioo a b)
    exact @SimplyConnectedSpace.ofContractible (Ioo a b) inferInstance hcontract
  have hzero : 0 ∉ g '' Ioo a b := by
    rintro ⟨x, hx, hgx⟩
    exact hne x hx hgx
  rcases Complex.exists_continuousOn_eqOn_exp_comp
      hsimply isOpen_Ioo hg hzero with ⟨ell, hellContinuous, hellExp⟩
  exact ⟨ell, hellContinuous, fun x hx => by simpa using hellExp hx⟩

/-- Two continuous logarithms of the same curve on a real open interval differ
by one constant deck transformation `2 * π * I * k`.  In particular, the
integer cannot vary from point to point on the connected interval. -/
theorem exists_int_continuousLogs_eq_add_two_pi_I
    {ell₁ ell₂ : ℝ → ℂ} {a b x₀ : ℝ}
    (h₁ : ContinuousOn ell₁ (Ioo a b))
    (h₂ : ContinuousOn ell₂ (Ioo a b))
    (hexp : ∀ x ∈ Ioo a b, Complex.exp (ell₁ x) = Complex.exp (ell₂ x))
    (hx₀ : x₀ ∈ Ioo a b) :
    ∃ k : ℤ, ∀ x ∈ Ioo a b,
      ell₁ x = ell₂ x + k * (2 * Real.pi * I) := by
  let d : ℝ → ℂ := fun x => ell₁ x - ell₂ x
  have hdContinuous : ContinuousOn d (Ioo a b) := h₁.sub h₂
  have hdMaps : MapsTo d (Ioo a b)
      (AddSubgroup.zmultiples (2 * Real.pi * I) : Set ℂ) := by
    intro x hx
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hexp x hx)
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul]
    dsimp [d]
    rw [hk]
    abel
  have hdDiscrete :
      IsDiscrete (AddSubgroup.zmultiples (2 * Real.pi * I) : Set ℂ) := by
    rw [SetLike.isDiscrete_iff_discreteTopology]
    infer_instance
  obtain ⟨k, hk⟩ :=
    Complex.exp_eq_exp_iff_exists_int.mp (hexp x₀ hx₀)
  refine ⟨k, fun x hx => ?_⟩
  have hconst : d x = d x₀ :=
    isPreconnected_Ioo.constant_of_mapsTo hdDiscrete hdContinuous hdMaps hx hx₀
  calc
    ell₁ x = ell₂ x + d x := by simp [d]
    _ = ell₂ x + d x₀ := by rw [hconst]
    _ = ell₂ x + k * (2 * Real.pi * I) := by
      change ell₂ x + (ell₁ x₀ - ell₂ x₀) = _
      rw [hk]
      abel

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

/-- The union of finitely many local phase bridges contains at most the sum
of their multiplicities.  No disjointness hypothesis is needed: overlaps can
only reduce the number of globally deleted argument levels. -/
theorem card_biUnion_argumentCrossingBridgeIndices_le
    {ι : Type*} [DecidableEq ι] (zeros : Finset ι)
    (alpha : ι → ℝ) (multiplicity : ι → ℕ) :
    (zeros.biUnion fun i =>
      argumentCrossingBridgeIndices (alpha i) (multiplicity i)).card ≤
      ∑ i ∈ zeros, multiplicity i := by
  calc
    (zeros.biUnion fun i =>
        argumentCrossingBridgeIndices (alpha i) (multiplicity i)).card ≤
        ∑ i ∈ zeros,
          (argumentCrossingBridgeIndices (alpha i) (multiplicity i)).card :=
      Finset.card_biUnion_le
    _ = ∑ i ∈ zeros, multiplicity i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact argumentCrossingBridgeIndices_card (alpha i) (multiplicity i)

/-- A finite alternating argument partition.  Each constructor adds one
genuine zero-free component from `a` to `b`, followed by an order-`m` positive
phase bridge from `b` to the first endpoint `c` of the remaining partition.
The lists retain the genuine component ranges and bridge data separately. -/
inductive ArgumentPhasePartition :
    ℝ → ℝ → List (ℝ × ℝ) → List (ℝ × ℕ) → Prop
  | single (a b : ℝ) :
      ArgumentPhasePartition a b [(a, b)] []
  | cons {a b c d : ℝ} {m : ℕ}
      {components : List (ℝ × ℝ)} {bridges : List (ℝ × ℕ)}
      (halign : c = b + m * Real.pi)
      (rest : ArgumentPhasePartition c d components bridges) :
      ArgumentPhasePartition a d
        ((a, b) :: components) ((b, m) :: bridges)

/-- Every value between the global endpoint arguments of a finite partition
lies either between the endpoints of a genuine component or in one of the
positive half-open zero bridges.  Genuine components are unordered because
their net argument change may be negative.  A bridge's excluded far endpoint
is routed into the next genuine component. -/
theorem ArgumentPhasePartition.exists_component_or_bridge
    {start finish : ℝ} {components : List (ℝ × ℝ)}
    {bridges : List (ℝ × ℕ)}
    (partition : ArgumentPhasePartition start finish components bridges)
    {x : ℝ} (hx : x ∈ uIcc start finish) :
    (∃ component ∈ components, x ∈ uIcc component.1 component.2) ∨
      ∃ bridge ∈ bridges,
        x ∈ Ico bridge.1 (bridge.1 + bridge.2 * Real.pi) := by
  induction partition with
  | single a b =>
      exact Or.inl ⟨(a, b), by simp, hx⟩
  | @cons a b c d m components bridges halign rest ih =>
      rcases Set.uIcc_subset_uIcc_union_uIcc
          (a := a) (b := b) (c := d) hx with hab | hbd
      · exact Or.inl ⟨(a, b), by simp, hab⟩
      · rcases Set.uIcc_subset_uIcc_union_uIcc
            (a := b) (b := c) (c := d) hbd with hbc | hcd
        · have hbcLe : b ≤ c := by
            rw [halign]
            exact le_add_of_nonneg_right
              (mul_nonneg (Nat.cast_nonneg m) Real.pi_pos.le)
          have hbc' : x ∈ Icc b c := by
            simpa [uIcc_of_le hbcLe] using hbc
          by_cases hxc : x < c
          · refine Or.inr ⟨(b, m), by simp, ?_⟩
            simpa [halign] using (show x ∈ Ico b c from ⟨hbc'.1, hxc⟩)
          · have hcx : c = x := le_antisymm (not_lt.mp hxc) hbc'.2
            have hxRest : x ∈ uIcc c d := by
              rw [← hcx]
              exact left_mem_uIcc
            rcases ih hxRest with
              ⟨component, hcomponent, hxcomponent⟩ |
              ⟨bridge, hbridge, hxbridge⟩
            · exact Or.inl
                ⟨component, List.mem_cons_of_mem (a, b) hcomponent, hxcomponent⟩
            · exact Or.inr
                ⟨bridge, List.mem_cons_of_mem (b, m) hbridge, hxbridge⟩
        · rcases ih hcd with
            ⟨component, hcomponent, hxcomponent⟩ |
            ⟨bridge, hbridge, hxbridge⟩
          · exact Or.inl
              ⟨component, List.mem_cons_of_mem (a, b) hcomponent, hxcomponent⟩
          · exact Or.inr
              ⟨bridge, List.mem_cons_of_mem (b, m) hbridge, hxbridge⟩

/-- If a globally covered value belongs to no half-open zero bridge, it lies
on an actual occurrence of a genuine component.  Returning a list index keeps
distinct component occurrences available even when their endpoint pairs are
equal. -/
theorem ArgumentPhasePartition.exists_component_index_of_forall_not_mem_bridge
    {start finish : ℝ} {components : List (ℝ × ℝ)}
    {bridges : List (ℝ × ℕ)}
    (partition : ArgumentPhasePartition start finish components bridges)
    {x : ℝ} (hx : x ∈ uIcc start finish)
    (hnotBridge : ∀ bridge ∈ bridges,
      x ∉ Ico bridge.1 (bridge.1 + bridge.2 * Real.pi)) :
    ∃ i : Fin components.length,
      x ∈ uIcc (components.get i).1 (components.get i).2 := by
  rcases partition.exists_component_or_bridge hx with
    ⟨component, hcomponent, hxcomponent⟩ |
    ⟨bridge, hbridge, hxbridge⟩
  · have hexists : ∃ component ∈ components,
        x ∈ uIcc component.1 component.2 :=
      ⟨component, hcomponent, hxcomponent⟩
    exact (List.exists_mem_iff_get
      (p := fun component : ℝ × ℝ =>
        x ∈ uIcc component.1 component.2)).mp hexists
  · exact (hnotBridge bridge hbridge hxbridge).elim

/-- An explicit logarithm of the vertical order-`m` factor on the left of a
zero, where `I * (t - tau) = -I * r` with `r > 0`. -/
noncomputable def verticalPowerLeftLog (m : ℕ) (r : ℝ) : ℂ :=
  (m : ℂ) *
    ((Real.log r : ℂ) + ((-Real.pi / 2 : ℝ) : ℂ) * I)

/-- An explicit logarithm of the vertical order-`m` factor on the right of a
zero, where `I * (t - tau) = I * r` with `r > 0`. -/
noncomputable def verticalPowerRightLog (m : ℕ) (r : ℝ) : ℂ :=
  (m : ℂ) *
    ((Real.log r : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * I)

theorem exp_verticalPowerLeftLog (m : ℕ) {r : ℝ} (hr : 0 < r) :
    Complex.exp (verticalPowerLeftLog m r) =
      (-I * (r : ℂ)) ^ m := by
  rw [verticalPowerLeftLog, Complex.exp_nat_mul]
  congr 1
  have hcos : Real.cos (-Real.pi / 2) = 0 := by
    rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
      Real.cos_neg, Real.cos_pi_div_two]
  have hsin : Real.sin (-Real.pi / 2) = -1 := by
    rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
      Real.sin_neg, Real.sin_pi_div_two]
  apply Complex.ext
  · simp [Complex.exp_re, Real.exp_log hr, hcos]
  · simp [Complex.exp_im, Real.exp_log hr, hsin]

theorem exp_verticalPowerRightLog (m : ℕ) {r : ℝ} (hr : 0 < r) :
    Complex.exp (verticalPowerRightLog m r) =
      (I * (r : ℂ)) ^ m := by
  rw [verticalPowerRightLog, Complex.exp_nat_mul]
  congr 1
  apply Complex.ext <;>
    simp [Complex.exp_re, Complex.exp_im, Real.exp_log hr]

/-- The two explicit logarithms of the vertical order-`m` power differ in
argument by exactly `m * π`; the common radial logarithm cancels. -/
theorem verticalPowerRightLog_im_sub_left (m : ℕ) (r : ℝ) :
    (verticalPowerRightLog m r).im -
        (verticalPowerLeftLog m r).im = (m : ℝ) * Real.pi := by
  simp [verticalPowerRightLog, verticalPowerLeftLog, Complex.mul_im]
  ring

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

/-- Deleting all levels swallowed by finitely many local zero bridges costs at
most the sum of their orders, while retaining the single global endpoint loss.
This is the finite multiplicity-accounting layer of Conrey equation (41). -/
theorem argumentCrossingIndices_sdiff_bridgeUnion_card_lower_bound
    {ι : Type*} [DecidableEq ι] {alpha beta : ℝ}
    (zeros : Finset ι) (bridgeStart : ι → ℝ)
    (multiplicity : ι → ℕ) :
    (beta - alpha) / Real.pi - 1 - (∑ i ∈ zeros, multiplicity i) ≤
      ((argumentCrossingIndices alpha beta) \
        (zeros.biUnion fun i =>
          argumentCrossingBridgeIndices (bridgeStart i) (multiplicity i))).card := by
  let bad : Finset ℤ := zeros.biUnion fun i =>
    argumentCrossingBridgeIndices (bridgeStart i) (multiplicity i)
  have hdeleted := argumentCrossingIndices_sdiff_card_lower_bound
    (alpha := alpha) (beta := beta) bad
  have hbadNat : bad.card ≤ ∑ i ∈ zeros, multiplicity i := by
    dsimp [bad]
    exact card_biUnion_argumentCrossingBridgeIndices_le
      zeros bridgeStart multiplicity
  have hbadReal : (bad.card : ℝ) ≤ (∑ i ∈ zeros, multiplicity i : ℕ) := by
    exact_mod_cast hbadNat
  dsimp [bad] at hdeleted ⊢
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

/-- A zero-free component realizes every crossing level in the unordered
interval between its endpoint arguments.  This is the form needed for global
gluing because a component's net argument change may be negative. -/
theorem exists_argumentCrossing_of_level_mem_uIcc
    (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0) (k : ℤ)
    (hlevel : argumentCrossingLevel k ∈
      uIcc (continuousArgumentLift gamma hne 0).im
        (continuousArgumentLift gamma hne 1).im) :
    ∃ t : unitInterval,
      (continuousArgumentLift gamma hne t).im = argumentCrossingLevel k ∧
        (gamma t).re = 0 := by
  let theta : unitInterval → ℝ := fun t ↦ (continuousArgumentLift gamma hne t).im
  have htheta : Continuous theta :=
    Complex.continuous_im.comp (continuousArgumentLift gamma hne).continuous
  have hlevelTheta : argumentCrossingLevel k ∈ uIcc (theta 0) (theta 1) := by
    simpa [theta] using hlevel
  have htRange : argumentCrossingLevel k ∈ Set.range theta := by
    by_cases horder : theta 0 ≤ theta 1
    · exact intermediate_value_univ (0 : unitInterval) 1 htheta
        (by simpa [uIcc_of_le horder] using hlevelTheta)
    · have hreverse : theta 1 ≤ theta 0 := le_of_not_ge horder
      exact intermediate_value_univ (1 : unitInterval) 0 htheta
        (by simpa [uIcc_of_ge hreverse] using hlevelTheta)
  rcases htRange with ⟨t, ht⟩
  have ht' :
      (continuousArgumentLift gamma hne t).im = argumentCrossingLevel k := by
    simpa [theta] using ht
  refine ⟨t, ht', ?_⟩
  rw [← exp_continuousArgumentLift_eq gamma hne t, Complex.exp_re, ht',
    argumentCrossingLevel, Real.cos_add_int_mul_pi, Real.cos_pi_div_two, mul_zero,
    mul_zero]

/-- A global level outside all zero bridges is realized on one indexed
zero-free component curve. -/
theorem ArgumentPhasePartition.exists_component_argumentCrossing_of_forall_not_mem_bridge
    {start finish : ℝ} {components : List (ℝ × ℝ)}
    {bridges : List (ℝ × ℕ)}
    (partition : ArgumentPhasePartition start finish components bridges)
    (gamma : Fin components.length → C(unitInterval, ℂ))
    (hne : ∀ i t, gamma i t ≠ 0)
    (hendpoints : ∀ i,
      (continuousArgumentLift (gamma i) (hne i) 0).im =
          (components.get i).1 ∧
        (continuousArgumentLift (gamma i) (hne i) 1).im =
          (components.get i).2)
    {k : ℤ}
    (hglobal : argumentCrossingLevel k ∈ uIcc start finish)
    (hnotBridge : ∀ bridge ∈ bridges,
      argumentCrossingLevel k ∉
        Ico bridge.1 (bridge.1 + bridge.2 * Real.pi)) :
    ∃ i : Fin components.length, ∃ t : unitInterval,
      (continuousArgumentLift (gamma i) (hne i) t).im =
          argumentCrossingLevel k ∧
        (gamma i t).re = 0 := by
  rcases partition.exists_component_index_of_forall_not_mem_bridge
      hglobal hnotBridge with ⟨i, hi⟩
  have hlevel : argumentCrossingLevel k ∈
      uIcc (continuousArgumentLift (gamma i) (hne i) 0).im
        (continuousArgumentLift (gamma i) (hne i) 1).im := by
    rw [(hendpoints i).1, (hendpoints i).2]
    exact hi
  rcases exists_argumentCrossing_of_level_mem_uIcc
      (gamma i) (hne i) k hlevel with ⟨t, ht⟩
  exact ⟨i, t, ht⟩

/-- A finite family of surviving global levels injects into component-tagged
crossing points.  The component tag prevents equal local parameters on
different zero-free components from being identified. -/
theorem ArgumentPhasePartition.exists_injective_component_argumentCrossings
    {start finish : ℝ} {components : List (ℝ × ℝ)}
    {bridges : List (ℝ × ℕ)}
    (partition : ArgumentPhasePartition start finish components bridges)
    (gamma : Fin components.length → C(unitInterval, ℂ))
    (hne : ∀ i t, gamma i t ≠ 0)
    (hendpoints : ∀ i,
      (continuousArgumentLift (gamma i) (hne i) 0).im =
          (components.get i).1 ∧
        (continuousArgumentLift (gamma i) (hne i) 1).im =
          (components.get i).2)
    (K : Finset ℤ)
    (hglobal : ∀ k ∈ K, argumentCrossingLevel k ∈ uIcc start finish)
    (hnotBridge : ∀ k ∈ K, ∀ bridge ∈ bridges,
      argumentCrossingLevel k ∉
        Ico bridge.1 (bridge.1 + bridge.2 * Real.pi)) :
    ∃ crossing : (k : ↥K) →
        Fin components.length × unitInterval,
      Function.Injective crossing ∧
        ∀ k : ↥K,
          (continuousArgumentLift (gamma (crossing k).1)
              (hne (crossing k).1) (crossing k).2).im =
                argumentCrossingLevel k.1 ∧
            (gamma (crossing k).1 (crossing k).2).re = 0 := by
  classical
  have hcross : ∀ k : ↥K,
      ∃ w : Fin components.length × unitInterval,
        (continuousArgumentLift (gamma w.1) (hne w.1) w.2).im =
            argumentCrossingLevel k.1 ∧
          (gamma w.1 w.2).re = 0 := by
    intro k
    rcases partition.exists_component_argumentCrossing_of_forall_not_mem_bridge
        gamma hne hendpoints (hglobal k.1 k.2)
          (hnotBridge k.1 k.2) with ⟨i, t, ht⟩
    exact ⟨⟨i, t⟩, ht⟩
  let crossing : (k : ↥K) →
      Fin components.length × unitInterval := fun k =>
    Classical.choose (hcross k)
  have hcrossing : ∀ k : ↥K,
      (continuousArgumentLift (gamma (crossing k).1)
          (hne (crossing k).1) (crossing k).2).im =
            argumentCrossingLevel k.1 ∧
        (gamma (crossing k).1 (crossing k).2).re = 0 := by
    intro k
    exact Classical.choose_spec (hcross k)
  refine ⟨crossing, ?_, hcrossing⟩
  intro k l hkl
  have hphaseEq := congrArg
    (fun w : Fin components.length × unitInterval =>
      (continuousArgumentLift (gamma w.1) (hne w.1) w.2).im) hkl
  have hlevels : argumentCrossingLevel k.1 = argumentCrossingLevel l.1 := by
    calc
      argumentCrossingLevel k.1 =
          (continuousArgumentLift (gamma (crossing k).1)
            (hne (crossing k).1) (crossing k).2).im := (hcrossing k).1.symm
      _ = (continuousArgumentLift (gamma (crossing l).1)
            (hne (crossing l).1) (crossing l).2).im := hphaseEq
      _ = argumentCrossingLevel l.1 := (hcrossing l).1
  have hcasts : (k.1 : ℝ) = (l.1 : ℝ) := by
    unfold argumentCrossingLevel at hlevels
    nlinarith [Real.pi_pos]
  apply Subtype.ext
  exact_mod_cast hcasts

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
