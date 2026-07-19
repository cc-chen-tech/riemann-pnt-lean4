import ZeroFreeRegion.VinogradovKorobov.HigherDifferenceIntegral

namespace ZeroFreeRegion.VinogradovKorobov

/-- The explicit derivative tower of the real logarithm. -/
noncomputable def logDerivativeTower : ℕ → ℝ → ℝ
  | 0 => Real.log
  | r + 1 => fun x ↦
      (-1 : ℝ) ^ r * (r.factorial : ℝ) * x ^ (-1 - (r : ℤ))

@[simp] lemma logDerivativeTower_zero :
    logDerivativeTower 0 = Real.log := rfl

@[simp] lemma logDerivativeTower_succ (r : ℕ) (x : ℝ) :
    logDerivativeTower (r + 1) x =
      (-1 : ℝ) ^ r * (r.factorial : ℝ) * x ^ (-1 - (r : ℤ)) := rfl

/-- Consecutive members of `logDerivativeTower` are genuine derivatives on
the positive axis. -/
lemma hasDerivAt_logDerivativeTower
    (r : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (logDerivativeTower r) (logDerivativeTower (r + 1) x) x := by
  cases r with
  | zero =>
      simpa using Real.hasDerivAt_log hx.ne'
  | succ r =>
      have hz := (hasDerivAt_zpow (-1 - (r : ℤ)) x (.inl hx.ne')).const_mul
        ((-1 : ℝ) ^ r * (r.factorial : ℝ))
      convert hz using 1
      simp only [logDerivativeTower_succ, Nat.cast_add, Nat.cast_one,
        Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one, pow_succ]
      push_cast
      ring

/-- Iterated shift integration is linear in a constant factor. -/
lemma iteratedShiftIntegral_const_mul
    (shifts : List ℝ) (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    iteratedShiftIntegral shifts (fun y ↦ c * f y) x =
      c * iteratedShiftIntegral shifts f x := by
  induction shifts generalizing x with
  | nil => rfl
  | cons h shifts ih =>
      simp only [iteratedShiftIntegral_cons]
      rw [show (fun u ↦ iteratedShiftIntegral shifts (fun y ↦ c * f y) u) =
          fun u ↦ c * iteratedShiftIntegral shifts f u by
        funext u
        exact ih u,
        intervalIntegral.integral_const_mul]

/-- Clamp a real variable to a closed interval. -/
def clampReal (a b y : ℝ) : ℝ := max a (min b y)

/-- A globally continuous inverse-power kernel agreeing with `y ↦ y⁻ᵖ`
on `[a, b]`. -/
noncomputable def clampedInvPow (p : ℕ) (a b y : ℝ) : ℝ :=
  (clampReal a b y ^ p)⁻¹

lemma left_le_clampReal (a b y : ℝ) : a ≤ clampReal a b y := by
  exact le_max_left _ _

lemma clampReal_le_right {a b y : ℝ} (hab : a ≤ b) :
    clampReal a b y ≤ b := by
  exact max_le hab (min_le_left _ _)

lemma clampReal_eq_self {a b y : ℝ} (hay : a ≤ y) (hyb : y ≤ b) :
    clampReal a b y = y := by
  simp [clampReal, min_eq_right hyb, max_eq_right hay]

lemma continuous_clampedInvPow
    (p : ℕ) {a b : ℝ} (ha : 0 < a) :
    Continuous (clampedInvPow p a b) := by
  have hclamp : Continuous (clampReal a b) :=
    continuous_const.max (continuous_const.min continuous_id)
  apply (hclamp.pow p).inv₀
  intro y
  exact pow_ne_zero p (ne_of_gt (ha.trans_le (left_le_clampReal a b y)))

/-- Inverse natural powers reverse positive base inequalities. -/
lemma inv_pow_antitone
    (p : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b ^ p)⁻¹ ≤ (a ^ p)⁻¹ := by
  have hb : 0 < b := ha.trans_le hab
  have hp : a ^ p ≤ b ^ p := pow_le_pow_left₀ ha.le hab p
  exact (inv_le_inv₀ (pow_pos hb p) (pow_pos ha p)).2 hp

lemma clampedInvPow_bounds
    (p : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (y : ℝ) :
    (b ^ p)⁻¹ ≤ clampedInvPow p a b y ∧
      clampedInvPow p a b y ≤ (a ^ p)⁻¹ := by
  have hclampPos : 0 < clampReal a b y :=
    ha.trans_le (left_le_clampReal a b y)
  constructor
  · exact inv_pow_antitone p hclampPos (clampReal_le_right hab)
  · exact inv_pow_antitone p ha (left_le_clampReal a b y)

lemma list_sum_nonneg_of_forall
    (shifts : List ℝ) (hshifts : ∀ h ∈ shifts, 0 ≤ h) :
    0 ≤ shifts.sum := by
  induction shifts with
  | nil => simp
  | cons h shifts ih =>
      simp only [List.sum_cons]
      exact add_nonneg (hshifts h (by simp))
        (ih (fun k hk ↦ hshifts k (by simp [hk])))

/-- Scale-sharp bounds for an arbitrary finite iterated inverse-power
kernel. -/
theorem iteratedShiftIntegral_invPow_bounds
    (p : ℕ) (shifts : List ℝ)
    (hshifts : ∀ h ∈ shifts, 0 ≤ h) {x : ℝ} (hx : 0 < x) :
    shifts.prod * ((x + shifts.sum) ^ p)⁻¹ ≤
        iteratedShiftIntegral shifts (fun y ↦ (y ^ p)⁻¹) x ∧
      iteratedShiftIntegral shifts (fun y ↦ (y ^ p)⁻¹) x ≤
        shifts.prod * (x ^ p)⁻¹ := by
  have hsum : 0 ≤ shifts.sum := list_sum_nonneg_of_forall shifts hshifts
  have hxb : x ≤ x + shifts.sum := le_add_of_nonneg_right hsum
  have hcont := continuous_clampedInvPow p hx (b := x + shifts.sum)
  have hpoint := clampedInvPow_bounds p hx hxb
  have hbounds := iteratedShiftIntegral_bounds hcont
    (((x + shifts.sum) ^ p)⁻¹) ((x ^ p)⁻¹)
    (fun y ↦ (hpoint y).1) (fun y ↦ (hpoint y).2)
    shifts hshifts x
  have hcongr :
      iteratedShiftIntegral shifts (fun y ↦ (y ^ p)⁻¹) x =
        iteratedShiftIntegral shifts (clampedInvPow p x (x + shifts.sum)) x := by
    apply iteratedShiftIntegral_congr_Icc shifts hshifts
    intro y hy
    unfold clampedInvPow
    rw [clampReal_eq_self hy.1 hy.2]
  rwa [← hcongr] at hbounds

/-- A globally continuous antitone inverse-power kernel agreeing with the
usual kernel to the right of `a`. -/
noncomputable def forwardClampedInvPow (p : ℕ) (a y : ℝ) : ℝ :=
  (max a y ^ p)⁻¹

lemma continuous_forwardClampedInvPow
    (p : ℕ) {a : ℝ} (ha : 0 < a) :
    Continuous (forwardClampedInvPow p a) := by
  have hmax : Continuous (fun y ↦ max a y) := continuous_const.max continuous_id
  apply (hmax.pow p).inv₀
  intro y
  exact pow_ne_zero p (ne_of_gt (ha.trans_le (le_max_left a y)))

lemma antitone_forwardClampedInvPow
    (p : ℕ) {a : ℝ} (ha : 0 < a) :
    Antitone (forwardClampedInvPow p a) := by
  intro x y hxy
  exact inv_pow_antitone p
    (ha.trans_le (le_max_left a x)) (max_le_max_left a hxy)

/-- The arbitrary iterated inverse-power kernel decreases as its base point
moves to the right. -/
theorem antitoneOn_iteratedShiftIntegral_invPow
    (p : ℕ) (shifts : List ℝ)
    (hshifts : ∀ h ∈ shifts, 0 ≤ h) :
    AntitoneOn
      (fun x ↦ iteratedShiftIntegral shifts (fun y ↦ (y ^ p)⁻¹) x)
      (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hcont := continuous_forwardClampedInvPow p hx
  have hanti := antitone_iteratedShiftIntegral hcont
    (antitone_forwardClampedInvPow p hx) shifts hshifts hxy
  have hxcongr :
      iteratedShiftIntegral shifts (fun z ↦ (z ^ p)⁻¹) x =
        iteratedShiftIntegral shifts (forwardClampedInvPow p x) x := by
    apply iteratedShiftIntegral_congr_Icc shifts hshifts
    intro z hz
    unfold forwardClampedInvPow
    rw [max_eq_right hz.1]
  have hycongr :
      iteratedShiftIntegral shifts (fun z ↦ (z ^ p)⁻¹) y =
        iteratedShiftIntegral shifts (forwardClampedInvPow p x) y := by
    apply iteratedShiftIntegral_congr_Icc shifts hshifts
    intro z hz
    unfold forwardClampedInvPow
    rw [max_eq_right (hxy.trans hz.1)]
  change iteratedShiftIntegral shifts (fun z ↦ (z ^ p)⁻¹) y ≤
    iteratedShiftIntegral shifts (fun z ↦ (z ^ p)⁻¹) x
  rw [hycongr, hxcongr]
  exact hanti

/-- Exact positive-kernel representation of every nonempty iterated
logarithmic difference. -/
theorem neg_realIteratedLogDifference_eq_kernelIntegral
    (h : ℝ) (shifts : List ℝ)
    (hh : 0 ≤ h) (hshifts : ∀ k ∈ shifts, 0 ≤ k)
    {x : ℝ} (hx : 0 < x) :
    -realIteratedPhaseDifference (h :: shifts) Real.log x =
      (shifts.length.factorial : ℝ) *
        iteratedShiftIntegral (h :: shifts)
          (fun y ↦ (y ^ (h :: shifts).length)⁻¹) x
    := by
  have hnonneg : ∀ k ∈ h :: shifts, 0 ≤ k := by
    intro k hk
    simp only [List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact hh
    · exact hshifts k hk
  have htower := iteratedShiftIntegral_tower_eq_signedDifference
    logDerivativeTower (fun j y hy ↦ hasDerivAt_logDerivativeTower j hy)
    (h :: shifts) hnonneg 0 hx
  have hkernel :
      logDerivativeTower ((h :: shifts).length) =
        fun y ↦ (-1 : ℝ) ^ shifts.length *
          (shifts.length.factorial : ℝ) *
            (y ^ (h :: shifts).length)⁻¹ := by
    funext y
    simp only [List.length_cons, logDerivativeTower_succ]
    congr 2
    rw [show (-1 - (shifts.length : ℤ)) =
        -((shifts.length + 1 : ℕ) : ℤ) by
      push_cast
      ring]
    rw [zpow_neg, zpow_natCast]
  have hsign : (-1 : ℝ) ^ shifts.length ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hcancel :
      (-1 : ℝ) ^ shifts.length *
          ((shifts.length.factorial : ℝ) *
            iteratedShiftIntegral (h :: shifts)
              (fun y ↦ (y ^ (h :: shifts).length)⁻¹) x) =
        (-1 : ℝ) ^ shifts.length *
          (-realIteratedPhaseDifference (h :: shifts) Real.log x) := by
    calc
      _ = iteratedShiftIntegral (h :: shifts)
          (logDerivativeTower ((h :: shifts).length)) x := by
        rw [hkernel, iteratedShiftIntegral_const_mul]
        ring
      _ = (-1 : ℝ) ^ (h :: shifts).length *
          realIteratedPhaseDifference (h :: shifts) Real.log x := by
        simpa using htower
      _ = (-1 : ℝ) ^ shifts.length *
          (-realIteratedPhaseDifference (h :: shifts) Real.log x) := by
        simp only [List.length_cons, pow_succ]
        ring
  exact (mul_left_cancel₀ hsign hcancel).symm

/-- Every nonempty positive-shift logarithmic difference decreases with the
positive base point. -/
theorem antitoneOn_neg_realIteratedLogDifference
    (h : ℝ) (shifts : List ℝ)
    (hh : 0 ≤ h) (hshifts : ∀ k ∈ shifts, 0 ≤ k) :
    AntitoneOn
      (fun x ↦ -realIteratedPhaseDifference (h :: shifts) Real.log x)
      (Set.Ioi 0) := by
  have hnonneg : ∀ k ∈ h :: shifts, 0 ≤ k := by
    intro k hk
    simp only [List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact hh
    · exact hshifts k hk
  have hkernel := antitoneOn_iteratedShiftIntegral_invPow
    (h :: shifts).length (h :: shifts) hnonneg
  intro x hx y hy hxy
  change -realIteratedPhaseDifference (h :: shifts) Real.log y ≤
    -realIteratedPhaseDifference (h :: shifts) Real.log x
  rw [neg_realIteratedLogDifference_eq_kernelIntegral h shifts hh hshifts hx,
    neg_realIteratedLogDifference_eq_kernelIntegral h shifts hh hshifts hy]
  exact mul_le_mul_of_nonneg_left (hkernel hx hy hxy) (by positivity)

/-- Uniform scale bounds for every nonempty iterated logarithmic difference.
The numerator is the product of all A-process shifts and the derivative
factorial; the denominator has the expected power equal to the depth. -/
theorem neg_realIteratedLogDifference_bounds
    (h : ℝ) (shifts : List ℝ)
    (hh : 0 ≤ h) (hshifts : ∀ k ∈ shifts, 0 ≤ k)
    {x : ℝ} (hx : 0 < x) :
    (shifts.length.factorial : ℝ) * (h :: shifts).prod *
        ((x + (h :: shifts).sum) ^ (h :: shifts).length)⁻¹ ≤
      -realIteratedPhaseDifference (h :: shifts) Real.log x ∧
    -realIteratedPhaseDifference (h :: shifts) Real.log x ≤
      (shifts.length.factorial : ℝ) * (h :: shifts).prod *
        (x ^ (h :: shifts).length)⁻¹ := by
  have hnonneg : ∀ k ∈ h :: shifts, 0 ≤ k := by
    intro k hk
    simp only [List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact hh
    · exact hshifts k hk
  have hkernel := iteratedShiftIntegral_invPow_bounds
    (h :: shifts).length (h :: shifts) hnonneg hx
  have hfactorial : 0 ≤ (shifts.length.factorial : ℝ) := by positivity
  rw [neg_realIteratedLogDifference_eq_kernelIntegral
    h shifts hh hshifts hx]
  constructor
  · calc
      (shifts.length.factorial : ℝ) * (h :: shifts).prod *
          ((x + (h :: shifts).sum) ^ (h :: shifts).length)⁻¹ =
          (shifts.length.factorial : ℝ) *
            ((h :: shifts).prod *
              ((x + (h :: shifts).sum) ^ (h :: shifts).length)⁻¹) := by ring
      _ ≤ (shifts.length.factorial : ℝ) *
          iteratedShiftIntegral (h :: shifts)
            (fun y ↦ (y ^ (h :: shifts).length)⁻¹) x :=
        mul_le_mul_of_nonneg_left hkernel.1 hfactorial
  · calc
      (shifts.length.factorial : ℝ) *
          iteratedShiftIntegral (h :: shifts)
            (fun y ↦ (y ^ (h :: shifts).length)⁻¹) x ≤
          (shifts.length.factorial : ℝ) *
            ((h :: shifts).prod * (x ^ (h :: shifts).length)⁻¹) :=
        mul_le_mul_of_nonneg_left hkernel.2 hfactorial
      _ = (shifts.length.factorial : ℝ) * (h :: shifts).prod *
          (x ^ (h :: shifts).length)⁻¹ := by ring

end ZeroFreeRegion.VinogradovKorobov
