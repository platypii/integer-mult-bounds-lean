import IntegerMultBounds.Machine.RecursiveRowDivisor
import IntegerMultBounds.Machine.FixedBasePowerUntilRange
import IntegerMultBounds.Machine.RoundedRowDescriptor

/-! Actual arbitrary-width high-row metadata construction. Only the runtime
width is supplied. Depth, recursive divisor, minimal paired high-row range,
and least enclosing divisible row count are synthesized and cleaned. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighPrepare
noncomputable section
variable {a : ℕ}
open Networks

def base : ℕ := 125000
def worlds : ℕ := Shared50TapeGlobal.roleCount
def depth (e : ℕ) := Nat.clog base e
def envelope (e : ℕ) := base^depth e
def divisor (e : ℕ) := worlds^depth e
def highDepth (q e : ℕ) := ArbitraryWidthHighRows.rho q (divisor e)
def rows (q e : ℕ) := (q*q)^highDepth q e
def rounded (q e : ℕ) := RoundedRowDescriptor.rounded (rows q e) (divisor e)
def kBits (e : ℕ) := FixedBasePowerUntil.counter (depth e)
def mBits (e : ℕ) := FixedBasePowerStep.bits base (depth e)
def dBits (e : ℕ) := FixedBasePowerStep.bits worlds (depth e)
def rhoBits (q e : ℕ) := FixedBasePowerUntil.counter (highDepth q e)
def rBits (q e : ℕ) := FixedBasePowerStep.bits (q*q) (highDepth q e)
def roundedBits (q e : ℕ) := RoundedRowDescriptor.bits (rows q e) (divisor e)

private def hd : Option (List Bool) → ℤ | none => 0 | some _ => 1
private def tp : Option (List Bool) → ℤ → Fin (a+4)
  | none => fun _ => blank
  | some bs => RadixZeroFill.encodedBinary bs

/-- Retained e0; generatedk1,envelope2,divisor3,rho4,rows5,rounded6;
twelve shared scratch tapes7–18. Present descriptor heads are one. -/
def bank (es : List Bool) (ks ms ds rs ps zs : Option (List Bool)) : Tapes 19 a :=
  ⟨(fun i => match i.val with
    | 0 => 1 | 1 => hd ks | 2 => hd ms | 3 => hd ds
    | 4 => hd rs | 5 => hd ps | 6 => hd zs | _ => 0),
    (fun i => match i.val with
    | 0 => RadixZeroFill.encodedBinary es
    | 1 => tp ks | 2 => tp ms | 3 => tp ds
    | 4 => tp rs | 5 => tp ps | 6 => tp zs | _ => fun _ => blank)⟩

def input (es : List Bool) : Tapes 19 a := bank es none none none none none none
def first (e : ℕ) (es : List Bool) : Tapes 19 a :=
  bank es (some (kBits e)) (some (mBits e)) none none none none
def second (e : ℕ) (es : List Bool) : Tapes 19 a :=
  bank es (some (kBits e)) (some (mBits e)) (some (dBits e)) none none none
def third (q e : ℕ) (es : List Bool) : Tapes 19 a :=
  bank es (some (kBits e)) (some (mBits e)) (some (dBits e)) (some (rhoBits q e)) (some (rBits q e)) none
def fourth (q e : ℕ) (es : List Bool) : Tapes 19 a :=
  bank es (some (kBits e)) (some (mBits e)) (some (dBits e)) (some (rhoBits q e)) (some (rBits q e)) (some (roundedBits q e))
def output (q e : ℕ) (es : List Bool) : Tapes 19 a :=
  bank es (some (kBits e)) none (some (dBits e)) (some (rhoBits q e)) (some (rBits q e)) (some (roundedBits q e))

def depthPlacement : Fin (9+10) ≃ Fin 19 where
  toFun := fun i => match i.val with
    | 0 => 7 | 1 => 8 | 2 => 9 | 3 => 10 | 4 => 11 | 5 => 2 | 6 => 0 | 7 => 1 | 8 => 12 | 9 => 3 | 10 => 4 | 11 => 5 | 12 => 6 | 13 => 13 | 14 => 14 | 15 => 15 | 16 => 16 | 17 => 17 | _ => 18
  invFun := fun i => match i.val with
    | 0 => 6 | 1 => 7 | 2 => 5 | 3 => 9 | 4 => 10 | 5 => 11 | 6 => 12 | 7 => 0 | 8 => 1 | 9 => 2 | 10 => 3 | 11 => 4 | 12 => 8 | 13 => 13 | 14 => 14 | 15 => 15 | 16 => 16 | 17 => 17 | _ => 18
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def divisorPlacement : Fin (8+11) ≃ Fin 19 where
  toFun := fun i => match i.val with
    | 0 => 7 | 1 => 8 | 2 => 9 | 3 => 10 | 4 => 11 | 5 => 3 | 6 => 12 | 7 => 1 | 8 => 0 | 9 => 2 | 10 => 4 | 11 => 5 | 12 => 6 | 13 => 13 | 14 => 14 | 15 => 15 | 16 => 16 | 17 => 17 | _ => 18
  invFun := fun i => match i.val with
    | 0 => 8 | 1 => 7 | 2 => 9 | 3 => 5 | 4 => 10 | 5 => 11 | 6 => 12 | 7 => 0 | 8 => 1 | 9 => 2 | 10 => 3 | 11 => 4 | 12 => 6 | 13 => 13 | 14 => 14 | 15 => 15 | 16 => 16 | 17 => 17 | _ => 18
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def rowsPlacement : Fin (9+10) ≃ Fin 19 where
  toFun := fun i => match i.val with
    | 0 => 7 | 1 => 8 | 2 => 9 | 3 => 10 | 4 => 11 | 5 => 5 | 6 => 3 | 7 => 4 | 8 => 12 | 9 => 0 | 10 => 1 | 11 => 2 | 12 => 6 | 13 => 13 | 14 => 14 | 15 => 15 | 16 => 16 | 17 => 17 | _ => 18
  invFun := fun i => match i.val with
    | 0 => 9 | 1 => 10 | 2 => 11 | 3 => 6 | 4 => 7 | 5 => 5 | 6 => 12 | 7 => 0 | 8 => 1 | 9 => 2 | 10 => 3 | 11 => 4 | 12 => 8 | 13 => 13 | 14 => 14 | 15 => 15 | 16 => 16 | 17 => 17 | _ => 18
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def roundPlacement : Fin (15+4) ≃ Fin 19 where
  toFun := fun i => match i.val with
    | 0 => 5 | 1 => 3 | 2 => 7 | 3 => 8 | 4 => 9 | 5 => 6 | 6 => 10 | 7 => 11 | 8 => 12 | 9 => 13 | 10 => 14 | 11 => 15 | 12 => 16 | 13 => 17 | 14 => 18 | 15 => 0 | 16 => 1 | 17 => 2 | _ => 4
  invFun := fun i => match i.val with
    | 0 => 15 | 1 => 16 | 2 => 17 | 3 => 1 | 4 => 18 | 5 => 0 | 6 => 5 | 7 => 2 | 8 => 3 | 9 => 4 | 10 => 6 | 11 => 7 | 12 => 8 | 13 => 9 | 14 => 10 | 15 => 11 | 16 => 12 | 17 => 13 | _ => 14
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private theorem encoded_descriptor (bs : List Bool) : RadixZeroFill.encodedBinary (q := a) bs =
    BinaryDescriptorStack.descriptor bs := (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm

private theorem encoded_binary (bs : List Bool) : RadixZeroFill.encodedBinary (q := a) bs =
    CountedLoopReuseAlphabet.binary bs := by
  change (fun z => (RadixToBinary.binaryEncoding (q := a)).encode (CountedCopyReuse.binary bs z)) = _
  exact CountedLoopReuseAlphabet.encoding_binary bs

private theorem placed_exact {s u t r cost : ℕ} {M : Program s r a}
    (e : Fin (s+u) ≃ Fin t) (v w : Tapes t a) (small small' : Tapes s a)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

def depthProgram := Placement.placed (FixedBasePowerUntil.program (q := a) base) depthPlacement
def divisorProgram := Placement.placed (RecursiveRowDivisor.program (q := a)) divisorPlacement
def rowsProgram (q : ℕ) := Placement.placed (FixedBasePowerUntil.program (q := a) (q*q)) rowsPlacement
def roundProgram := Placement.placed (RoundedRowDescriptor.program (q := a)) roundPlacement
def eraseEnvelope := BinaryDescriptorCleanupList.oneProgram (a := a) (2 : Fin 19)
def program (q : ℕ) := seq (seq (seq (seq (depthProgram (a := a)) divisorProgram) (rowsProgram q)) roundProgram) eraseEnvelope

theorem base_ge_two : 2 ≤ base := by decide
theorem worlds_ge_base : base ≤ worlds := by
  unfold base worlds
  rw [Shared50RecursiveNodeLayout.roleCount_eq_W,Shared50Parameters.wire_count]
  decide

theorem depth_value (e : ℕ) : Counter.value (kBits e) = depth e := FixedBasePowerUntil.counter_value _
theorem envelope_value (e : ℕ) : Counter.value (mBits e) = envelope e := FixedBasePowerStep.bits_value _ _
theorem divisor_value (e : ℕ) : Counter.value (dBits e) = divisor e := FixedBasePowerStep.bits_value _ _
theorem high_depth_value (q e : ℕ) : Counter.value (rhoBits q e) = highDepth q e := FixedBasePowerUntil.counter_value _
theorem rows_value (q e : ℕ) : Counter.value (rBits q e) = rows q e := FixedBasePowerStep.bits_value _ _
theorem rounded_value (q e : ℕ) : Counter.value (roundedBits q e) = rounded q e := RoundedRowDescriptor.bits_value _ _

theorem divisor_positive (e : ℕ) : 0 < divisor e := Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < base) worlds_ge_base)
theorem rows_positive (q e : ℕ) (hq : 2 ≤ q) : 0 < rows q e := Nat.pow_pos (Nat.mul_pos (by omega) (by omega))
theorem divisor_le_rows (q e : ℕ) (hq : 2 ≤ q) : divisor e ≤ rows q e :=
  FixedBasePowerUntilBound.dominates (q*q) (divisor e) (by nlinarith)
theorem rows_le_rounded (q e : ℕ) (hq : 2 ≤ q) : rows q e ≤ rounded q e :=
  RoundedRowDescriptor.rows_le _ _ (rows_positive q e hq) (divisor_positive e)
theorem divisor_le_rounded (q e : ℕ) : divisor e ≤ rounded q e := RoundedRowDescriptor.divisor_le _ _
theorem width_le_divisor (e : ℕ) : e ≤ divisor e := by
  have he : e ≤ envelope e := FixedBasePowerUntilBound.dominates base e base_ge_two
  exact he.trans (Nat.pow_le_pow_left worlds_ge_base _)

private theorem depth_hoare (e : ℕ) (es : List Bool) (he : 0 < e)
    (hv : Counter.value es = e) (hc : GrowingCounterData.Canonical es) :
    HoareTime (depthProgram (a := a)) (fun v => v = input es) (fun v => v = first e es)
      ((FixedBasePowerUntil.constant base*base)*e) := by
  apply placed_exact depthPlacement _ _ _ _ _ _ _
    (FixedBasePowerUntilRange.constructs_threshold_linear base e base_ge_two he es hv hc)
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact encoded_descriptor _

private theorem divisor_hoare (e : ℕ) (es : List Bool) :
    HoareTime (divisorProgram (a := a)) (fun v => v = first e es) (fun v => v = second e es)
      (RecursiveRowDivisor.constant*divisor e) := by
  apply placed_exact divisorPlacement _ _ _ _ _ _ _
    (RecursiveRowDivisor.construct_hoare (kBits e) (depth e) (depth_value e) (FixedBasePowerUntil.counter_canonical _))
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact encoded_binary _

private theorem rows_hoare (q e : ℕ) (es : List Bool) (hq : 2 ≤ q) :
    HoareTime (rowsProgram (a := a) q) (fun v => v = second e es) (fun v => v = third q e es)
      ((FixedBasePowerUntil.constant (q*q)*(q*q))*divisor e) := by
  apply placed_exact rowsPlacement _ _ _ _ _ _ _
    (FixedBasePowerUntilRange.constructs_threshold_linear (q*q) (divisor e) (by nlinarith) (divisor_positive e)
      (dBits e) (divisor_value e) (FixedBasePowerStep.bits_canonical _ _))
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact encoded_descriptor _

private theorem round_hoare (q e : ℕ) (es : List Bool) (hq : 2 ≤ q) :
    HoareTime (roundProgram (a := a)) (fun v => v = third q e es) (fun v => v = fourth q e es)
      (4096*rounded q e) := by
  apply placed_exact roundPlacement _ _ _ _ _ _ _
    (RoundedRowDescriptor.construct_hoare (rBits q e) (dBits e) (rows q e) (divisor e)
      (rows_value q e) (divisor_value e) (FixedBasePowerStep.bits_canonical _ _) (FixedBasePowerStep.bits_canonical _ _)
      (rows_positive q e hq) (divisor_positive e))
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem erase_envelope_hoare (q e : ℕ) (es : List Bool) :
    HoareTime (eraseEnvelope (a := a)) (fun v => v = fourth q e es)
      (fun v => v = output q e es) (2*(mBits e).length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare (2 : Fin 19) (fourth (a := a) q e es) (mBits e)
    (encoded_descriptor _) rfl
  have he : SharedPlacementAlphabet.setTape (fourth (a := a) q e es) 2 (fun _ => blank) 0 = output q e es := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h
  exact h

/-- The physically produced row count is exactly the manuscript high range. -/
theorem rows_eq_high_rows (q e : ℕ) : rows q e = ArbitraryWidthHighRows.rowCount q (divisor e) :=
  (ArbitraryWidthHighRows.square_power q (highDepth q e)).symm

theorem rounded_eq_ceiling (q e : ℕ) (hq : 2 ≤ q) :
    rounded q e = divisor e*((rows q e+divisor e-1)/divisor e) :=
  RoundedRowDescriptor.rounded_eq_ceiling _ _ (rows_positive q e hq) (divisor_positive e)

theorem rounded_divisible (q e : ℕ) : divisor e ∣ rounded q e := RoundedRowDescriptor.rounded_dvd _ _

theorem rounded_bound (q e : ℕ) (hq : 2 ≤ q) : rounded q e < 2*(q*q)*divisor e := by
  have hr := FixedBasePowerUntilRange.final_power_lt (q*q) (divisor e) (by nlinarith) (divisor_positive e)
  have hz := RoundedRowDescriptor.rounded_lt_twice (rows q e) (divisor e)
    (rows_positive q e hq) (divisor_le_rows q e hq)
  change rows q e < (q*q)*divisor e at hr
  change rounded q e < 2*rows q e at hz
  nlinarith

private theorem envelope_le_rounded (q e : ℕ) : envelope e ≤ rounded q e :=
  (Nat.pow_le_pow_left worlds_ge_base (depth e)).trans (divisor_le_rounded q e)

private theorem canonical_length_bound (bs : List Bool) (cb : GrowingCounterData.Canonical bs)
    (q e : ℕ) (hb : Counter.value bs ≤ rounded q e) : bs.length ≤ 2*rounded q e := by
  have hw := GrowingCounterData.canonical_width bs cb
  have hl := Nat.log2_le_self (Counter.value bs)
  have hp := RoundedRowDescriptor.rounded_pos (rows q e) (divisor e) (divisor_positive e)
  change 0 < rounded q e at hp
  omega

def constant (q : ℕ) := FixedBasePowerUntil.constant base*base+
  RecursiveRowDivisor.constant+FixedBasePowerUntil.constant (q*q)*(q*q)+4110

/-- The complete fixed finite constructor starts with only canonical width e.
It returns the exact depth k, recursive divisor W^k, high selector rho,
minimal paired-power range R and least enclosing divisible R'. Every actual
subroutine and the unused envelope erasure is paid; private tapes are blank. -/
theorem construct_hoare (q e : ℕ) (hq : 2 ≤ q) (he : 0 < e) (es : List Bool)
    (hv : Counter.value es = e) (hc : GrowingCounterData.Canonical es) :
    HoareTime (program (a := a) q) (fun v => v = input es) (fun v => v = output q e es)
      (constant q*rounded q e) := by
  have h := ((((depth_hoare (a := a) e es he hv hc).seq (divisor_hoare e es)).seq
    (rows_hoare q e es hq)).seq (round_hoare q e es hq)).seq (erase_envelope_hoare q e es)
  have hwidth := (width_le_divisor e).trans (divisor_le_rounded q e)
  have hd := divisor_le_rounded q e
  have hm := canonical_length_bound (mBits e) (FixedBasePowerStep.bits_canonical _ _) q e
    (by rw [envelope_value]; exact envelope_le_rounded q e)
  have hp := RoundedRowDescriptor.rounded_pos (rows q e) (divisor e) (divisor_positive e)
  have h1 := Nat.mul_le_mul_left (FixedBasePowerUntil.constant base*base) hwidth
  have h2 := Nat.mul_le_mul_left RecursiveRowDivisor.constant hd
  have h3 := Nat.mul_le_mul_left (FixedBasePowerUntil.constant (q*q)*(q*q)) hd
  apply h.consequence (fun _ hh => hh) (fun _ hh => hh)
  unfold constant
  nlinarith

def cleanupSlots : List (Fin 19) := [1,3,4,5,6]
def cleanupWords (q e : ℕ) (i : Fin 19) : List Bool := match i.val with
  | 1 => kBits e | 3 => dBits e | 4 => rhoBits q e
  | 5 => rBits q e | 6 => roundedBits q e | _ => []
def cleanupProgram := BinaryDescriptorCleanupList.program (a := a) (by decide : 0 < 19) cleanupSlots

/-- All five generated descriptors are actually erased, recovering the
sole original width header and blank workspace exactly. -/
theorem cleanup_hoare (q e : ℕ) (hq : 2 ≤ q) (es : List Bool) :
    HoareTime (cleanupProgram (a := a)) (fun v => v = output q e es) (fun v => v = input es)
      (45*rounded q e) := by
  have h := BinaryDescriptorCleanupList.cleanup_hoare (a := a) (by decide : 0 < 19)
    cleanupSlots (by decide) (cleanupWords q e) (output q e es) (by
      intro i hi
      simp only [cleanupSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      all_goals exact ⟨rfl,encoded_descriptor _⟩)
  have heq : BinaryDescriptorCleanupList.cleared cleanupSlots (output (a := a) q e es) = input es := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [heq] at h
  have hp := RoundedRowDescriptor.rounded_pos (rows q e) (divisor e) (divisor_positive e)
  have hk : depth e ≤ rounded q e := by
    have hh := FixedBasePowerDescriptor.depth_le_power base (depth e) base_ge_two
    change depth e+1 ≤ envelope e at hh
    exact (by omega : depth e ≤ envelope e).trans (envelope_le_rounded q e)
  have hrho : highDepth q e ≤ rounded q e := by
    have hh := FixedBasePowerDescriptor.depth_le_power (q*q) (highDepth q e) (by nlinarith)
    change highDepth q e+1 ≤ rows q e at hh
    exact (by omega : highDepth q e ≤ rows q e).trans (rows_le_rounded q e hq)
  have hw : ∀ i ∈ cleanupSlots, (cleanupWords q e i).length ≤ 2*rounded q e := by
    intro i hi
    simp only [cleanupSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact canonical_length_bound _ (FixedBasePowerUntil.counter_canonical _) q e (by change Counter.value (kBits e) ≤ _; rw [depth_value]; exact hk)
    · exact canonical_length_bound _ (FixedBasePowerStep.bits_canonical _ _) q e (by change Counter.value (dBits e) ≤ _; rw [divisor_value]; exact divisor_le_rounded q e)
    · exact canonical_length_bound _ (FixedBasePowerUntil.counter_canonical _) q e (by change Counter.value (rhoBits q e) ≤ _; rw [high_depth_value]; exact hrho)
    · exact canonical_length_bound _ (FixedBasePowerStep.bits_canonical _ _) q e (by change Counter.value (rBits q e) ≤ _; rw [rows_value]; exact rows_le_rounded q e hq)
    · exact canonical_length_bound _ (RoundedRowDescriptor.bits_canonical _ _) q e (by change Counter.value (roundedBits q e) ≤ _; rw [rounded_value])
  have hb := BinaryDescriptorCleanupList.cost_le cleanupSlots (cleanupWords q e) (2*rounded q e) hw
  simp only [cleanupSlots,List.length_cons,List.length_nil] at hb
  change 0 < rounded q e at hp
  apply h.consequence (fun _ hh => hh) (fun _ hh => hh)
  unfold cleanupSlots
  nlinarith

/-- Runtime outputs in physical slot order k,D,rho,R,R'. -/
def words (q e : ℕ) : Fin 5 → List Bool := ![kBits e,dBits e,rhoBits q e,rBits q e,roundedBits q e]
def values (q e : ℕ) : Fin 5 → ℕ := ![depth e,divisor e,highDepth q e,rows q e,rounded q e]
def slots : Fin 5 → Fin 19 := ![1,3,4,5,6]

theorem words_value (q e : ℕ) (i : Fin 5) : Counter.value (words q e i) = values q e i := by
  fin_cases i
  · exact depth_value _
  · exact divisor_value _
  · exact high_depth_value _ _
  · exact rows_value _ _
  · exact rounded_value _ _

theorem words_canonical (q e : ℕ) (i : Fin 5) : GrowingCounterData.Canonical (words q e i) := by
  fin_cases i
  · exact FixedBasePowerUntil.counter_canonical _
  · exact FixedBasePowerStep.bits_canonical _ _
  · exact FixedBasePowerUntil.counter_canonical _
  · exact FixedBasePowerStep.bits_canonical _ _
  · exact RoundedRowDescriptor.bits_canonical _ _

theorem output_ready (q e : ℕ) (es : List Bool) (i : Fin 5) :
    (output (a := a) q e es).head (slots i) = 1 ∧
    (output (a := a) q e es).tape (slots i) = RadixZeroFill.encodedBinary (words q e i) := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

theorem worlds_eq_W : worlds = Shared50Parameters.W := Shared50RecursiveNodeLayout.roleCount_eq_W

theorem divisor_eq_manuscript (e : ℕ) : divisor e = Shared50Parameters.W^depth e := by
  unfold divisor; rw [worlds_eq_W]

theorem selector_eq_manuscript (q e : ℕ) (hq : 2 ≤ q) :
    highDepth q e = ⌈(depth e : ℝ)*Real.log Shared50Parameters.W/(2*Real.log q)⌉₊ := by
  unfold highDepth
  rw [divisor_eq_manuscript]
  exact ArbitraryWidthHighRows.rho_manuscript q _ _ hq

end
end IntegerMultBounds.Machine.ArbitraryWidthHighPrepare
