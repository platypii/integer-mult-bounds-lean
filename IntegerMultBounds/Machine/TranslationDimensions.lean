import IntegerMultBounds.Machine.RadixPowerMultipleDescriptor
import IntegerMultBounds.Machine.DimensionProductDescriptor

/-! Shared dimensions for a flat coordinate translation, built from one exponent
and one trailing record width. All descriptor calculations reuse blank work. -/
namespace IntegerMultBounds.Machine.TranslationDimensions

variable {q : ℕ} (hq : 2 ≤ q)

/-- Scratch slots zero, one and eight are always returned blank at head zero. -/
def scratchSlots : Fin 3 → Fin 9 := ![0,1,8]
def exponentSlot : Fin 9 := 2
def widthSlot : Fin 9 := 3
def qSlot : Fin 9 := 4
def pSlot : Fin 9 := 5
def suffixSlot : Fin 9 := 6
def bSlot : Fin 9 := 7

private def descriptorHead : Option (List Bool) → ℤ
  | none => 0
  | some _ => 1

private def descriptorTape : Option (List Bool) → ℤ → Fin (q+4)
  | none => fun _ => blank
  | some bs => RadixZeroFill.encodedBinary bs

/-- Four descriptor slots follow the two retained inputs. None means a genuinely
blank output tape with its head at zero, including the future marker cell. -/
def bank (bs ws : List Bool) (ds : Fin 4 → Option (List Bool)) : Tapes 9 q :=
  ⟨![0,0,1,1,descriptorHead (ds 0),descriptorHead (ds 1),descriptorHead (ds 2),descriptorHead (ds 3),0],
    ![fun _ => blank,fun _ => blank,RadixZeroFill.encodedBinary bs,RadixZeroFill.encodedBinary ws,
      descriptorTape (ds 0),descriptorTape (ds 1),descriptorTape (ds 2),descriptorTape (ds 3),fun _ => blank]⟩

def input (bs ws : List Bool) : Tapes 9 q := bank bs ws (fun _ => none)

def qBits (b : ℕ) : List Bool := RadixPowerDescriptor.bits hq b
def pBits (p b : ℕ) : List Bool := RadixPowerDescriptor.bits hq (p*b)
def suffixBits (s b : ℕ) : List Bool := RadixPowerDescriptor.bits hq (s*b)
def bBits (s b W : ℕ) : List Bool := DimensionProductDescriptor.bits (q^(s*b)) W

def descriptors (p s b W : ℕ) : Fin 4 → Option (List Bool) :=
  ![some (qBits hq b),some (pBits hq p b),some (suffixBits hq s b),some (bBits (q := q) s b W)]

def output (p s : ℕ) (bs ws : List Bool) (b W : ℕ) : Tapes 9 q :=
  bank bs ws (descriptors hq p s b W)

private theorem placed_exact {t u n r a cost : ℕ} {M : Program t r a}
    (e : Fin (t+u) ≃ Fin n) (v w : Tapes n a) (small small' : Tapes t a)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

omit hq in
private def powerPlacement (j : Fin 3) : Fin (4+5) ≃ Fin 9 :=
  Equiv.swap 3 ⟨4+j,Nat.lt_trans (Nat.add_lt_add_left j.isLt 4) (by decide)⟩

private theorem power_active_empty (j : Fin 3) (bs ws : List Bool)
    (ds : Fin 4 → Option (List Bool)) (hj : ds j.castSucc = none) :
    Placement.active (powerPlacement j) (bank (q := q) bs ws ds) = RadixPowerMultipleDescriptor.input bs := by
  have hs : descriptorHead (ds j.castSucc) = 0 ∧
      descriptorTape (q := q) (ds j.castSucc) = (fun _ => blank) := by
    rw [hj]
    exact ⟨rfl,rfl⟩
  fin_cases j <;> apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    first | rfl | exact hs.1 | exact hs.2

private theorem power_active_full (j : Fin 3) (bs ws : List Bool)
    (ds : Fin 4 → Option (List Bool)) (n : ℕ)
    (hj : ds j.castSucc = some (RadixPowerDescriptor.bits hq n)) :
    Placement.active (powerPlacement j) (bank (q := q) bs ws ds) = RadixPowerMultipleDescriptor.output hq bs n := by
  have hs : descriptorHead (ds j.castSucc) = 1 ∧
      descriptorTape (q := q) (ds j.castSucc) = RadixZeroFill.encodedBinary (RadixPowerDescriptor.bits hq n) := by
    rw [hj]
    exact ⟨rfl,rfl⟩
  fin_cases j <;> apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    first | rfl | exact hs.1 | exact hs.2

private theorem power_frame_zero (bs ws xs : List Bool) (ds : Fin 4 → Option (List Bool)) :
    Placement.extra (powerPlacement 0) (bank (q := q) bs ws ds) =
      Placement.extra (powerPlacement 0) (bank bs ws (Function.update ds 0 (some xs))) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [powerPlacement,bank,Equiv.swap_apply_def]

private theorem power_frame_one (bs ws xs : List Bool) (ds : Fin 4 → Option (List Bool)) :
    Placement.extra (powerPlacement 1) (bank (q := q) bs ws ds) =
      Placement.extra (powerPlacement 1) (bank bs ws (Function.update ds 1 (some xs))) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [powerPlacement,bank,Equiv.swap_apply_def]

private theorem power_frame_two (bs ws xs : List Bool) (ds : Fin 4 → Option (List Bool)) :
    Placement.extra (powerPlacement 2) (bank (q := q) bs ws ds) =
      Placement.extra (powerPlacement 2) (bank bs ws (Function.update ds 2 (some xs))) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [powerPlacement,bank,Equiv.swap_apply_def]

private theorem power_frame (j : Fin 3) (bs ws xs : List Bool) (ds : Fin 4 → Option (List Bool)) :
    Placement.extra (powerPlacement j) (bank (q := q) bs ws ds) =
      Placement.extra (powerPlacement j) (bank bs ws (Function.update ds j.castSucc (some xs))) := by
  fin_cases j
  · exact power_frame_zero bs ws xs ds
  · exact power_frame_one bs ws xs ds
  · exact power_frame_two bs ws xs ds

private theorem power_hoare (j : Fin 3) (k : ℕ) (bs ws : List Bool)
    (ds : Fin 4 → Option (List Bool)) (hj : ds j.castSucc = none)
    (b : ℕ) (hb : Counter.value bs = b) (hc : GrowingCounterData.Canonical bs) :
    HoareTime (Placement.placed (RadixPowerMultipleDescriptor.program hq k) (powerPlacement j))
      (fun v => v = bank bs ws ds)
      (fun v => v = bank bs ws (Function.update ds j.castSucc (some (RadixPowerDescriptor.bits hq (k*b)))))
      ((24*k+75)*q^(k*b)) :=
  placed_exact (powerPlacement j) _ _ _ _
    (power_active_empty j bs ws ds hj)
    (power_active_full hq j bs ws _ (k*b) (Function.update_self ..))
    (power_frame j bs ws _ ds)
    (RadixPowerMultipleDescriptor.construct_hoare_linear hq k bs b hb hc)

private def afterQ (b : ℕ) : Fin 4 → Option (List Bool) := ![some (qBits hq b),none,none,none]
private def afterP (p b : ℕ) : Fin 4 → Option (List Bool) :=
  ![some (qBits hq b),some (pBits hq p b),none,none]
private def afterS (p s b : ℕ) : Fin 4 → Option (List Bool) :=
  ![some (qBits hq b),some (pBits hq p b),some (suffixBits hq s b),none]

private def productPlacement : Fin (6+3) ≃ Fin 9 where
  toFun := fun i => ![0,7,1,3,8,6,2,4,5] i
  invFun := fun i => ![0,2,6,3,7,8,5,1,4] i
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private theorem product_active_input (p s : ℕ) (bs ws : List Bool) (b : ℕ) :
    Placement.active productPlacement (bank (q := q) bs ws (afterS hq p s b)) =
      DimensionProductDescriptor.input ws (suffixBits hq s b) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem product_active_output (p s : ℕ) (bs ws : List Bool) (b W : ℕ) :
    Placement.active productPlacement (output hq p s bs ws b W) =
      DimensionProductDescriptor.output ws (suffixBits hq s b) (q^(s*b)) W := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem product_frame (p s : ℕ) (bs ws : List Bool) (b W : ℕ) :
    Placement.extra productPlacement (bank bs ws (afterS hq p s b)) =
      Placement.extra productPlacement (output hq p s bs ws b W) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [productPlacement,bank,output,afterS,descriptors]

private theorem product_hoare (p s : ℕ) (bs ws : List Bool) (b W : ℕ) (hW : 0 < W)
    (hw : Counter.value ws = W) (cw : GrowingCounterData.Canonical ws) :
    HoareTime (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlacement)
      (fun v => v = bank bs ws (afterS hq p s b)) (fun v => v = output hq p s bs ws b W)
      (53*(q^(s*b)*W)+28) :=
  placed_exact productPlacement _ _ _ _
    (product_active_input hq p s bs ws b)
    (product_active_output hq p s bs ws b W)
    (product_frame hq p s bs ws b W)
    (DimensionProductDescriptor.construct_hoare ws (suffixBits hq s b)
      (q^(s*b)) W hW hw (RadixPowerDescriptor.bits_value hq (s*b)) cw
      (RadixPowerDescriptor.bits_canonical hq (s*b)))

/-- Only the fixed coordinate counts and radix determine the finite program. -/
def program (p s : ℕ) :=
  seq (seq (seq
    (Placement.placed (RadixPowerMultipleDescriptor.program hq 1) (powerPlacement 0))
    (Placement.placed (RadixPowerMultipleDescriptor.program hq p) (powerPlacement 1)))
    (Placement.placed (RadixPowerMultipleDescriptor.program hq s) (powerPlacement 2)))
    (Placement.placed (DimensionProductDescriptor.program (q := q)) productPlacement)

/-- Every input copy, marker, scan, and cleanup is charged. -/
theorem construct_hoare (p s : ℕ) (bs ws : List Bool) (b W : ℕ)
    (hb : Counter.value bs = b) (hw : Counter.value ws = W) (hW : 0 < W)
    (cb : GrowingCounterData.Canonical bs) (cw : GrowingCounterData.Canonical ws) :
    HoareTime (program hq p s) (fun v => v = input bs ws)
      (fun v => v = output hq p s bs ws b W)
      (99*q^b+(24*p+75)*q^(p*b)+(24*s+75)*q^(s*b)+53*(q^(s*b)*W)+31) := by
  have hq' := power_hoare hq 0 1 bs ws (fun _ => none) rfl b hb cb
  have hq'' : HoareTime (Placement.placed (RadixPowerMultipleDescriptor.program hq 1) (powerPlacement 0)) (fun v => v = input bs ws) (fun v => v = bank bs ws (afterQ hq b)) (99*q^b) := by
    apply hq'.consequence (fun _ h => h) _ (by simp)
    intro v hv
    rw [hv]
    congr 1
    funext i; fin_cases i <;> simp [afterQ,qBits]
  have hp := power_hoare hq 1 p bs ws (afterQ hq b) rfl b hb cb
  have hp' : HoareTime (Placement.placed (RadixPowerMultipleDescriptor.program hq p) (powerPlacement 1)) (fun v => v = bank bs ws (afterQ hq b))
      (fun v => v = bank bs ws (afterP hq p b)) ((24*p+75)*q^(p*b)) := by
    apply hp.consequence (fun _ h => h) _ le_rfl
    intro v hv
    rw [hv]
    congr 1
    funext i; fin_cases i <;> simp [afterQ,afterP,pBits]
  have hs := power_hoare hq 2 s bs ws (afterP hq p b) rfl b hb cb
  have hs' : HoareTime (Placement.placed (RadixPowerMultipleDescriptor.program hq s) (powerPlacement 2)) (fun v => v = bank bs ws (afterP hq p b))
      (fun v => v = bank bs ws (afterS hq p s b)) ((24*s+75)*q^(s*b)) := by
    apply hs.consequence (fun _ h => h) _ le_rfl
    intro v hv
    rw [hv]
    congr 1
    funext i; fin_cases i <;> simp [afterP,afterS,suffixBits]
  exact (((hq''.seq hp').seq hs').seq (product_hoare hq p s bs ws b W hW hw cw)).consequence
    (fun _ h => h) (fun _ h => h) (by omega)


/-- Construction is linear in the complete row-major array volume. -/
theorem construct_hoare_volume (p s : ℕ) (bs ws : List Bool) (b W : ℕ)
    (hb : Counter.value bs = b) (hw : Counter.value ws = W) (hW : 0 < W)
    (cb : GrowingCounterData.Canonical bs) (cw : GrowingCounterData.Canonical ws) :
    HoareTime (program hq p s) (fun v => v = input bs ws)
      (fun v => v = output hq p s bs ws b W)
      ((24*p+24*s+333)*(q^(p*b)*q^b*(q^(s*b)*W))) := by
  let P := q^(p*b)
  let Q := q^b
  let S := q^(s*b)
  let B := S*W
  let V := P*Q*B
  have hP : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have hQ : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  have hS : 1 ≤ S := Nat.one_le_pow _ _ (by omega)
  have hSB : S ≤ B := Nat.le_mul_of_pos_right _ hW
  have hB : 1 ≤ B := hS.trans hSB
  have hPQ : 1 ≤ P*Q := by nlinarith
  have hBV : B ≤ V := by exact Nat.le_mul_of_pos_left B hPQ
  have hQV : Q ≤ V := by
    have h1 : Q ≤ P*Q := Nat.le_mul_of_pos_left _ hP
    have h2 : P*Q ≤ V := Nat.le_mul_of_pos_right _ hB
    exact h1.trans h2
  have hPV : P ≤ V := by
    have h1 : P ≤ P*Q := Nat.le_mul_of_pos_right _ hQ
    have h2 : P*Q ≤ V := Nat.le_mul_of_pos_right _ hB
    exact h1.trans h2
  have hSV := hSB.trans hBV
  have hV := hB.trans hBV
  apply (construct_hoare hq p s bs ws b W hb hw hW cb cw).consequence
    (fun _ h => h) (fun _ h => h)
  change 99*Q+(24*p+75)*P+(24*s+75)*S+53*B+31 ≤ (24*p+24*s+333)*V
  nlinarith [Nat.mul_le_mul_left (24*p+75) hPV,Nat.mul_le_mul_left (24*s+75) hSV]

/-- The physical constructors produce exactly the schedule's canonical words. -/
theorem qBits_eq_advance (b : ℕ) : qBits hq b = GrowingCounterData.advance (q^b) [] := by
  unfold qBits RadixPowerDescriptor.bits RadixToBinaryData.output
  rw [RadixPowerWord.digits_value]

theorem pBits_eq_advance (p b : ℕ) : pBits hq p b = GrowingCounterData.advance (q^(p*b)) [] := by
  unfold pBits RadixPowerDescriptor.bits RadixToBinaryData.output
  rw [RadixPowerWord.digits_value]

theorem suffixBits_eq_advance (s b : ℕ) : suffixBits hq s b = GrowingCounterData.advance (q^(s*b)) [] := by
  unfold suffixBits RadixPowerDescriptor.bits RadixToBinaryData.output
  rw [RadixPowerWord.digits_value]

theorem bBits_eq_advance (s b W : ℕ) : bBits (q := q) s b W =
    GrowingCounterData.advance (q^(s*b)*W) [] := rfl

theorem qBits_value (b : ℕ) : Counter.value (qBits hq b) = q^b :=
  RadixPowerDescriptor.bits_value hq b

theorem pBits_value (p b : ℕ) : Counter.value (pBits hq p b) = q^(p*b) :=
  RadixPowerDescriptor.bits_value hq (p*b)

theorem suffixBits_value (s b : ℕ) : Counter.value (suffixBits hq s b) = q^(s*b) :=
  RadixPowerDescriptor.bits_value hq (s*b)

theorem bBits_value (s b W : ℕ) : Counter.value (bBits (q := q) s b W) = q^(s*b)*W :=
  DimensionProductDescriptor.bits_value _ _

theorem descriptors_canonical (p s b W : ℕ) :
    GrowingCounterData.Canonical (qBits hq b) ∧
    GrowingCounterData.Canonical (pBits hq p b) ∧
    GrowingCounterData.Canonical (suffixBits hq s b) ∧
    GrowingCounterData.Canonical (bBits (q := q) s b W) :=
  ⟨RadixPowerDescriptor.bits_canonical hq b,RadixPowerDescriptor.bits_canonical hq (p*b),
    RadixPowerDescriptor.bits_canonical hq (s*b),DimensionProductDescriptor.bits_canonical _ _⟩

/-- The two and only two supplied descriptors retain their complete tapes. -/
theorem inputs_preserved (p s : ℕ) (bs ws : List Bool) (b W : ℕ) :
    (output hq p s bs ws b W).head exponentSlot = (input (q := q) bs ws).head exponentSlot ∧
    (output hq p s bs ws b W).tape exponentSlot = (input (q := q) bs ws).tape exponentSlot ∧
    (output hq p s bs ws b W).head widthSlot = (input (q := q) bs ws).head widthSlot ∧
    (output hq p s bs ws b W).tape widthSlot = (input (q := q) bs ws).tape widthSlot := by
  simp [output,input,bank,exponentSlot,widthSlot]

theorem scratch_blank (p s : ℕ) (bs ws : List Bool) (b W : ℕ) (i : Fin 3) :
    (output hq p s bs ws b W).head (scratchSlots i) = 0 ∧
    (output hq p s bs ws b W).tape (scratchSlots i) = fun _ => blank := by
  fin_cases i <;> simp [output,bank,scratchSlots]

theorem input_workspace_blank (bs ws : List Bool) (i : Fin 9)
    (hb : i ≠ exponentSlot) (hw : i ≠ widthSlot) :
    (input (q := q) bs ws).head i = 0 ∧ (input (q := q) bs ws).tape i = fun _ => blank := by
  fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact (hb rfl).elim | exact (hw rfl).elim

theorem output_q (p s : ℕ) (bs ws : List Bool) (b W : ℕ) :
    (output hq p s bs ws b W).head qSlot = 1 ∧
    (output hq p s bs ws b W).tape qSlot = RadixZeroFill.encodedBinary (qBits hq b) := by
  simp [output,bank,descriptors,qSlot,descriptorHead,descriptorTape]

theorem output_p (p s : ℕ) (bs ws : List Bool) (b W : ℕ) :
    (output hq p s bs ws b W).head pSlot = 1 ∧
    (output hq p s bs ws b W).tape pSlot = RadixZeroFill.encodedBinary (pBits hq p b) := by
  simp [output,bank,descriptors,pSlot,descriptorHead,descriptorTape]

theorem output_suffix (p s : ℕ) (bs ws : List Bool) (b W : ℕ) :
    (output hq p s bs ws b W).head suffixSlot = 1 ∧
    (output hq p s bs ws b W).tape suffixSlot = RadixZeroFill.encodedBinary (suffixBits hq s b) := by
  simp [output,bank,descriptors,suffixSlot,descriptorHead,descriptorTape]

theorem output_b (p s : ℕ) (bs ws : List Bool) (b W : ℕ) :
    (output hq p s bs ws b W).head bSlot = 1 ∧
    (output hq p s bs ws b W).tape bSlot = RadixZeroFill.encodedBinary (bBits (q := q) s b W) := by
  simp [output,bank,descriptors,bSlot,descriptorHead,descriptorTape]

end IntegerMultBounds.Machine.TranslationDimensions
