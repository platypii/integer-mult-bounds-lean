import IntegerMultBounds.Machine.RadixPowerMultipleWord
import IntegerMultBounds.Machine.RadixPowerDescriptor

/-! A fixed four-tape machine computes q^(k*b) from one binary b descriptor.
The fixed k belongs to finite control; even k=0 reads no supplied dimension. -/
namespace IntegerMultBounds.Machine.RadixPowerMultipleDescriptor

open RadixDigits MarkedWordCleanup
variable {q : ℕ} (hq : 2 ≤ q)

def bits (b : ℕ) : List Bool := RadixPowerDescriptor.bits hq b

theorem bits_canonical (b : ℕ) : GrowingCounterData.Canonical (bits hq b) :=
  RadixToBinaryData.output_canonical _

@[simp] theorem bits_value (b : ℕ) : Counter.value (bits hq b) = q^b := by
  exact RadixPowerDescriptor.bits_value hq b

/-- Slots: radix scratch, clock scratch, exponent input, power output. -/
def input (bs : List Bool) : Tapes 4 q :=
  RadixPowerDescriptor.input bs

private def ready (bs : List Bool) (b : ℕ) : Tapes 4 q :=
  (RadixPowerWord.output hq bs b).append (one (fun _ => blank) 0)

private def converted (bs : List Bool) (b : ℕ) : Tapes 4 q :=
  ⟨![0,0,1,1],![word ((RadixPowerWord.digits hq b).map digitSymbol),fun _ => blank,
    RadixZeroFill.encodedBinary bs,RadixZeroFill.encodedBinary (bits hq b)]⟩

/-- Only the original input and computed canonical output remain nonblank. -/
def output (bs : List Bool) (b : ℕ) : Tapes 4 q :=
  RadixPowerDescriptor.output hq bs b

def conversionPlacement : Fin (3+1) ≃ Fin 4 := RadixPowerDescriptor.conversionPlacement

private theorem conversion_hoare (bs : List Bool) (b : ℕ) :
    HoareTime (Placement.placed (RadixToBinary.convertProgram hq) conversionPlacement)
      (fun v => v = ready hq bs b) (fun v => v = converted hq bs b)
      (10*q^b+6*b+20) := by
  let xs := RadixPowerWord.digits hq b
  have ha : Placement.active conversionPlacement (ready hq bs b) = RadixToBinary.input xs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hf : Placement.active conversionPlacement (converted hq bs b) = RadixToBinary.output xs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have he : Placement.extra conversionPlacement (ready hq bs b) =
      Placement.extra conversionPlacement (converted hq bs b) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  apply (Placement.hoare_at (RadixToBinary.convert_hoare hq xs) conversionPlacement
    (ready hq bs b) ha).consequence (fun _ h => h) _ (by simp [xs]; omega)
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

private theorem cleanup_hoare (bs : List Bool) (b : ℕ) :
    HoareTime (extend (MarkedWordCleanup.program (a := q)) 3)
      (fun v => v = converted hq bs b) (fun v => v = output hq bs b) (2*b+8) := by
  let xs := (RadixPowerWord.digits hq b).map digitSymbol
  let frame : Tapes 3 q := ⟨![0,1,1],![fun _ => blank,RadixZeroFill.encodedBinary bs,
    RadixZeroFill.encodedBinary (bits hq b)]⟩
  have hd : ∀ x ∈ xs, x ≠ (blank : Fin (q+4)) := by
    intro x hx
    obtain ⟨d,_,rfl⟩ := List.mem_map.mp hx
    simp [digitSymbol,blank]
  apply ((MarkedWordCleanup.cleanup_hoare xs hd).extend frame).consequence _ _ (by simp [xs]; omega)
  · intro v hv
    refine ⟨_,rfl,?_⟩
    rw [hv]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · rintro v ⟨w,rfl,rfl⟩
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- Only k, never b, determines this finite control. -/
def program (k : ℕ) : Program 4 (2+RadixPowerMultipleWord.loopStates k+1+3+3+18+6) q :=
  seq (seq (extend (RadixPowerMultipleWord.program hq k) 1)
    (Placement.placed (RadixToBinary.convertProgram hq) conversionPlacement))
    (extend MarkedWordCleanup.program 3)

theorem construct_hoare (k : ℕ) (bs : List Bool) (b : ℕ) (hb : Counter.value bs = b) :
    HoareTime (program hq k) (fun v => v = input bs) (fun v => v = output hq bs (k*b))
      (10*q^(k*b)+18*(k*b)+7*k*bs.length+17*k+40) := by
  have hi : HoareTime (extend (RadixPowerMultipleWord.program hq k) 1)
      (fun v => v = input bs) (fun v => v = ready hq bs (k*b))
      (10*(k*b)+7*k*bs.length+17*k+10) := by
    apply ((RadixPowerMultipleWord.construct_hoare hq k bs b hb).extend
      (one (fun _ => blank) 0)).consequence _ _ le_rfl
    · intro v hv; exact ⟨_,rfl,hv⟩
    · rintro v ⟨w,rfl,rfl⟩; rfl
  exact ((hi.seq (conversion_hoare hq bs (k*b))).seq (cleanup_hoare hq bs (k*b))).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

/-- Includes k=0: no descriptor scan is performed by that branch. -/
theorem construct_hoare_linear (k : ℕ) (bs : List Bool) (b : ℕ) (hb : Counter.value bs = b)
    (hc : GrowingCounterData.Canonical bs) :
    HoareTime (program hq k) (fun v => v = input bs) (fun v => v = output hq bs (k*b))
      ((24*k+75)*q^(k*b)) := by
  have hw := GrowingCounterData.canonical_width bs hc
  have hl := Nat.log2_le_self b
  have hp := RadixToBinaryData.width_le_power hq (k*b)
  have hpos : 1 ≤ q^(k*b) := Nat.one_le_pow _ _ (by omega)
  rw [hb] at hw
  have hw' : bs.length ≤ b+1 := by omega
  have hkw : 7*k*bs.length ≤ 7*(k*b)+7*k := by nlinarith [Nat.mul_le_mul_left (7*k) hw']
  have hk : 24*k ≤ 24*k*q^(k*b) := Nat.le_mul_of_pos_right _ hpos
  apply (construct_hoare hq k bs b hb).consequence (fun _ h => h) (fun _ h => h)
  nlinarith

/-- The exponent tape is unchanged, including its head. -/
theorem exponent_preserved (bs : List Bool) (b : ℕ) :
    (output hq bs b).head 2 = (input (q := q) bs).head 2 ∧
      (output hq bs b).tape 2 = (input (q := q) bs).tape 2 := ⟨rfl,rfl⟩

theorem scratch_blank (bs : List Bool) (b : ℕ) (i : Fin 2) :
    (output hq bs b).head (Fin.castAdd 2 i) = 0 ∧
      (output hq bs b).tape (Fin.castAdd 2 i) = fun _ => blank := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

theorem output_descriptor (bs : List Bool) (b : ℕ) :
    (output hq bs b).head 3 = 1 ∧
      (output hq bs b).tape 3 = RadixZeroFill.encodedBinary (bits hq b) := ⟨rfl,rfl⟩

end IntegerMultBounds.Machine.RadixPowerMultipleDescriptor
