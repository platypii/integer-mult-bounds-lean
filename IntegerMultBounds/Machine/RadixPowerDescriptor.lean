import IntegerMultBounds.Machine.RadixPowerWord

/-! A fixed four-tape machine computes the canonical binary descriptor q^b
from the canonical binary descriptor b, restoring every scratch tape to blank. -/
namespace IntegerMultBounds.Machine.RadixPowerDescriptor

open RadixDigits MarkedWordCleanup
variable {q : ℕ} (hq : 2 ≤ q)

def bits (b : ℕ) : List Bool := RadixToBinaryData.output (RadixPowerWord.digits hq b)

theorem bits_canonical (b : ℕ) : GrowingCounterData.Canonical (bits hq b) :=
  RadixToBinaryData.output_canonical _

@[simp] theorem bits_value (b : ℕ) : Counter.value (bits hq b) = q^b := by
  rw [bits,RadixToBinaryData.output_value,RadixPowerWord.digits_value]

/-- Slots: radix scratch, clock scratch, exponent input, power output. -/
def input (bs : List Bool) : Tapes 4 q :=
  (RadixPowerWord.input bs).append (one (fun _ => blank) 0)

private def ready (bs : List Bool) (b : ℕ) : Tapes 4 q :=
  (RadixPowerWord.output hq bs b).append (one (fun _ => blank) 0)

private def converted (bs : List Bool) (b : ℕ) : Tapes 4 q :=
  ⟨![0,0,1,1],![word ((RadixPowerWord.digits hq b).map digitSymbol),fun _ => blank,
    RadixZeroFill.encodedBinary bs,RadixZeroFill.encodedBinary (bits hq b)]⟩

/-- Only the original input and computed canonical output remain nonblank. -/
def output (bs : List Bool) (b : ℕ) : Tapes 4 q :=
  ⟨![0,0,1,1],![fun _ => blank,fun _ => blank,
    RadixZeroFill.encodedBinary bs,RadixZeroFill.encodedBinary (bits hq b)]⟩

def conversionPlacement : Fin (3+1) ≃ Fin 4 where
  toFun := fun i => ![3,1,0,2] i
  invFun := fun i => ![2,1,3,0] i
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

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

/-- No program state depends on the runtime exponent. -/
def program : Program 4 53 q :=
  seq (seq (extend (RadixPowerWord.program hq) 1)
    (Placement.placed (RadixToBinary.convertProgram hq) conversionPlacement))
    (extend MarkedWordCleanup.program 3)

theorem construct_hoare (bs : List Bool) (b : ℕ) (hb : Counter.value bs = b) :
    HoareTime (program hq) (fun v => v = input bs) (fun v => v = output hq bs b)
      (10*q^b+18*b+7*bs.length+57) := by
  have hi : HoareTime (extend (RadixPowerWord.program hq) 1)
      (fun v => v = input bs) (fun v => v = ready hq bs b) (10*b+7*bs.length+27) := by
    apply ((RadixPowerWord.construct_hoare hq bs b hb).extend (one (fun _ => blank) 0)).consequence
      _ _ le_rfl
    · intro v hv; exact ⟨_,rfl,hv⟩
    · rintro v ⟨w,rfl,rfl⟩; rfl
  exact ((hi.seq (conversion_hoare hq bs b)).seq (cleanup_hoare hq bs b)).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

/-- The complete setup, conversion, and erasure cost is linear in q^b. -/
theorem construct_hoare_linear (bs : List Bool) (b : ℕ) (hb : Counter.value bs = b)
    (hc : GrowingCounterData.Canonical bs) :
    HoareTime (program hq) (fun v => v = input bs) (fun v => v = output hq bs b) (99*q^b) := by
  have hw := GrowingCounterData.canonical_width bs hc
  have hl := Nat.log2_le_self b
  have hp := RadixToBinaryData.width_le_power hq b
  have hpos : 1 ≤ q^b := Nat.one_le_pow _ _ (by omega)
  rw [hb] at hw
  exact (construct_hoare hq bs b hb).consequence (fun _ h => h) (fun _ h => h) (by omega)

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

end IntegerMultBounds.Machine.RadixPowerDescriptor
