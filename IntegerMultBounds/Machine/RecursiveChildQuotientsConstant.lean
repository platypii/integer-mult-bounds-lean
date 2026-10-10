import IntegerMultBounds.Machine.BinaryDescriptorStackRoundtrip
import IntegerMultBounds.Machine.FiniteReturnStackAt
import IntegerMultBounds.Machine.ExactFrame
import IntegerMultBounds.Machine.BinaryCanonicalData
import Mathlib.Data.Nat.Bits

/-! A literal finite-control writer for the fixed divisor constants used by
child quotient production. All writes, rewinds and joins are charged. -/
namespace IntegerMultBounds.Machine.RecursiveChildQuotientsConstant
variable {a : ℕ}

def writeSymbol (x : Fin (a+4)) : Program 1 2 a :=
  DescriptorStackControl.once (by decide) (fun _ _ => (x,Move.right))

private theorem write_hoare (x : Fin (a+4)) (f : ℤ → Fin (a+4)) (p : ℤ) :
    HoareTime (writeSymbol x) (fun v => v = FiniteReturnStack.bank f p)
      (fun v => v = FiniteReturnStack.bank (Function.update f p x) (p+1)) 1 := by
  apply (DescriptorStackControl.once_hoare (by decide) _ (FiniteReturnStack.bank f p)).consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk
  · funext i; rfl
  · funext i z; simp [FiniteReturnStack.bank,Function.update_apply]; rfl

def writeStates : List (Fin (a+4)) → ℕ
  | [] => 1
  | _::xs => 2+writeStates xs

def writeProgram : (xs : List (Fin (a+4))) → Program 1 (writeStates xs) a
  | [] => skip 1 a (by decide)
  | x::xs => seq (writeSymbol x) (writeProgram xs)

private theorem writes_hoare (xs : List (Fin (a+4))) (f : ℤ → Fin (a+4)) (p : ℤ) :
    HoareTime (writeProgram xs) (fun v => v = FiniteReturnStack.bank f p)
      (fun v => v = FiniteReturnStack.bank (putWord f p xs) (p+xs.length)) (2*xs.length) := by
  induction xs generalizing f p with
  | nil => simpa [writeProgram,writeStates,putWord] using skip_hoare (a := a) (by decide : 0 < 1) (FiniteReturnStack.bank f p)
  | cons x xs ih =>
    have h := (write_hoare x f p).seq (ih (Function.update f p x) (p+1))
    rw [← putWord_cons] at h
    apply h.consequence (fun _ h => h) _ (by simp only [List.length_cons]; omega)
    intro v hv
    convert hv using 1; simp [List.length_cons,add_assoc,add_comm]

/-- Binary recursion avoids constructing a fixed descriptor by one increment
per represented integer. The resulting word is exactly the original word. -/
def bits (n : ℕ) : List Bool := n.bits

private theorem nat_bits_value (n : ℕ) : Counter.value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    cases b <;> simp [Counter.value,Nat.bit,ih]; omega

private theorem nat_bits_canonical (n : ℕ) : GrowingCounterData.Canonical n.bits := by
  induction n using Nat.binaryRec' with
  | zero => exact Or.inl rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    cases he : n.bits with
    | nil =>
      have hn : n=0 := by simpa [he,Counter.value] using (nat_bits_value n).symm
      subst n
      have hb := h rfl
      subst b
      exact Or.inr rfl
    | cons c cs =>
      rcases ih with hn | hl
      · rw [he] at hn; contradiction
      · exact Or.inr (by simpa [he] using hl)

theorem bits_value (n : ℕ) : Counter.value (bits n) = n := nat_bits_value n

theorem bits_canonical (n : ℕ) : GrowingCounterData.Canonical (bits n) :=
  nat_bits_canonical n

theorem bits_eq_advance (n : ℕ) : bits n = GrowingCounterData.advance n [] :=
  BinaryCanonicalData.value_injective _ _ (bits_canonical n)
    (GrowingCounterData.advance_canonical n [] (Or.inl rfl))
    ((bits_value n).trans (GrowingCounterData.empty_value n).symm)

def program (n : ℕ) := seq (seq (seq (writeSymbol (separator : Fin (a+4)))
  (writeProgram ((bits n).map bitSymbol))) (Rewind.program separator)) StepRight.program

def cost (n : ℕ) : ℕ := 3*(bits n).length+6

theorem initialize_hoare (n : ℕ) :
    HoareTime (program (a := a) n) (fun v => v = FiniteReturnStack.bank (fun _ => blank) 0)
      (fun v => v = FiniteReturnStack.bank (BinaryDescriptorStack.descriptor (bits n)) 1) (cost n) := by
  have hi := write_hoare (separator : Fin (a+4)) (fun _ => blank) 0
  have he : Function.update (fun _ : ℤ => (blank : Fin (a+4))) 0 separator = BinaryDescriptorStack.empty := by
    funext z; simp [BinaryDescriptorStack.empty,Function.update_apply]
  rw [he] at hi
  have hw := writes_hoare ((bits n).map (bitSymbol (a := a))) BinaryDescriptorStack.empty 1
  simp only [List.length_map] at hw
  have hr := Rewind.rewind_hoare (separator : Fin (a+4)) (BinaryDescriptorStack.descriptor (bits n)) (1+(bits n).length) ((bits n).length+1)
    (by
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [Nat.cast_zero,sub_zero,BinaryDescriptorStack.descriptor,putWord_outside _ _ _ _ (Or.inr (by simp))]
        simp [BinaryDescriptorStack.empty,show (1 : ℤ)+(bits n).length ≠ 0 by omega,blank,separator,Fin.ext_iff]
      · have hm := ReturnOrigin.putWord_mem BinaryDescriptorStack.empty 1 ((bits n).map (bitSymbol (a := a))) (1+(bits n).length-j) (by simp; omega)
        obtain ⟨b,_,he⟩ := List.mem_map.mp hm
        change putWord BinaryDescriptorStack.empty 1 ((bits n).map bitSymbol) (1+(bits n).length-j) ≠ separator
        rw [← he]
        cases b <;> simp [bitSymbol,separator,Fin.ext_iff])
    (by
      have hz : (1 : ℤ)+(bits n).length-((bits n).length+1 : ℕ) = 0 := by omega
      rw [hz,BinaryDescriptorStack.descriptor,putWord_outside _ _ _ _ (Or.inl (by omega))]
      rfl)
  have hz : (1 : ℤ)+(bits n).length-((bits n).length+1 : ℕ) = 0 := by omega
  rw [hz] at hr
  exact (((hi.seq hw).seq hr).seq (StepRight.step_hoare (BinaryDescriptorStack.descriptor (bits n)) 0)).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end IntegerMultBounds.Machine.RecursiveChildQuotientsConstant
