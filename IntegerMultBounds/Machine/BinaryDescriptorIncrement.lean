import IntegerMultBounds.Machine.BinaryDescriptorStackRoundtrip
import IntegerMultBounds.Machine.GrowingCounter

/-! A reusable incrementer for marked binary descriptors on the unchanged
finite alphabet. Carry propagation and return to the marker are charged. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorIncrement
variable {q : ℕ}

def program : Program 1 3 q := RadixToBinary.incrementProgram q

def bank (bs : List Bool) : Tapes 1 q :=
  ⟨fun _ => 1, fun _ => BinaryDescriptorStack.descriptor bs⟩

theorem bank_state (bs : List Bool) : bank (q := q) bs = RadixToBinary.binaryState q bs := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    exact BinaryDescriptorStackRoundtrip.descriptor_encoded bs

theorem increment_hoare (bs : List Bool) :
    HoareTime (program (q := q)) (fun v => v = bank bs)
      (fun v => v = bank (GrowingCounterData.increment bs))
      (2 * GrowingCounterData.carrySteps bs) := by
  have h := GrowingCounter.increment_hoare CountedCopyReuse.empty bs
    (by simp [CountedCopyReuse.empty])
    (by simp [CountedCopyReuse.empty,show (1 : ℤ)+bs.length ≠ 0 by omega])
  have hm := Alphabet.map_hoare (RadixToBinary.binaryEncoding (q := q)) h
  rw [bank_state,bank_state]
  apply hm.consequence _ _ le_rfl
  · intro v hv
    exact ⟨_,rfl,hv⟩
  · rintro v ⟨w,rfl,hv⟩
    exact hv

theorem increment_linear (bs : List Bool) :
    HoareTime (program (q := q)) (fun v => v = bank bs)
      (fun v => v = bank (GrowingCounterData.increment bs)) (2*(bs.length+1)) :=
  (increment_hoare bs).consequence (fun _ h => h) (fun _ h => h)
    (Nat.mul_le_mul_left 2 (GrowingCounterData.carrySteps_bounds bs).2)

theorem value (bs : List Bool) :
    Counter.value (GrowingCounterData.increment bs) = Counter.value bs+1 :=
  GrowingCounterData.increment_value bs

theorem canonical (bs : List Bool) (h : GrowingCounterData.Canonical bs) :
    GrowingCounterData.Canonical (GrowingCounterData.increment bs) :=
  GrowingCounterData.increment_canonical bs h

end IntegerMultBounds.Machine.BinaryDescriptorIncrement
