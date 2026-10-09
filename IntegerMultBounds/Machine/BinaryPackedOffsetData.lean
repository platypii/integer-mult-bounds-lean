import IntegerMultBounds.Machine.BinaryPackedFieldSwap
import IntegerMultBounds.Machine.PackedOffsetPayloadArray

/-! Literal coordinate semantics for swapping a dirty front field to the back,
rotating it using packed source words, then swapping it back. -/
namespace IntegerMultBounds.Machine.BinaryPackedOffsetData
noncomputable section
open RadixRangePadding (volume index transpose)
open RecursiveInterchangeRows (pack pack_val)

abbrev rows (P w G : ℕ) := P*2^w*G

theorem size (P w G B : ℕ) : volume P (2^w) G B = rows P w G*(2^w*B) := by
  unfold volume rows
  ring

def rowIndex {P N G : ℕ} (p : Fin P) (h : Fin N) (g : Fin G) : Fin (P*N*G) := pack (pack p h) g

def asFiber {P w G B : ℕ} (x : Fin (volume P (2^w) G B) → Bool) :
    Fin (rows P w G*(2^w*B)) → Bool := fun i => x (Fin.cast (size P w G B).symm i)

def fromFiber {P w G B : ℕ} (x : Fin (rows P w G*(2^w*B)) → Bool) :
    Fin (volume P (2^w) G B) → Bool := fun i => x (Fin.cast (size P w G B) i)

theorem asFiber_fromFiber {P w G B : ℕ} (x : Fin (rows P w G*(2^w*B)) → Bool) :
    asFiber (fromFiber x) = x := by
  funext i; rfl

theorem fromFiber_asFiber {P w G B : ℕ} (x : Fin (volume P (2^w) G B) → Bool) :
    fromFiber (asFiber x) = x := by
  funext i; rfl

theorem fiber_index {P w G B : ℕ} (p : Fin P) (h d : Fin (2^w)) (g : Fin G) (j : Fin B) :
    Fin.cast (size P w G B) (index p h g d j) = FiberLayoutData.index (rowIndex p h g) d j := by
  apply Fin.ext
  change (index p h g d j).val = (FiberLayoutData.index (rowIndex p h g) d j).val
  simp only [index,pack_val,FiberLayoutData.index_val,rowIndex]
  ring

theorem word_cast {m n : ℕ} (h : m=n) (x : Fin m → Bool) :
    List.ofFn (fun i : Fin n => bitSymbol (x (Fin.cast h.symm i))) =
      List.ofFn (fun i => (bitSymbol (x i) : Fin (Networks.Shared50ModularControl.prime+4))) := by
  subst n
  rfl

def back (V : List Bool) (P w G B : ℕ) (x : Fin (volume P (2^w) G B) → Bool) :=
  fromFiber (PackedOffsetPayloadArray.array V w (rows P w G) B (asFiber x))

def result (V : List Bool) (P w G B : ℕ) (x : Fin (volume P (2^w) G B) → Bool) :=
  transpose (back V P w G B (transpose x))

/-- Offset is read from the source field indexed by the original dirty back
coordinate. The entire back coordinate and arbitrary suffix bit survive. -/
theorem result_entry (V : List Bool) (P w G B : ℕ) (hV : V.length=rows P w G*w)
    (x : Fin (volume P (2^w) G B) → Bool)
    (p : Fin P) (front back : Fin (2^w)) (g : Fin G) (j : Fin B) :
    result V P w G B x (index p
      ⟨(front.val+PackedOffsetPayloadValue.offset V w (rowIndex p back g).val)%2^w,
        Nat.mod_lt _ (by positivity)⟩ g back j) = x (index p front g back j) := by
  rw [result,RadixRangePadding.transpose_entry]
  change PackedOffsetPayloadArray.array V w (rows P w G) B (asFiber (transpose x))
    (Fin.cast (size P w G B) (index p back g _ j)) = _
  rw [fiber_index,PackedOffsetPayloadArray.array_entry V w (rows P w G) B hV]
  change transpose x (Fin.cast (size P w G B).symm (FiberLayoutData.index (rowIndex p back g) front j)) = _
  rw [← fiber_index]
  exact RadixRangePadding.transpose_entry x p back g front j

end
end IntegerMultBounds.Machine.BinaryPackedOffsetData
