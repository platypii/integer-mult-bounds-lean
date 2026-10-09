import IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalCoordinates
import IntegerMultBounds.Machine.BinaryPackedLatePermutation

/-! The physical compact source offsets are the exact load/unload arithmetic
of the packed late permutation, including modular carry and borrow. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlSourcePacked
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes
open ActivePrefixLayoutBack (afterControls)
open ActivePrefixDirtyControlSourceSemantics (selectedCompact)
open ActivePrefixDirtyControlGlobalCoordinates
open ActivePrefixDirtyControlGlobalSequence
open ActivePrefixDirtyControlGlobalConjugation (uDestination)

variable (s : Shape) (p : Parameters s) (offset : ℕ) {rows : ℕ}

theorem controls (x : Address s p rows) : ActivePrefixDirtyControlLayoutRows.controls s p x=
    BinaryPackedLateData.controls p.b p.n x.u := rfl

def packed (b : ℕ) (X : List Bool) := (X.map (fun z => z::List.replicate (b-1) false)).flatten

theorem gather_word (b : ℕ) (hb : 1≤b) (X : List Bool) :
    Gather.gather (fun _ z => z) (CountedPackedControlLoadHeaders.shape b hb) X X X.length=packed b X := by
  rw [Compact.PowerTwo.gather_flatten]
  unfold packed
  conv_rhs => rw [Compact.PowerTwo.list_eq_range X,List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i _
  simp [Gather.digitWord,CountedPackedControlLoadHeaders.shape,Gather.field]

theorem packed_value (b : ℕ) (hb : 1≤b) (X : List Bool) :
    (Counter.value (packed b X) : ℤ)=Compact.Radix.pack ((2 : ℤ)^b) (X.map Compact.PowerTwo.ctrl) := by
  rw [←gather_word b hb X]
  exact CountedPackedControlLoadRun.controlWord_value b hb X

theorem packed_length (b : ℕ) (hb : 1≤b) (X : List Bool) : (packed b X).length=X.length*b := by
  rw [←gather_word b hb X,Gather.gather_length]
  rfl

theorem load_eq (b n : ℕ) (hb : 1≤b) (X : List Bool) (hX : X.length=n) (u : BinaryPackedEarlyData.Temp b n) :
    BinaryPackedEarlyData.add u (Counter.value (packed b X))=BinaryPackedLateData.load b n hb X hX u := by
  apply Fin.ext
  have h := BinaryPackedLateData.load_value b n hb X hX u
  have h' := BinaryPackedEarlyData.add_value u (Counter.value (packed b X))
  rw [packed_value b hb X] at h'
  rw [←pow_mul,show b*n=n*b from Nat.mul_comm b n] at h
  exact_mod_cast h'.trans h.symm

theorem unload_eq (b n : ℕ) (hb : 1≤b) (X : List Bool) (hX : X.length=n) (u : BinaryPackedEarlyData.Temp b n) :
    BinaryPackedEarlyData.add u (Counter.value (TwosComplement.negWord (packed b X)))=
      BinaryPackedLateData.unload b n hb X hX u := by
  apply Fin.ext
  have h := BinaryPackedLateData.unload_value b n hb X hX u
  have h' := BinaryPackedEarlyData.add_value u (Counter.value (TwosComplement.negWord (packed b X)))
  rw [BinaryParityXorOffsetValue.negWord_value,packed_length b hb X,hX,packed_value b hb X] at h'
  rw [←pow_mul,show b*n=n*b from Nat.mul_comm b n] at h
  have he (a z M : ℤ) : (a+(-z)%M)%M=(a-z)%M := by
    rw [Int.add_emod,Int.emod_emod,←Int.add_emod]
    rfl
  rw [he] at h'
  exact_mod_cast h'.trans h.symm

theorem source_destination (hfit : offset+p.f*p.q≤p.after) (x : Address s p rows) :
    uDestination s p (sourceOffsets s p rows offset hfit) x={ x with
      u := BinaryPackedLateData.load p.b p.n p.hb (afterControls s p x offset)
        (SelectedSourceBitsData.selected_length _ _ _ _) x.u } := by
  rw [ActivePrefixDirtyControlGlobalCoordinates.source_destination]
  unfold selectedCompact
  rw [show ((afterControls s p x offset).map (fun z => z::List.replicate (p.b-1) false)).flatten=
    packed p.b (afterControls s p x offset) from rfl,load_eq p.b p.n p.hb (afterControls s p x offset) (SelectedSourceBitsData.selected_length _ _ _ _) x.u]

theorem unload_destination (hfit : offset+p.f*p.q≤p.after) (x : Address s p rows) :
    uDestination s p (unloadOffsets s p rows offset hfit) x={ x with
      u := BinaryPackedLateData.unload p.b p.n p.hb (afterControls s p x offset)
        (SelectedSourceBitsData.selected_length _ _ _ _) x.u } := by
  rw [ActivePrefixDirtyControlGlobalCoordinates.unload_destination]
  unfold selectedCompact
  rw [show ((afterControls s p x offset).map (fun z => z::List.replicate (p.b-1) false)).flatten=
    packed p.b (afterControls s p x offset) from rfl,unload_eq p.b p.n p.hb (afterControls s p x offset) (SelectedSourceBitsData.selected_length _ _ _ _) x.u]

end IntegerMultBounds.Machine.ActivePrefixDirtyControlSourcePacked
