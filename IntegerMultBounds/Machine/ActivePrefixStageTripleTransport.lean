import IntegerMultBounds.Machine.SymbolTripleArray
import IntegerMultBounds.Machine.ActivePrefixStageRuntimeSelected

/-! The actual all-width stage endpoint transports literal native coefficient
codes, with arbitrary payload spectators. Each observed output bit is the
result of the proved physical runtime stage, not an assumed record permutation.
Conversion placement, cleanup and whole-stage assembly remain separate. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageTripleTransport
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageFullSelected (geometry Address)
open ActivePrefixDirtyControlGlobalSwap (index)
open ActivePrefixStageRuntimeSelected (destination)
open ActiveRepairLayoutRecordsData (Array)
variable {s : Shape} {B K : ℕ}

def equiv (d : Inputs s) : Address d ≃ Fin (d.rows*s.recordWidth) :=
  CompactActiveTargetLayout.indexEquiv s ((geometry d).n*(geometry d).b)
    ((geometry d).n*(geometry d).q) (geometry d).before (geometry d).after d.rows
    (geometry d).compactFits (geometry d).activeSize

def base (d : Inputs s) (i : Address d) : Address d :=
  {i with payload:=⟨0,by have := d.hrecord; omega⟩}

def encodedArray (d : Inputs s) (h : s.payload=B*3+K)
    (xs : Address d → Fin B → Fin 6) (tail : Address d → Fin K → Bool) : Array s d.rows :=
  fun k => let i := (equiv d).symm k
    SymbolTripleArray.record (xs (base d i)) (tail (base d i)) (Fin.cast h i.payload)

theorem encoded_entry (d : Inputs s) (h : s.payload=B*3+K)
    (xs : Address d → Fin B → Fin 6) (tail : Address d → Fin K → Bool) (i : Address d) :
    encodedArray d h xs tail (index s (geometry d) i)=
      SymbolTripleArray.record (xs (base d i)) (tail (base d i)) (Fin.cast h i.payload) := by
  change SymbolTripleArray.record (xs (base d ((equiv d).symm ((equiv d) i))))
    (tail (base d ((equiv d).symm ((equiv d) i))))
    (Fin.cast h ((equiv d).symm ((equiv d) i)).payload)=_
  rw [Equiv.symm_apply_apply]

def symbolCell (d : Inputs s) (h : s.payload=B*3+K) (i : Address d)
    (j : Fin B) (b : Fin 3) : Address d :=
  {i with payload:=Fin.cast h.symm (Fin.castAdd K (finProdFinEquiv (j,b)))}

def spectatorCell (d : Inputs s) (h : s.payload=B*3+K) (i : Address d)
    (j : Fin K) : Address d :=
  {i with payload:=Fin.cast h.symm (Fin.natAdd (B*3) j)}

/-- All code bits arrive in one contiguous destination payload, since the
actual runtime address action is independent of the payload coordinate. -/
theorem destination_payload (d : Inputs s) (i : Address d) (r : Fin s.payload) :
    destination d {i with payload:=r}={destination d i with payload:=r} := by
  unfold destination
  split_ifs with hw
  · unfold ActivePrefixStageDispatchSelected.destination
    split_ifs <;> rfl
  · unfold ActivePrefixStageRuntimeSelected.singletonDestination
    split_ifs <;> rfl

theorem symbolCell_destination (d : Inputs s) (h : s.payload=B*3+K)
    (i : Address d) (j : Fin B) (b : Fin 3) :
    destination d (symbolCell d h i j b)=symbolCell d h (destination d i) j b :=
  destination_payload d i _

theorem spectatorCell_destination (d : Inputs s) (h : s.payload=B*3+K)
    (i : Address d) (j : Fin K) :
    destination d (spectatorCell d h i j)=spectatorCell d h (destination d i) j :=
  destination_payload d i _

theorem stage_symbol_bit (d : Inputs s) (h : s.payload=B*3+K)
    (xs : Address d → Fin B → Fin 6) (tail : Address d → Fin K → Bool)
    (i : Address d) (j : Fin B) (b : Fin 3) :
    ActivePrefixStageRuntimeData.result d (encodedArray d h xs tail)
      (index s (geometry d) (destination d (symbolCell d h i j b)))=
      SymbolTripleEncode.bit (xs (base d i) j) b := by
  rw [ActivePrefixStageRuntimeSelected.entry,encoded_entry]
  simp only [symbolCell,base,Fin.cast_cast,Fin.cast_eq_self]
  rw [SymbolTripleArray.record_symbol,SymbolTripleArray.triple_at]

/-- Decoding the three actual transported result bits recovers the original
native symbol at its stage destination, for every positive stage width. -/
theorem stage_symbol (d : Inputs s) (h : s.payload=B*3+K)
    (xs : Address d → Fin B → Fin 6) (tail : Address d → Fin K → Bool)
    (i : Address d) (j : Fin B) :
    let y := ActivePrefixStageRuntimeData.result d (encodedArray d h xs tail)
    SymbolTripleDecode.value
      (y (index s (geometry d) (symbolCell d h (destination d i) j 0)))
      (y (index s (geometry d) (symbolCell d h (destination d i) j 1)))
      (y (index s (geometry d) (symbolCell d h (destination d i) j 2)))=xs (base d i) j := by
  dsimp only
  rw [←symbolCell_destination,←symbolCell_destination,←symbolCell_destination,
    stage_symbol_bit,stage_symbol_bit,stage_symbol_bit,SymbolTripleDecode.value_code]

theorem stage_spectator (d : Inputs s) (h : s.payload=B*3+K)
    (xs : Address d → Fin B → Fin 6) (tail : Address d → Fin K → Bool)
    (i : Address d) (j : Fin K) :
    ActivePrefixStageRuntimeData.result d (encodedArray d h xs tail)
      (index s (geometry d) (spectatorCell d h (destination d i) j))=tail (base d i) j := by
  rw [←spectatorCell_destination,ActivePrefixStageRuntimeSelected.entry,encoded_entry]
  simp only [spectatorCell,base,Fin.cast_cast,Fin.cast_eq_self]
  exact SymbolTripleArray.record_spectator _ _ j

end
end IntegerMultBounds.Machine.ActivePrefixStageTripleTransport
