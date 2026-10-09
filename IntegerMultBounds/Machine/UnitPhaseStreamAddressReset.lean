import IntegerMultBounds.Machine.CompactZeroUnitPhase

/-! Physically erase the final live counter and raw address after a whole
phase stream. A preserved-address scan copies into clean clock45, so both
raw words can be erased backwards with genuine head returns. Streams and
all original/controller tapes are retained. -/
namespace IntegerMultBounds.Machine.UnitPhaseStreamAddressReset
noncomputable section
open SharedPlacementAlphabet (setTape)
open CountedLoopReuseAlphabet (binary)

def copy := TwoTapeAt.program (Copy.program (blank : Fin 6) false) (43 : Fin 60) 45 (by decide)
def eraseAddress := Placement.placed (RawBitWordReset.program (a := 2)) (FiniteReturnStackAt.placement (43 : Fin 60))
def eraseClock := Placement.placed (RawBitWordReset.program (a := 2)) (FiniteReturnStackAt.placement (45 : Fin 60))
def eraseCounter := BinaryDescriptorCleanupList.oneProgram (a := 2) (57 : Fin 60)
def program := seq (seq (seq copy eraseAddress) eraseClock) eraseCounter
def copied (v : Tapes 60 2) (addr : List Bool) := TwoTapeAt.result v 43 45
  (SelectedSourceBitsScan.word addr) (SelectedSourceBitsScan.word addr) addr.length addr.length
def afterAddress (v : Tapes 60 2) (addr : List Bool) := setTape (copied v addr) 43 (fun _ => blank) 0
def afterClock (v : Tapes 60 2) (addr : List Bool) := setTape (afterAddress v addr) 45 (fun _ => blank) 0
def output (v : Tapes 60 2) (addr : List Bool) := setTape (afterClock v addr) 57 (fun _ => blank) 0

theorem output_eq (v : Tapes 60 2) (addr : List Bool) :
    output v addr=setTape (setTape (setTape v 43 (fun _ => blank) 0) 45 (fun _ => blank) 0)
      57 (fun _ => blank) 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem raw_clears (v : Tapes 60 2) (i : Fin 60) (addr : List Bool)
    (ht : v.tape i=SelectedSourceBitsScan.word addr) (hh : v.head i=addr.length) :
    HoareTime (Placement.placed (RawBitWordReset.program (a := 2)) (FiniteReturnStackAt.placement i))
      (fun z => z=v) (fun z => z=setTape v i (fun _ => blank) 0) (addr.length+2) := by
  have h := Placement.hoare_at (RawBitWordReset.runs (a := 2) addr) (FiniteReturnStackAt.placement i) v
    (by rw [FiniteReturnStackAt.active_bank,ht,hh]; rfl)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

theorem runs (v : Tapes 60 2) (addr counter : List Bool)
    (ha : v.tape 43=SelectedSourceBitsScan.word addr ∧ v.head 43=0)
    (hk : v.tape 45=(fun _ => blank) ∧ v.head 45=0)
    (hc : v.tape 57=binary counter ∧ v.head 57=1) :
    HoareTime program (fun z => z=v) (fun z => z=output v addr) (3*addr.length+2*counter.length+11) := by
  have hs := Copy.copy_hoare (blank : Fin 6) false (fun _ => blank) (fun _ => blank) 0 0
    (addr.map bitSymbol) (ReturnOrigin.bits_nonblank addr)
    (by rfl)
  have hr : (Copy.retained false : Fin 6 → Fin 6)=id := rfl
  simp only [hr,List.map_id,List.length_map,zero_add] at hs
  change HoareTime _ (fun z => z=Copy.tapes (SelectedSourceBitsScan.word addr) (fun _ => blank) 0 0)
    (fun z => z=Copy.tapes (SelectedSourceBitsScan.word addr) (SelectedSourceBitsScan.word addr) addr.length addr.length)
    addr.length at hs
  have h0 := TwoTapeAt.runs (Copy.program (blank : Fin 6) false) (43 : Fin 60) 45 (by decide)
    v _ _ _ _ _ _ _ _ ha hk hs
  have h1 := raw_clears (copied v addr) 43 addr (by rfl) (by rfl)
  have h2 := raw_clears (afterAddress v addr) 45 addr (by rfl) (by rfl)
  have h3 := BinaryDescriptorCleanupList.one_hoare (57 : Fin 60) (afterClock v addr) counter
    (by change v.tape 57=BinaryDescriptorStack.descriptor counter
        rw [hc.1,BinaryDescriptorStackRoundtrip.descriptor_encoded]
        exact CountedLoopReuseAlphabet.encoding_binary counter |>.symm)
    (by exact hc.2)
  exact (((h0.seq h1).seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.UnitPhaseStreamAddressReset
