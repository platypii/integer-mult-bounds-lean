import IntegerMultBounds.Machine.PlacementBank
import IntegerMultBounds.Machine.BinaryCurrentAddressInit
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Initialize live counter57 and raw address43 from the physically derived
complete-width header22 using clean clock45; erase header22 afterwards.
No counter/address word or width header59 is prepared externally. -/
namespace IntegerMultBounds.Machine.UnitPhaseAddressInitAt
noncomputable section
open SharedPlacementAlphabet (setTape)
open CountedLoopReuseAlphabet (binary)
abbrev count := 60

def slots : Fin 4 → Fin count := ![57,43,45,22]
theorem injective : Function.Injective slots := by decide

def placement : Fin (4+56) ≃ Fin count := InjectivePlacement.placement slots injective (by decide)
def initializer := Placement.placed (BinaryCurrentAddressInit.program (a := 2)) placement
def erase := BinaryDescriptorCleanupList.oneProgram (a := 2) (22 : Fin count)
def program := seq initializer erase
def initialized (v : Tapes count 2) (bs : List Bool) (W : ℕ) :=
  Placement.replace placement v (BinaryCurrentAddressInit.output bs W)
def output (v : Tapes count 2) (bs : List Bool) (W : ℕ) :=
  setTape (initialized v bs W) 22 (fun _ => blank) 0

private theorem slot_head (v : Tapes count 2) (b : Tapes 4 2) (i : Fin 4) :
    (Placement.replace placement v b).head (slots i)=b.head i :=
  InjectivePlacement.replace_head_slot slots injective (by decide) v b i
private theorem slot_tape (v : Tapes count 2) (b : Tapes 4 2) (i : Fin 4) :
    (Placement.replace placement v b).tape (slots i)=b.tape i :=
  InjectivePlacement.replace_tape_slot slots injective (by decide) v b i

theorem output_eq (v : Tapes count 2) (bs : List Bool) (W : ℕ) :
    output v bs W=setTape (setTape (setTape (setTape v 57
      (binary (BinaryAddressTableData.row W 0)) 1) 43
        (SelectedSourceBitsScan.word (BinaryAddressTableData.row W 0)) 0) 45 (fun _ => blank) 0)
          22 (fun _ => blank) 0 := by
  unfold output
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp only [setTape,Function.update_apply]
  all_goals first
    | rfl
    | exact slot_head v (BinaryCurrentAddressInit.output bs W) 0
    | exact slot_head v (BinaryCurrentAddressInit.output bs W) 1
    | exact slot_head v (BinaryCurrentAddressInit.output bs W) 2
    | exact slot_tape v (BinaryCurrentAddressInit.output bs W) 0
    | exact slot_tape v (BinaryCurrentAddressInit.output bs W) 1
    | exact slot_tape v (BinaryCurrentAddressInit.output bs W) 2
    | exact InjectivePlacement.replace_head_other slots injective (by decide) v
        (BinaryCurrentAddressInit.output bs W) _ (by intro j; fin_cases j <;> decide)
    | exact InjectivePlacement.replace_tape_other slots injective (by decide) v
        (BinaryCurrentAddressInit.output bs W) _ (by intro j; fin_cases j <;> decide)

theorem runs (v : Tapes count 2) (bs : List Bool) (W : ℕ) (hw : Counter.value bs=W)
    (hc : GrowingCounterData.Canonical bs)
    (hh : v.tape 22=binary bs ∧ v.head 22=1)
    (hm : v.tape 57=(fun _ => blank) ∧ v.head 57=0)
    (ha : v.tape 43=(fun _ => blank) ∧ v.head 43=0)
    (hk : v.tape 45=(fun _ => blank) ∧ v.head 45=0) :
    HoareTime program (fun z => z=v) (fun z => z=output v bs W) (65*(W+1)+2*bs.length+5) := by
  have hactive : Placement.active placement v=BinaryCurrentAddressInit.input bs := by
    rw [placement,InjectivePlacement.active_bank]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals first | exact hm.1 | exact hm.2 | exact ha.1 | exact ha.2 | exact hk.1 | exact hk.2 | exact hh.1 | exact hh.2
  have h := Placement.hoare_at (BinaryCurrentAddressInit.runs (a := 2) bs W hw hc) placement v hactive
  have h0 : HoareTime initializer (fun z => z=v) (fun z => z=initialized v bs W) (65*(W+1)) := by
    apply h.consequence (fun _ h => h) _ le_rfl
    rintro z ⟨small,rfl,rfl⟩
    rfl
  have hheader : (initialized v bs W).tape 22=BinaryDescriptorStack.descriptor bs := by
    have h := slot_tape v (BinaryCurrentAddressInit.output bs W) 3
    change (initialized v bs W).tape 22=binary bs at h
    rw [h,BinaryDescriptorStackRoundtrip.descriptor_encoded]
    exact CountedLoopReuseAlphabet.encoding_binary bs |>.symm
  have hhead : (initialized v bs W).head 22=1 := slot_head v (BinaryCurrentAddressInit.output bs W) 3
  have h1 := BinaryDescriptorCleanupList.one_hoare (22 : Fin count) (initialized v bs W) bs hheader hhead
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem counter (v : Tapes count 2) (bs : List Bool) (W : ℕ) :
    (output v bs W).tape 57=binary (BinaryAddressTableData.row W 0) ∧ (output v bs W).head 57=1 := by
  have ht := slot_tape v (BinaryCurrentAddressInit.output bs W) 0
  have hh := slot_head v (BinaryCurrentAddressInit.output bs W) 0
  simpa [output,initialized,setTape,slots,BinaryCurrentAddressInit.output,BinaryCurrentAddressInit.bank] using And.intro ht hh

theorem address (v : Tapes count 2) (bs : List Bool) (W : ℕ) :
    (output v bs W).tape 43=SelectedSourceBitsScan.word (BinaryAddressTableData.row W 0) ∧
      (output v bs W).head 43=0 := by
  have ht := slot_tape v (BinaryCurrentAddressInit.output bs W) 1
  have hh := slot_head v (BinaryCurrentAddressInit.output bs W) 1
  simpa [output,initialized,setTape,slots,BinaryCurrentAddressInit.output,BinaryCurrentAddressInit.bank] using And.intro ht hh

end
end IntegerMultBounds.Machine.UnitPhaseAddressInitAt
