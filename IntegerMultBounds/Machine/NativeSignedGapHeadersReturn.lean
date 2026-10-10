import IntegerMultBounds.Machine.NativeSignedGapReturn
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCore
import IntegerMultBounds.Machine.PlacedDescriptorConstruction

/-! Precision return from two physical retained denominator descriptors. The
fixed machine subtracts current minus target into a blank private gap tape,
executes one native stream return, then erases the synthesized gap descriptor.
These are true denominator inputs, not the controller's geometric exponent k
or the width baseline. Propagating them through recursive execution is separate. -/
namespace IntegerMultBounds.Machine.NativeSignedGapHeadersReturn
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
open NativeSignedReturnStream (volume)
open RadixSignedShiftRight (Word)

def exponents (current target : ℕ) : Tapes 2 2 :=
  ⟨fun _ => 1,![RadixZeroFill.encodedBinary (bits current),RadixZeroFill.encodedBinary (bits target)]⟩
def prepared (ws : List Word) (current target : ℕ) (ls : List Bool) :=
  (CountedLoopHeaderClean.bank (NativeSignedGapReturn.input ws (bits (current-target)) ls)).append (exponents current target)
def input (ws : List Word) (current target : ℕ) (ls : List Bool) :=
  setTape (prepared ws current target ls) (4:Fin 10) (fun _ => blank) 0
def returned (ws : List Word) (current target : ℕ) (ls : List Bool) :=
  (CountedLoopHeaderClean.bank (NativeSignedGapReturn.output ws (current-target) (bits (current-target)) ls)).append (exponents current target)
def output (ws : List Word) (current target : ℕ) (ls : List Bool) :=
  setTape (returned ws current target ls) (4:Fin 10) (fun _ => blank) 0

def focus : Fin 3 → Fin 10 := ![8,9,4]
theorem focus_injective : Function.Injective focus := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [focus]
def placement : Fin (3+7) ≃ Fin 10 := InjectivePlacement.placement focus focus_injective rfl
def synthesize := Placement.placed (BinaryDescriptorDifference.program (a:=2)) placement
def returnProgram := extend NativeSignedGapReturn.program 2
def cleanup := BinaryDescriptorCleanupList.oneProgram (a:=2) (4:Fin 10)
def program := seq (seq synthesize returnProgram) cleanup

def cost (ws : List Word) (current target : ℕ) :=
  6*max (bits current).length (bits target).length+21+
    (129*volume ws+324)+(2*(bits (current-target)).length+4)+2

private theorem active_input (ws : List Word) (current target : ℕ) (ls : List Bool) :
    Placement.active placement (input ws current target ls)=
      BinaryDescriptorDifference.input (a:=2) (bits current) (bits target) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [placement,InjectivePlacement.active_slot,focus,input,setTape]
  all_goals fin_cases i
  all_goals dsimp only [BinaryDescriptorDifference.input,BinaryDescriptorDifference.bank]
  all_goals simp [prepared,exponents,Tapes.append,Fin.addCases]
  all_goals exact CompactGadgetReservationHeadersCore.encoded_binary _

private theorem installed (ws : List Word) (current target : ℕ) (ls : List Bool) :
    setTape (input ws current target ls) (4:Fin 10)
      (RadixZeroFill.encodedBinary (bits (current-target))) 1=prepared ws current target ls := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem synthesize_runs (ws : List Word) (current target : ℕ) (hle : target≤current) (ls : List Bool) :
    HoareTime synthesize (fun v => v=input ws current target ls)
      (fun v => v=prepared ws current target ls)
      (6*max (bits current).length (bits target).length+21) := by
  have h := Placement.hoare_at (BinaryDescriptorDifference.difference_hoare (a:=2)
    (bits current) (bits target) (by simpa only [RecursiveChildQuotientsConstant.bits_value] using hle))
    placement (input ws current target ls) (active_input ws current target ls)
  have he : BinaryDescriptorDifference.output (a:=2) (bits current) (bits target) (bits (current-target))=
      setTape (BinaryDescriptorDifference.input (bits current) (bits target)) (2:Fin 3)
        (RadixZeroFill.encodedBinary (bits (current-target))) 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals dsimp only [BinaryDescriptorDifference.output,BinaryDescriptorDifference.input,
      BinaryDescriptorDifference.bank,setTape]
    all_goals simp [BinaryDescriptorStackRoundtrip.descriptor_encoded]
  simp only [RecursiveChildQuotientsConstant.bits_value] at h
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [he,←active_input ws current target ls,PlacedDescriptorConstruction.replace_setTape]
  simp only [placement,InjectivePlacement.active_slot,focus,Matrix.cons_val_two]
  exact installed ws current target ls

attribute [local irreducible] synthesize returnProgram cleanup NativeSignedGapReturn.program

theorem runs (ws : List Word) (current target : ℕ) (hle : target≤current)
    (hd : ∀ w∈ws,current-target≤w.length) (hn : ws≠[]) (ls : List Bool)
    (hlen : Counter.value ls=volume ws) (hl : GrowingCounterData.Canonical ls) :
    HoareTime program (fun v => v=input ws current target ls)
      (fun v => v=output ws current target ls) (cost ws current target) := by
  have h0 := synthesize_runs ws current target hle ls
  have h1 := hoare_extend_eq (NativeSignedGapReturn.runs_linear ws (current-target) hd hn
    (bits (current-target)) ls (RecursiveChildQuotientsConstant.bits_value _) hlen
    (RecursiveChildQuotientsConstant.bits_canonical _) hl) (exponents current target)
  have h2 := BinaryDescriptorCleanupList.one_hoare (4:Fin 10) (returned ws current target ls)
    (bits (current-target))
    (by change RadixZeroFill.encodedBinary _=_; rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]) (by rfl)
  have h1' : HoareTime returnProgram (fun v => v=prepared ws current target ls)
      (fun v => v=returned ws current target ls) (129*volume ws+324) := by
    simpa only [returnProgram,prepared,returned] using h1
  have h2' : HoareTime cleanup (fun v => v=returned ws current target ls)
      (fun v => v=output ws current target ls) (2*(bits (current-target)).length+4) := by
    simpa only [cleanup,output] using h2
  unfold program
  have h01 := h0.seq h1'
  have h012 := h01.seq h2'
  apply h012.consequence (fun _ h => h) (fun _ h => h)
  unfold cost
  omega

/-- The exponent descriptors are paid as binary words, not subtraction oracles. -/
theorem cost_le (ws : List Word) (current target : ℕ) (hle : target≤current) :
    cost ws current target≤129*volume ws+8*current+359 := by
  have hw (n : ℕ) : (bits n).length≤n+1 := by
    have hh := GrowingCounterData.canonical_width (bits n) (RecursiveChildQuotientsConstant.bits_canonical n)
    rw [RecursiveChildQuotientsConstant.bits_value] at hh
    exact hh.trans (Nat.add_le_add_right (Nat.log2_le_self n) 1)
  have hc := hw current
  have ht := hw target
  have hd := hw (current-target)
  unfold cost
  omega

theorem endpoint (ws : List Word) (current target : ℕ) (ls : List Bool) :
    let v := output ws current target ls
    v.head 0=0 ∧ v.tape 0=NativeSignedGapReturn.word (ws.map (NativeSignedGapScan.result (current-target))) ∧
    (∀ i:Fin 10,i∈[1,2,3,4,6,7] → v.head i=0 ∧ v.tape i=(fun _ => blank)) ∧
    v.head 5=1 ∧ v.tape 5=RadixZeroFill.encodedBinary ls ∧
    v.head 8=1 ∧ v.tape 8=RadixZeroFill.encodedBinary (bits current) ∧
    v.head 9=1 ∧ v.tape 9=RadixZeroFill.encodedBinary (bits target) := by
  dsimp only
  refine ⟨rfl,rfl,?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
  intro i hi
  fin_cases i <;> simp at hi ⊢
  all_goals exact ⟨rfl,rfl⟩

/-- Placement consumes original physical denominator tapes and frames the
whole complementary caller bank, including recursive stacks. -/
theorem runs_at {u t : ℕ} (e : Fin (10+u) ≃ Fin t) (v : Tapes t 2)
    (ws : List Word) (current target : ℕ) (hle : target≤current)
    (hd : ∀ w∈ws,current-target≤w.length) (hn : ws≠[]) (ls : List Bool)
    (hlen : Counter.value ls=volume ws) (hl : GrowingCounterData.Canonical ls)
    (ha : Placement.active e v=input ws current target ls) :
    HoareTime (Placement.placed program e) (fun w => w=v)
      (fun w => w=Placement.replace e v (output ws current target ls)) (cost ws current target) := by
  apply (Placement.hoare_at (runs ws current target hle hd hn ls hlen hl) e v ha).consequence
    (fun _ h => h) _ le_rfl
  rintro w ⟨small,rfl,rfl⟩
  rfl

end
end IntegerMultBounds.Machine.NativeSignedGapHeadersReturn
