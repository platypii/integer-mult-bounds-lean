import IntegerMultBounds.Machine.CountedRepairScanMetadataRun

/-! Physical sentinel initialization for the fixed fourteen-tape scan bank. -/
namespace IntegerMultBounds.Machine.CountedRepairScanSeed
noncomputable section

def markedSlot (i : Fin 14) : Prop := i.val≤7 ∨ i=12
instance (i : Fin 14) : Decidable (markedSlot i) := inferInstanceAs (Decidable (i.val≤7 ∨ i=12))

def input (src : ℤ → Fin 5) : Tapes 14 1 :=
  ⟨fun _ => 0,fun i => if i=11 then src else fun _ => blank⟩

def middle (src : ℤ → Fin 5) : Tapes 14 1 :=
  ⟨fun i => if markedSlot i then -1 else 0,(input src).tape⟩

def output (src : ℤ → Fin 5) : Tapes 14 1 :=
  RepairScan.bank 0 [] 0 (fun _ => blank) 0 src 0 (FlagCopy.keyTape []) (RepairScan.ctrTape [])

def program : Program 14 3 1 where
  tapes_pos := by decide
  start := 0
  transition := fun s sy => if s=0 then some (1,fun i => (sy i,if markedSlot i then .left else .stay))
    else if s=1 then some (2,fun i =>
      if markedSlot i then (PartitionMarked.marker,.right)
      else if i=13 then (separator,.right) else (sy i,.stay)) else none

theorem first_step (src : ℤ → Fin 5) :
    step program ((input src).start program)=some (⟨1,(middle src).head,(middle src).tape⟩ : Config 14 3 1) := by
  simp only [step,Tapes.start,program,ite_true]
  congr 1
  apply congrArg₂ (Config.mk (1 : Fin 3))
  · funext i; by_cases h : markedSlot i <;> simp [input,middle,h,Move.offset]
  · funext i z; by_cases hz : z=0 <;> simp [input,middle,hz]

theorem second_step (src : ℤ → Fin 5) :
    step program (⟨1,(middle src).head,(middle src).tape⟩ : Config 14 3 1)=
      some (⟨2,(output src).head,(output src).tape⟩ : Config 14 3 1) := by
  simp only [step,program,show (1 : Fin 3)≠0 by decide,ite_false,ite_true]
  congr 1
  apply congrArg₂ (Config.mk (2 : Fin 3))
  · funext i; fin_cases i <;> rfl
  · funext i z; fin_cases i <;>
      simp [output,RepairScan.bank,RepairStage.stage,Tapes.append,Fin.addCases,KeyPartition.rawTape,
        KeySelect.selector,PartitionMarked.markedTape,FlagCopy.keyTape,RepairScan.ctrTape,putWord,putBits,
        GrowingCounter.emptyTape,input,middle,markedSlot,PartitionMarked.encoding,bitSymbol,blank,separator,
        PartitionMarked.marker]
    all_goals first
      | rfl
      | (intro hz; rw [hz])
      | (by_cases hz : z = -1 <;> simp only [hz,ite_true,ite_false] <;> first | rfl | (rw [ite_eq_right (by omega : ¬(0≤z ∧ z<0))]))
      | (apply Fin.ext; by_cases hz : z=0 <;> first | rfl | (simp only [hz,ite_true,ite_false]; rfl))


theorem runs (src : ℤ → Fin 5) :
    HoareTime program (fun v => v=input src) (fun v => v=output src) 2 := by
  rintro v rfl
  refine ⟨2,⟨2,(output src).head,(output src).tape⟩,le_rfl,?_,?_,rfl⟩
  · change run program (1+1) _ = _
    rw [run_add,run_one,first_step,Option.bind_some,run_one,second_step]
  · simp [step,program]

end
end IntegerMultBounds.Machine.CountedRepairScanSeed
