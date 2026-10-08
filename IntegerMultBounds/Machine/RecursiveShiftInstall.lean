import IntegerMultBounds.Machine.RecursiveDimensionBank
import IntegerMultBounds.Machine.RepeatedControlBootstrap
import IntegerMultBounds.Machine.BinaryDescriptorInstallMarkedList

/-! Five physical marked descriptor copies connect the recursive dimension
bank to the blank shift workspace. Original headers and payload are framed. -/
namespace IntegerMultBounds.Machine.RecursiveShiftInstall
open BinaryDescriptorInstallMarkedList
variable {q : ℕ}
noncomputable section

def sourceSlots : Fin 5 → Fin 13 := ![8,9,7,12,6]
def destSlots : Fin 5 → Fin 21 := ![5,7,17,19,20]

def instruction (i : Fin 5) : Instruction 34 :=
  ⟨Fin.castAdd 21 (sourceSlots i),Fin.natAdd 13 (destSlots i),by
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hh
    have hs := (sourceSlots i).isLt
    omega⟩

def instructions : List (Instruction 34) :=
  [instruction 0,instruction 1,instruction 2,instruction 3,instruction 4]

theorem disjoint : Disjoint instructions := by
  intro a ha b hb he
  simp only [instructions,List.mem_cons,List.not_mem_nil,or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> cases he

theorem unique : Unique instructions := by simp [BinaryDescriptorInstallMarkedList.Unique,instructions,instruction,destSlots]

def words (ws : Fin 5 → List Bool) (i : Fin 34) : List Bool :=
  if i.val = 8 then ws 0 else if i.val = 9 then ws 1 else if i.val = 7 then ws 2
    else if i.val = 12 then ws 3 else if i.val = 6 then ws 4 else []

def blankLocal (source : ℤ → Fin 4) : Tapes 21 q :=
  ⟨fun _ => 0,fun i => if i = 10 then FlatRepeatedControlNormalize.encoded source else fun _ => blank⟩

def readyLocal (source : ℤ → Fin 4) (ws : Fin 5 → List Bool) : Tapes 21 q :=
  RepeatedControlBootstrap.input source (fun _ => blank) 0 0 (ws 0) (ws 1) (ws 2) (ws 3) (ws 4)

private theorem ready_head (source : ℤ → Fin 4) (ws : Fin 5 → List Bool) (i : Fin 21) :
    (readyLocal (q := q) source ws).head i =
      if i = 5 ∨ i = 7 ∨ i = 17 ∨ i = 19 ∨ i = 20 then 1 else 0 := by
  change Fin (20+1) at i
  induction i using Fin.addCases with
  | left i =>
    unfold readyLocal RepeatedControlBootstrap.input RepeatedControlBootstrap.raw
    simp only [Tapes.append,Fin.addCases_left]
    fin_cases i <;> simp [RepeatedControlBootstrap.workspace] <;> rfl
  | right i =>
    unfold readyLocal RepeatedControlBootstrap.input
    simp only [Tapes.append,Fin.addCases_right]
    fin_cases i; rfl

private theorem ready_tape (source : ℤ → Fin 4) (ws : Fin 5 → List Bool) (i : Fin 21) :
    (readyLocal (q := q) source ws).tape i =
      if i = 5 then RadixZeroFill.encodedBinary (ws 0) else
      if i = 7 then RadixZeroFill.encodedBinary (ws 1) else
      if i = 17 then RadixZeroFill.encodedBinary (ws 2) else
      if i = 19 then RadixZeroFill.encodedBinary (ws 3) else
      if i = 20 then RadixZeroFill.encodedBinary (ws 4) else
      if i = 10 then FlatRepeatedControlNormalize.encoded source else fun _ => blank := by
  change Fin (20+1) at i
  induction i using Fin.addCases with
  | left i =>
    unfold readyLocal RepeatedControlBootstrap.input RepeatedControlBootstrap.raw
    simp only [Tapes.append,Fin.addCases_left]
    fin_cases i <;> simp [RepeatedControlBootstrap.workspace] <;> first
      | rfl
      | exact (CountedLoopReuseAlphabet.encoding_binary _).symm
  | right i =>
    unfold readyLocal RepeatedControlBootstrap.input
    simp only [Tapes.append,Fin.addCases_right]
    fin_cases i; rfl

def program (q : ℕ) := BinaryDescriptorInstallMarkedList.program q (by decide : 0 < 34) instructions

theorem result_exact (v : Tapes 13 q) (source : ℤ → Fin 4) (ws : Fin 5 → List Bool) :
    result instructions (words ws) (v.append (blankLocal source)) = v.append (readyLocal source ws) := by
  apply congrArg₂ Tapes.mk
  · funext i
    change Fin (13+21) at i
    induction i using Fin.addCases with
    | left i =>
      simp [write,SharedPlacementAlphabet.setTape,instruction,Tapes.append,
        show ∀ j : Fin 5, Fin.castAdd 21 i ≠ Fin.natAdd 13 (destSlots j) by
          intro j he; have hh := congrArg Fin.val he; simp only [Fin.val_castAdd,Fin.val_natAdd] at hh
          have := i.isLt; omega]
    | right i =>
      simp only [Tapes.append,Fin.addCases_right]
      rw [ready_head]
      fin_cases i <;> simp [write,SharedPlacementAlphabet.setTape,instruction,
        destSlots,blankLocal,Fin.addCases]
  · funext i
    change Fin (13+21) at i
    induction i using Fin.addCases with
    | left i =>
      have hf := result_frame instructions (words ws) (v.append (blankLocal source)) (Fin.castAdd 21 i) (by
        intro op hop he
        simp only [instructions,List.mem_cons,List.not_mem_nil,or_false] at hop
        rcases hop with rfl | rfl | rfl | rfl | rfl <;>
          have hh := congrArg Fin.val he <;> simp only [instruction,Fin.val_castAdd,Fin.val_natAdd] at hh <;>
          have := i.isLt <;> omega)
      simpa only [result,instructions,write,SharedPlacementAlphabet.setTape,Tapes.append,Fin.addCases_left] using hf.2
    | right i =>
      simp only [Tapes.append,Fin.addCases_right]
      rw [ready_tape]
      fin_cases i <;> simp [write,SharedPlacementAlphabet.setTape,instruction,
        sourceSlots,destSlots,words,blankLocal,Fin.addCases]

private theorem mem_instruction (op : Instruction 34) (hop : op ∈ instructions) : ∃ i : Fin 5, op = instruction i := by
  simp only [instructions,List.mem_cons,List.not_mem_nil,or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨4,rfl⟩

theorem installs_hoare (v : Tapes 13 q) (source : ℤ → Fin 4) (ws : Fin 5 → List Bool)
    (hready : ∀ i, v.head (sourceSlots i) = 1 ∧ v.tape (sourceSlots i) = RadixZeroFill.encodedBinary (ws i)) :
    HoareTime (program q) (fun w => w = v.append (blankLocal source))
      (fun w => w = v.append (readyLocal source ws)) (cost instructions (words ws)) := by
  have hh := BinaryDescriptorInstallMarkedList.installs_hoare (by decide : 0 < 34) instructions disjoint unique
    (words ws) (v.append (blankLocal source))
    (by intro op hop
        obtain ⟨i,rfl⟩ := mem_instruction op hop
        have ht := hready i
        simp only [instruction,Tapes.append,Fin.addCases_left]
        fin_cases i <;> simpa [sourceSlots,words] using ht)
    (by intro op hop
        obtain ⟨i,rfl⟩ := mem_instruction op hop
        fin_cases i <;> exact ⟨rfl,rfl⟩)
  exact hh.consequence (fun _ h => h) (fun w hw => hw.trans (result_exact v source ws)) le_rfl

theorem cost_bound (ws : Fin 5 → List Bool) (L : ℕ) (hL : ∀ i, (ws i).length ≤ L) :
    cost instructions (words ws) ≤ 10*L+30 := by
  have hh := BinaryDescriptorInstallMarkedList.cost_le instructions (words ws) L (by
    intro op hop
    obtain ⟨i,rfl⟩ := mem_instruction op hop
    have hi := hL i
    fin_cases i <;> simpa [instruction,sourceSlots,words] using hi)
  change cost instructions (words ws) ≤ 5*(2*L+6) at hh
  nlinarith


end
end IntegerMultBounds.Machine.RecursiveShiftInstall
