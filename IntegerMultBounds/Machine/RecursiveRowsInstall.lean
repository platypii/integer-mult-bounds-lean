import IntegerMultBounds.Machine.RecursiveRowsDimensions
import IntegerMultBounds.Machine.RecursiveInterchangeRowsNormalized
import IntegerMultBounds.Machine.BinaryDescriptorInstallMarkedList

/-! Install the two generated cyclic row counters into a blank transfer bank.
Both copies and the two loop sentinel initializations are actual charged steps. -/
namespace IntegerMultBounds.Machine.RecursiveRowsInstall
open BinaryDescriptorInstallMarkedList
variable {q c : ℕ}
noncomputable section

abbrev LocalTapes (c : ℕ) := ((1+c)+2)+2
abbrev TotalTapes (c : ℕ) := 38+LocalTapes c

def dest (j : Fin 2) : Fin (LocalTapes c) :=
  if j = 0 then Fin.castAdd 2 (Fin.natAdd (1+c) (1 : Fin 2))
    else Fin.natAdd ((1+c)+2) (1 : Fin 2)

theorem dest_injective : Function.Injective (dest (c := c)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (have hh := congrArg Fin.val h; simp [dest] at hh)

def instruction (j : Fin 2) : Instruction (TotalTapes c) :=
  ⟨Fin.castAdd _ (RecursiveRowsDimensions.sourceSlots j),Fin.natAdd 38 (dest j),by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hh
    have := (RecursiveRowsDimensions.sourceSlots j).isLt
    omega⟩

def instructions : List (Instruction (TotalTapes c)) := (List.finRange 2).map instruction

theorem disjoint : Disjoint (instructions (c := c)) := by
  rintro a ha b hb he
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hb
  have hh := congrArg Fin.val he
  simp only [instruction,Fin.val_castAdd,Fin.val_natAdd] at hh
  have := (RecursiveRowsDimensions.sourceSlots j).isLt
  omega

theorem unique : Unique (instructions (c := c)) := by
  unfold BinaryDescriptorInstallMarkedList.Unique instructions
  rw [List.map_map]
  apply List.Nodup.map
  · intro i j he
    apply dest_injective (c := c)
    apply Fin.ext
    have hh := congrArg Fin.val he
    change 38+(dest (c := c) i).val = 38+(dest j).val at hh
    omega
  · exact List.nodup_finRange _

def words (ws : Fin 2 → List Bool) (i : Fin (TotalTapes c)) : List Bool :=
  if i.val = 18 then ws 0 else if i.val = 19 then ws 1 else []

@[simp] theorem source_word (ws : Fin 2 → List Bool) (j : Fin 2) :
    words (c := c) ws (instruction j).source = ws j := by
  fin_cases j <;> rfl

def blankLocal (payload : Tapes (1+c) q) : Tapes (LocalTapes c) q :=
  (payload.append (SharedBank.empty 2 q)).append (SharedBank.empty 2 q)

def descriptorPair (ws : List Bool) : Tapes 2 q :=
  ⟨![0,1],![fun _ => blank,RadixZeroFill.encodedBinary ws]⟩

def readyLocal (payload : Tapes (1+c) q) (ws : Fin 2 → List Bool) : Tapes (LocalTapes c) q :=
  (payload.append (descriptorPair (ws 0))).append (descriptorPair (ws 1))

private theorem dest_ready (payload : Tapes (1+c) q) (ws : Fin 2 → List Bool) (j : Fin 2) :
    (readyLocal payload ws).head (dest j) = 1 ∧
    (readyLocal payload ws).tape (dest j) = RadixZeroFill.encodedBinary (ws j) := by
  fin_cases j <;> simp [readyLocal,dest,Tapes.append,descriptorPair]

private theorem dest_blank (payload : Tapes (1+c) q) (j : Fin 2) :
    (blankLocal payload).head (dest j) = 0 ∧ (blankLocal payload).tape (dest j) = fun _ => blank := by
  fin_cases j <;> simp [blankLocal,dest,Tapes.append,SharedBank.empty]

private theorem ready_frame (payload : Tapes (1+c) q) (ws : Fin 2 → List Bool)
    (i : Fin (LocalTapes c)) (hi : ∀ j, i ≠ dest j) :
    (blankLocal payload).head i = (readyLocal payload ws).head i ∧
    (blankLocal payload).tape i = (readyLocal payload ws).tape i := by
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i => simp [blankLocal,readyLocal,Tapes.append]
    | right i =>
      fin_cases i
      · simp [blankLocal,readyLocal,Tapes.append,descriptorPair,SharedBank.empty]
      · exact (hi 0 rfl).elim
  | right i =>
    fin_cases i
    · simp [blankLocal,readyLocal,Tapes.append,descriptorPair,SharedBank.empty]
    · exact (hi 1 rfl).elim

theorem result_exact (v : Tapes 38 q) (payload : Tapes (1+c) q) (ws : Fin 2 → List Bool) :
    result instructions (words ws) (v.append (blankLocal payload)) = v.append (readyLocal payload ws) := by
  have point (i : Fin (TotalTapes c)) :
      (result instructions (words ws) (v.append (blankLocal payload))).head i = (v.append (readyLocal payload ws)).head i ∧
      (result instructions (words ws) (v.append (blankLocal payload))).tape i = (v.append (readyLocal payload ws)).tape i := by
    induction i using Fin.addCases with
    | left i =>
      have hh := result_frame instructions (words ws) (v.append (blankLocal payload)) (Fin.castAdd _ i) (by
        rintro op hop he
        obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
        have hv := congrArg Fin.val he
        simp only [instruction,Fin.val_castAdd,Fin.val_natAdd] at hv
        have := i.isLt
        omega)
      simpa only [Tapes.append,Fin.addCases_left] using hh
    | right i =>
      by_cases hi : ∃ j, i = dest j
      · obtain ⟨j,rfl⟩ := hi
        have hh := result_dest instructions unique (words ws) (v.append (blankLocal payload)) (instruction j)
          (List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩)
        rw [source_word] at hh
        simpa only [instruction,Tapes.append,Fin.addCases_right,(dest_ready payload ws j).1,(dest_ready payload ws j).2] using hh
      · have hj : ∀ j, i ≠ dest j := by simpa only [not_exists] using hi
        have hh := result_frame instructions (words ws) (v.append (blankLocal payload)) (Fin.natAdd 38 i) (by
          rintro op hop he
          obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
          apply hj j
          apply Fin.ext
          have hh := congrArg Fin.val he
          change 38+i.val = 38+(dest (c := c) j).val at hh
          omega)
        simpa only [Tapes.append,Fin.addCases_right,(ready_frame payload ws i hj).1,(ready_frame payload ws i hj).2] using hh
  apply congrArg₂ Tapes.mk
  · funext i; exact (point i).1
  · funext i; exact (point i).2

def program (c q : ℕ) := BinaryDescriptorInstallMarkedList.program q (by unfold TotalTapes; omega) (instructions (c := c))

theorem installs_hoare (v : Tapes 38 q) (payload : Tapes (1+c) q) (ws : Fin 2 → List Bool)
    (hv : ∀ j, v.head (RecursiveRowsDimensions.sourceSlots j) = 1 ∧
      v.tape (RecursiveRowsDimensions.sourceSlots j) = RadixZeroFill.encodedBinary (ws j)) :
    HoareTime (program c q) (fun w => w = v.append (blankLocal payload))
      (fun w => w = v.append (readyLocal payload ws)) (cost (instructions (c := c)) (words ws)) := by
  have hh := BinaryDescriptorInstallMarkedList.installs_hoare (by unfold TotalTapes; omega : 0 < TotalTapes c)
    instructions disjoint unique (words ws) (v.append (blankLocal payload))
    (by
      rintro op hop
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
      rw [source_word]
      simpa only [instruction,Tapes.append,Fin.addCases_left] using hv j)
    (by
      rintro op hop
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
      simpa only [instruction,Tapes.append,Fin.addCases_right] using dest_blank payload j)
  exact hh.consequence (fun _ h => h) (fun _ h => h.trans (result_exact v payload ws)) le_rfl

theorem cost_bound (ws : Fin 2 → List Bool) (L : ℕ) (hL : ∀ j, (ws j).length ≤ L) :
    cost (instructions (c := c)) (words ws) ≤ 4*L+12 := by
  have hh := BinaryDescriptorInstallMarkedList.cost_le (instructions (c := c)) (words ws) L (by
    rintro op hop
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
    simpa only [source_word] using hL j)
  simp only [instructions,List.length_map,List.length_finRange] at hh ⊢
  nlinarith


def clock (i : Fin (LocalTapes c)) : Bool := decide (i.val = 1+c ∨ i.val = (1+c)+2)

def prepared (payload : Tapes (1+c) q) (ws : Fin 2 → List Bool) : Tapes (LocalTapes c) q :=
  CountedLoopReuseAlphabet.bank
    (CountedLoopReuseAlphabet.bank payload CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary (ws 0)) 1 1)
    CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary (ws 1)) 1 1

def initProgram (c q : ℕ) : Program (LocalTapes c) 2 q where
  tapes_pos := by unfold LocalTapes; omega
  start := 0
  transition := fun st sy => if st = 0 then some (1,fun i =>
    (if clock i then separator else sy i,if clock i then .right else .stay)) else none

theorem initializes_hoare (payload : Tapes (1+c) q) (ws : Fin 2 → List Bool) :
    HoareTime (initProgram c q) (fun v => v = readyLocal payload ws)
      (fun v => v = prepared payload ws) 1 := by
  have hn : 1+c+2+1 ≠ 1+c := by omega
  have he : RadixZeroFill.encodedBinary (q := q) = CountedLoopReuseAlphabet.binary := by
    funext bs
    exact CountedLoopReuseAlphabet.encoding_binary bs
  rintro v rfl
  refine ⟨1,⟨1,(prepared payload ws).head,(prepared payload ws).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,initProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i =>
          have h1 : i.val ≠ 1+c := by omega
          have h2 : i.val ≠ 1+c+2 := by omega
          simp [readyLocal,prepared,Tapes.append,CountedLoopReuseAlphabet.bank,clock,Move.offset,h1,h2]
        | right i => fin_cases i <;>
            simp [readyLocal,prepared,Tapes.append,CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,descriptorPair,clock,Move.offset]
      | right i => fin_cases i <;>
          simp [readyLocal,prepared,Tapes.append,CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,descriptorPair,clock,Move.offset,hn]
    · funext i z
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i =>
          have h1 : i.val ≠ 1+c := by omega
          have h2 : i.val ≠ 1+c+2 := by omega
          simp [readyLocal,prepared,Tapes.append,CountedLoopReuseAlphabet.bank,clock,h1,h2]
          intro hz; subst z; rfl
        | right i => fin_cases i <;>
            simp [readyLocal,prepared,Tapes.append,CountedLoopReuseAlphabet.bank,descriptorPair,clock,
              CountedLoopReuseAlphabet.controls,CountedLoopReuseAlphabet.empty,he] <;>
              (intro hz; subst z; rfl)
      | right i => fin_cases i <;>
          simp [readyLocal,prepared,Tapes.append,CountedLoopReuseAlphabet.bank,descriptorPair,clock,
            CountedLoopReuseAlphabet.controls,CountedLoopReuseAlphabet.empty,he,hn] <;>
              (intro hz; subst z; rfl)
  · simp [step,initProgram]

end
end IntegerMultBounds.Machine.RecursiveRowsInstall
