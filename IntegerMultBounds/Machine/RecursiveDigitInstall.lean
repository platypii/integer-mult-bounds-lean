import IntegerMultBounds.Machine.RecursiveDigitDimensions
import IntegerMultBounds.Machine.DigitInterchangeClean
import IntegerMultBounds.Machine.BinaryDescriptorInstallMarkedList

/-! Four physical marked descriptor copies connect the generated recursive
base dimensions to a completely blank digit-interchange workspace. -/
namespace IntegerMultBounds.Machine.RecursiveDigitInstall
open BinaryDescriptorInstallMarkedList
open DigitInterchangeBank (Slot slot name TapeCount)
variable {q : ℕ}
noncomputable section

abbrev LocalTapes (q : ℕ) := TapeCount q+TapeCount q
abbrev TotalTapes (q : ℕ) := 17+LocalTapes q

def source : Fin (LocalTapes q) := Fin.castAdd (TapeCount q) (slot .source)
def dest (j : Fin 4) : Fin (LocalTapes q) := Fin.castAdd (TapeCount q) (slot (.header j))

theorem dest_injective : Function.Injective (dest (q := q)) :=
  (Fin.castAdd_injective _ _).comp ((Fintype.equivFin (Slot q)).injective.comp (fun _ _ h => Slot.header.inj h))

def instruction (j : Fin 4) : Instruction (TotalTapes q) :=
  ⟨Fin.castAdd _ (RecursiveDigitDimensions.sourceSlots j),Fin.natAdd 17 (dest j),by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hh
    have := (RecursiveDigitDimensions.sourceSlots j).isLt
    omega⟩

def instructions : List (Instruction (TotalTapes q)) := (List.finRange 4).map instruction

theorem disjoint : Disjoint (instructions (q := q)) := by
  rintro a ha b hb he
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hb
  have hh := congrArg Fin.val he
  simp only [instruction,Fin.val_castAdd,Fin.val_natAdd] at hh
  have := (RecursiveDigitDimensions.sourceSlots j).isLt
  omega

theorem unique : Unique (instructions (q := q)) := by
  unfold BinaryDescriptorInstallMarkedList.Unique instructions
  rw [List.map_map]
  apply List.Nodup.map
  · intro i j he
    apply dest_injective (q := q)
    apply Fin.ext
    have hh := congrArg Fin.val he
    change 17+(dest (q := q) i).val = 17+(dest j).val at hh
    omega
  · exact List.nodup_finRange _

def words (ws : Fin 4 → List Bool) (i : Fin (TotalTapes q)) : List Bool :=
  if i.val = 14 then ws 0 else if i.val = 11 then ws 1 else if i.val = 8 then ws 2
    else if i.val = 16 then ws 3 else []

@[simp] theorem source_word (ws : Fin 4 → List Bool) (j : Fin 4) :
    words (q := q) ws (instruction j).source = ws j := by
  fin_cases j <;> rfl

def blankLocal (f : ℤ → Fin (q+4)) : Tapes (LocalTapes q) q :=
  ⟨fun _ => 0,fun i => if i = source then f else fun _ => blank⟩

def readyWord (f : ℤ → Fin (q+4)) (ws : Fin 4 → List Bool) : Slot q → ℤ → Fin (q+4)
  | .source => f | .header j => RadixZeroFill.encodedBinary (ws j) | _ => fun _ => blank

def readyLocal (f : ℤ → Fin (q+4)) (ws : Fin 4 → List Bool) : Tapes (LocalTapes q) q :=
  (⟨fun i => DigitInterchangeClean.rawHead (name i),fun i => readyWord f ws (name i)⟩ : Tapes (TapeCount q) q).append
    (SharedBank.empty (TapeCount q) q)

private theorem dest_ready (f : ℤ → Fin (q+4)) (ws : Fin 4 → List Bool) (j : Fin 4) :
    (readyLocal f ws).head (dest j) = 1 ∧
    (readyLocal f ws).tape (dest j) = RadixZeroFill.encodedBinary (ws j) := by
  simp [readyLocal,dest,Tapes.append,DigitInterchangeClean.rawHead,readyWord]

private theorem dest_blank (f : ℤ → Fin (q+4)) (j : Fin 4) :
    (blankLocal f).head (dest j) = 0 ∧ (blankLocal f).tape (dest j) = fun _ => blank := by
  have hn : dest (q := q) j ≠ source := by
    intro he
    have he' := (Fin.castAdd_injective _ _) he
    have hh := (Fintype.equivFin (Slot q)).injective he'
    cases hh
  simp [blankLocal,hn]

private theorem ready_frame (f : ℤ → Fin (q+4)) (ws : Fin 4 → List Bool)
    (i : Fin (LocalTapes q)) (hi : ∀ j, i ≠ dest j) :
    (blankLocal f).head i = (readyLocal f ws).head i ∧
    (blankLocal f).tape i = (readyLocal f ws).tape i := by
  induction i using Fin.addCases with
  | left i =>
    obtain ⟨z,rfl⟩ := (Fintype.equivFin (Slot q)).surjective i
    cases z with
    | header j => exact (hi j rfl).elim
    | source => simp [blankLocal,readyLocal,Tapes.append,source,DigitInterchangeClean.rawHead,readyWord,slot,name]
    | dest => simp [blankLocal,readyLocal,Tapes.append,source,DigitInterchangeClean.rawHead,readyWord,slot,name]
    | first h => simp [blankLocal,readyLocal,Tapes.append,source,DigitInterchangeClean.rawHead,readyWord,slot,name]
    | leaf h d => simp [blankLocal,readyLocal,Tapes.append,source,DigitInterchangeClean.rawHead,readyWord,slot,name]
    | merged h => simp [blankLocal,readyLocal,Tapes.append,source,DigitInterchangeClean.rawHead,readyWord,slot,name]
    | rowClock => simp [blankLocal,readyLocal,Tapes.append,source,DigitInterchangeClean.rawHead,readyWord,slot,name]
    | groupClock => simp [blankLocal,readyLocal,Tapes.append,source,DigitInterchangeClean.rawHead,readyWord,slot,name]
  | right i =>
    have hn : Fin.natAdd (TapeCount q) i ≠ source (q := q) := by
      intro he
      have hh := congrArg Fin.val he
      simp only [source,Fin.val_natAdd,Fin.val_castAdd] at hh
      have := (slot (Slot.source (q := q))).isLt
      omega
    simp only [blankLocal,readyLocal,Tapes.append,Fin.addCases_right,SharedBank.empty,hn,ite_false]
    trivial

theorem result_exact (v : Tapes 17 q) (f : ℤ → Fin (q+4)) (ws : Fin 4 → List Bool) :
    result instructions (words ws) (v.append (blankLocal f)) = v.append (readyLocal f ws) := by
  have point (i : Fin (TotalTapes q)) :
      (result instructions (words ws) (v.append (blankLocal f))).head i = (v.append (readyLocal f ws)).head i ∧
      (result instructions (words ws) (v.append (blankLocal f))).tape i = (v.append (readyLocal f ws)).tape i := by
    induction i using Fin.addCases with
    | left i =>
      have hh := result_frame instructions (words ws) (v.append (blankLocal f)) (Fin.castAdd _ i) (by
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
        have hh := result_dest instructions unique (words ws) (v.append (blankLocal f)) (instruction j)
          (List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩)
        rw [source_word] at hh
        simpa only [instruction,Tapes.append,Fin.addCases_right,(dest_ready f ws j).1,(dest_ready f ws j).2] using hh
      · have hj : ∀ j, i ≠ dest j := by simpa only [not_exists] using hi
        have hh := result_frame instructions (words ws) (v.append (blankLocal f)) (Fin.natAdd 17 i) (by
          rintro op hop he
          obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
          apply hj j
          apply Fin.ext
          have hh := congrArg Fin.val he
          change 17+i.val = 17+(dest (q := q) j).val at hh
          omega)
        simpa only [Tapes.append,Fin.addCases_right,(ready_frame f ws i hj).1,(ready_frame f ws i hj).2] using hh
  apply congrArg₂ Tapes.mk
  · funext i; exact (point i).1
  · funext i; exact (point i).2

def program (q : ℕ) := BinaryDescriptorInstallMarkedList.program q (by unfold TotalTapes; omega) (instructions (q := q))

theorem installs_hoare (v : Tapes 17 q) (f : ℤ → Fin (q+4)) (ws : Fin 4 → List Bool)
    (hv : ∀ j, v.head (RecursiveDigitDimensions.sourceSlots j) = 1 ∧
      v.tape (RecursiveDigitDimensions.sourceSlots j) = RadixZeroFill.encodedBinary (ws j)) :
    HoareTime (program q) (fun w => w = v.append (blankLocal f))
      (fun w => w = v.append (readyLocal f ws)) (cost (instructions (q := q)) (words ws)) := by
  have hh := BinaryDescriptorInstallMarkedList.installs_hoare (by unfold TotalTapes; omega : 0 < TotalTapes q)
    instructions disjoint unique (words ws) (v.append (blankLocal f))
    (by
      rintro op hop
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
      rw [source_word]
      simpa only [instruction,Tapes.append,Fin.addCases_left] using hv j)
    (by
      rintro op hop
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
      simpa only [instruction,Tapes.append,Fin.addCases_right] using dest_blank f j)
  exact hh.consequence (fun _ h => h) (fun _ h => h.trans (result_exact v f ws)) le_rfl

theorem cost_bound (ws : Fin 4 → List Bool) (L : ℕ) (hL : ∀ j, (ws j).length ≤ L) :
    cost (instructions (q := q)) (words ws) ≤ 8*L+24 := by
  have hh := BinaryDescriptorInstallMarkedList.cost_le (instructions (q := q)) (words ws) L (by
    rintro op hop
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
    simpa only [source_word] using hL j)
  simp only [instructions,List.length_map,List.length_finRange] at hh ⊢
  nlinarith

/-- The installed sentinels are exactly those consumed by the clean base machine. -/
theorem ready_eq (x : DigitInterchangeRows.Array O q C E q) (ws : Fin 4 → List Bool) :
    readyLocal (putWord (fun _ => blank) 0 (CyclicRowSplit.sourceWord (DigitInterchangeRows.outerRows x))) ws =
      DigitInterchangeClean.bank x (ws 0) (ws 1) (ws 2) (ws 3) := by
  unfold readyLocal DigitInterchangeClean.bank
  congr 1
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    cases hn : name i <;> simp only [DigitInterchangeClean.rawBank,DigitInterchangeClean.rawWord,hn,readyWord]
    rename_i j
    have he : DigitInterchangeBank.headerWord (ws 0) (ws 1) (ws 2) (ws 3) j = ws j := by fin_cases j <;> rfl
    rw [he]
    exact CountedLoopReuseAlphabet.encoding_binary _

end
end IntegerMultBounds.Machine.RecursiveDigitInstall
