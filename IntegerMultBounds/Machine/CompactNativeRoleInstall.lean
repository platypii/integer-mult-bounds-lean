import IntegerMultBounds.Machine.CompactNativeRoleDestructive
import IntegerMultBounds.Machine.BinaryDescriptorInstallMarkedList
import IntegerMultBounds.Machine.RecursiveRowsInstall

/-! Actual installation of generated row/group/erase lengths into a blank
native role-transfer workspace; the two loop markers are initialized by a paid
step, and all five installed words are erased after the destructive transfer. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleInstall
noncomputable section
open BinaryDescriptorInstallMarkedList
open CompactNativeRoleDestructive (localCount withCount)
open RecursiveRowsInstall (readyLocal prepared initProgram)
variable {c : ℕ}

abbrev rawCount (c : ℕ) := localCount c+3
abbrev tapes (c : ℕ) := 43+rawCount c

def blankRaw (payload : Tapes (1+c) 2) :=
  (((payload.append (SharedBank.empty 2 2)).append (SharedBank.empty 2 2)).append
    (SharedBank.empty 1 2)).append (SharedBank.empty 2 2)
def readyRaw (payload : Tapes (1+c) 2) (ws : Fin 3 → List Bool) :=
  ((readyLocal payload ![ws 0,ws 1]).append
    (⟨fun _ => 1,fun _ => RadixZeroFill.encodedBinary (ws 2)⟩ : Tapes 1 2)).append (SharedBank.empty 2 2)
def preparedRaw (payload : Tapes (1+c) 2) (ws : Fin 3 → List Bool) :=
  ((prepared payload ![ws 0,ws 1]).append
    (⟨fun _ => 1,fun _ => RadixZeroFill.encodedBinary (ws 2)⟩ : Tapes 1 2)).append (SharedBank.empty 2 2)

def source (j : Fin 3) : Fin 43 := ![25,26,27] j
def dest (j : Fin 3) : Fin (rawCount c) :=
  match j.val with
  | 0 => Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 2 (Fin.natAdd (1+c) (1 : Fin 2))))
  | 1 => Fin.castAdd 2 (Fin.castAdd 1 (Fin.natAdd ((1+c)+2) (1 : Fin 2)))
  | _ => Fin.castAdd 2 (Fin.natAdd (localCount c) (0 : Fin 1))
def instruction (j : Fin 3) : Instruction (tapes c) :=
  ⟨Fin.castAdd (rawCount c) (source j),Fin.natAdd 43 (dest j),by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
    have := (source j).isLt
    omega⟩
def instructions := (List.finRange 3).map (instruction (c:=c))
def words (ws : Fin 3 → List Bool) (i : Fin (tapes c)) :=
  if i.val=25 then ws 0 else if i.val=26 then ws 1 else if i.val=27 then ws 2 else []

@[simp] theorem source_word (ws : Fin 3 → List Bool) (j : Fin 3) :
    words ws (instruction (c:=c) j).source=ws j := by fin_cases j <;> rfl

theorem dest_injective : Function.Injective (dest (c:=c)) := by
  intro i j h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> first | rfl | (simp [dest,localCount] at hv)

theorem disjoint : Disjoint (instructions (c:=c)) := by
  rintro a ha b hb h
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hb
  have hv := congrArg Fin.val h
  simp only [instruction,Fin.val_natAdd,Fin.val_castAdd] at hv
  have := (source j).isLt
  omega

theorem unique : BinaryDescriptorInstallMarkedList.Unique (instructions (c:=c)) := by
  unfold BinaryDescriptorInstallMarkedList.Unique instructions
  rw [List.map_map]
  apply List.Nodup.map
  · intro i j h
    apply dest_injective
    apply Fin.ext
    have hv := congrArg Fin.val h
    change 43+(dest (c:=c) i).val=43+(dest j).val at hv
    omega
  · exact List.nodup_finRange _

theorem ready_dest (payload : Tapes (1+c) 2) (ws : Fin 3 → List Bool) (j : Fin 3) :
    (readyRaw payload ws).head (dest j)=1 ∧
      (readyRaw payload ws).tape (dest j)=RadixZeroFill.encodedBinary (ws j) := by
  fin_cases j <;> simp [readyRaw,dest,readyLocal,RecursiveRowsInstall.descriptorPair,Tapes.append]

theorem blank_dest (payload : Tapes (1+c) 2) (j : Fin 3) :
    (blankRaw payload).head (dest j)=0 ∧ (blankRaw payload).tape (dest j)=fun _ => blank := by
  fin_cases j <;> simp [blankRaw,dest,Tapes.append,SharedBank.empty]

theorem ready_frame (payload : Tapes (1+c) 2) (ws : Fin 3 → List Bool)
    (i : Fin (rawCount c)) (hi : ∀ j,i≠dest j) :
    (readyRaw payload ws).head i=(blankRaw payload).head i ∧
      (readyRaw payload ws).tape i=(blankRaw payload).tape i := by
  induction i using (Fin.addCases (m:=localCount c+1) (n:=2)) with
  | right i => simp [readyRaw,blankRaw,Tapes.append,SharedBank.empty]
  | left i =>
    induction i using (Fin.addCases (m:=localCount c) (n:=1)) with
    | right i => fin_cases i; exact (hi 2 rfl).elim
    | left i =>
      induction i using (Fin.addCases (m:=(1+c)+2) (n:=2)) with
      | right i =>
        fin_cases i
        · simp [readyRaw,blankRaw,readyLocal,RecursiveRowsInstall.descriptorPair,Tapes.append,SharedBank.empty]
        · exact (hi 1 rfl).elim
      | left i =>
        induction i using (Fin.addCases (m:=1+c) (n:=2)) with
        | right i =>
          fin_cases i
          · simp [readyRaw,blankRaw,readyLocal,RecursiveRowsInstall.descriptorPair,Tapes.append,SharedBank.empty]
          · exact (hi 0 rfl).elim
        | left i => simp [readyRaw,blankRaw,readyLocal,Tapes.append]

theorem result_exact (v : Tapes 43 2) (payload : Tapes (1+c) 2) (ws : Fin 3 → List Bool) :
    result instructions (words ws) (v.append (blankRaw payload)) = v.append (readyRaw payload ws) := by
  have point (i : Fin (tapes c)) :
      (result instructions (words ws) (v.append (blankRaw payload))).head i = (v.append (readyRaw payload ws)).head i ∧
      (result instructions (words ws) (v.append (blankRaw payload))).tape i = (v.append (readyRaw payload ws)).tape i := by
    induction i using Fin.addCases with
    | left i =>
      have hh := result_frame instructions (words ws) (v.append (blankRaw payload)) (Fin.castAdd _ i) (by
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
        have hh := result_dest instructions unique (words ws) (v.append (blankRaw payload)) (instruction j)
          (List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩)
        rw [source_word] at hh
        simpa only [instruction,Tapes.append,Fin.addCases_right,(ready_dest payload ws j).1,(ready_dest payload ws j).2] using hh
      · have hj : ∀ j, i ≠ dest j := by simpa only [not_exists] using hi
        have hh := result_frame instructions (words ws) (v.append (blankRaw payload)) (Fin.natAdd 43 i) (by
          rintro op hop he
          obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
          apply hj j
          apply Fin.ext
          have hh := congrArg Fin.val he
          change 43+i.val = 43+(dest (c := c) j).val at hh
          omega)
        simpa only [Tapes.append,Fin.addCases_right,(ready_frame payload ws i hj).1,(ready_frame payload ws i hj).2] using hh
  apply congrArg₂ Tapes.mk
  · funext i; exact (point i).1
  · funext i; exact (point i).2

def program (c : ℕ) := BinaryDescriptorInstallMarkedList.program 2 (by unfold tapes; omega) (instructions (c:=c))

theorem installs (v : Tapes 43 2) (payload : Tapes (1+c) 2) (ws : Fin 3 → List Bool)
    (hv : ∀ j,v.head (source j)=1 ∧ v.tape (source j)=RadixZeroFill.encodedBinary (ws j)) :
    HoareTime (program c) (fun w => w=v.append (blankRaw payload))
      (fun w => w=v.append (readyRaw payload ws)) (cost (instructions (c:=c)) (words ws)) := by
  have hh := BinaryDescriptorInstallMarkedList.installs_hoare (by unfold tapes; omega : 0<tapes c)
    instructions disjoint unique (words ws) (v.append (blankRaw payload))
    (by
      rintro op hop
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
      rw [source_word]
      simpa only [instruction,Tapes.append,Fin.addCases_left] using hv j)
    (by
      rintro op hop
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
      simpa only [instruction,Tapes.append,Fin.addCases_right] using blank_dest payload j)
  exact hh.consequence (fun _ h => h) (fun _ h => h.trans (result_exact v payload ws)) le_rfl

def initializes (c : ℕ) := Placement.placed (extend (extend (initProgram c 2) 1) 2) (finAddFlip : Fin (rawCount c+43) ≃ Fin (43+rawCount c))

theorem initializes_runs (v : Tapes 43 2) (payload : Tapes (1+c) 2) (ws : Fin 3 → List Bool) :
    HoareTime (initializes c) (fun w => w=v.append (readyRaw payload ws))
      (fun w => w=v.append (preparedRaw payload ws)) 1 :=
  RecursiveRowsConstruct.left_frame (hoare_extend_eq (hoare_extend_eq
    (RecursiveRowsInstall.initializes_hoare payload ![ws 0,ws 1])
      (⟨fun _ => 1,fun _ => RadixZeroFill.encodedBinary (ws 2)⟩ : Tapes 1 2))
      (SharedBank.empty 2 2)) v

def cleanupSlot (j : Fin 5) : Fin (rawCount c) :=
  match j.val with
  | 0 => Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 2 (Fin.natAdd (1+c) (0 : Fin 2))))
  | 1 => dest 0
  | 2 => Fin.castAdd 2 (Fin.castAdd 1 (Fin.natAdd ((1+c)+2) (0 : Fin 2)))
  | 3 => dest 1
  | _ => dest 2

def cleanupSlots := (List.finRange 5).map (cleanupSlot (c:=c))
def cleanupWords (ws : Fin 3 → List Bool) (i : Fin (rawCount c)) :=
  if i.val=(dest (c:=c) 0).val then ws 0 else
  if i.val=(dest (c:=c) 1).val then ws 1 else
  if i.val=(dest (c:=c) 2).val then ws 2 else []

theorem cleanupSlot_injective : Function.Injective (cleanupSlot (c:=c)) := by
  intro i j h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> first | rfl | (simp [cleanupSlot,dest,localCount] at hv)
  all_goals omega

theorem cleanupSlots_nodup : (cleanupSlots (c:=c)).Nodup :=
  List.Nodup.map cleanupSlot_injective (List.nodup_finRange _)

theorem cleanup_ready (payload : Tapes (1+c) 2) (ws : Fin 3 → List Bool) (j : Fin 5) :
    (preparedRaw payload ws).head (cleanupSlot j)=1 ∧
      (preparedRaw payload ws).tape (cleanupSlot j)=
        BinaryDescriptorStack.descriptor (cleanupWords (c:=c) ws (cleanupSlot (c:=c) j)) := by
  have empty_eq : CountedLoopReuseAlphabet.empty (a:=2)=RadixZeroFill.encodedBinary [] := by
    funext z
    by_cases hz : z=0 <;> simp [CountedLoopReuseAlphabet.empty,RadixZeroFill.encodedBinary,CountedCopyReuse.binary,
      CountedCopyReuse.empty,putBits,RadixToBinary.binaryEncoding,hz]
    all_goals rfl
  fin_cases j
  all_goals simp [preparedRaw,cleanupSlot,cleanupWords,dest,localCount,prepared,CountedLoopReuseAlphabet.bank,
    CountedLoopReuseAlphabet.controls,Tapes.append,BinaryDescriptorStackRoundtrip.descriptor_encoded,
    Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  all_goals first | rfl | exact empty_eq | exact (CountedLoopReuseAlphabet.encoding_binary _).symm

theorem cleanup_blank (payload : Tapes (1+c) 2) (j : Fin 5) :
    (blankRaw payload).head (cleanupSlot j)=0 ∧ (blankRaw payload).tape (cleanupSlot j)=fun _ => blank := by
  fin_cases j <;> simp [blankRaw,cleanupSlot,dest,Tapes.append,SharedBank.empty]

theorem cleanup_frame (payload : Tapes (1+c) 2) (ws : Fin 3 → List Bool)
    (i : Fin (rawCount c)) (hi : ∀ j,i≠cleanupSlot j) :
    (preparedRaw payload ws).head i=(blankRaw payload).head i ∧
      (preparedRaw payload ws).tape i=(blankRaw payload).tape i := by
  induction i using (Fin.addCases (m:=localCount c+1) (n:=2)) with
  | right i => simp [preparedRaw,blankRaw,Tapes.append,SharedBank.empty]
  | left i =>
    induction i using (Fin.addCases (m:=localCount c) (n:=1)) with
    | right i => fin_cases i; exact (hi 4 rfl).elim
    | left i =>
      induction i using (Fin.addCases (m:=(1+c)+2) (n:=2)) with
      | right i => fin_cases i
                   · exact (hi 2 rfl).elim
                   · exact (hi 3 rfl).elim
      | left i =>
        induction i using (Fin.addCases (m:=1+c) (n:=2)) with
        | right i => fin_cases i
                     · exact (hi 0 rfl).elim
                     · exact (hi 1 rfl).elim
        | left i => simp [preparedRaw,blankRaw,prepared,CountedLoopReuseAlphabet.bank,Tapes.append]

theorem cleared_exact (payload : Tapes (1+c) 2) (ws : Fin 3 → List Bool) :
    BinaryDescriptorCleanupList.cleared cleanupSlots (preparedRaw payload ws)=blankRaw payload := by
  have point (i : Fin (rawCount c)) :
      (BinaryDescriptorCleanupList.cleared cleanupSlots (preparedRaw payload ws)).head i=(blankRaw payload).head i ∧
      (BinaryDescriptorCleanupList.cleared cleanupSlots (preparedRaw payload ws)).tape i=(blankRaw payload).tape i := by
    by_cases hi : ∃ j,i=cleanupSlot j
    · obtain ⟨j,rfl⟩ := hi
      have hh := BinaryDescriptorCleanupList.cleared_slot cleanupSlots cleanupSlots_nodup (preparedRaw payload ws)
        (cleanupSlot j) (List.mem_map.mpr ⟨j,List.mem_finRange _,rfl⟩)
      rw [(cleanup_blank payload j).1,(cleanup_blank payload j).2]
      exact hh
    · have hn : ∀ j,i≠cleanupSlot j := by simpa only [not_exists] using hi
      have hh := BinaryDescriptorCleanupList.cleared_frame cleanupSlots (preparedRaw payload ws) i (by
        intro he
        obtain ⟨j,_,he⟩ := List.mem_map.mp he
        exact hn j he.symm)
      exact ⟨hh.1.trans (cleanup_frame payload ws i hn).1,hh.2.trans (cleanup_frame payload ws i hn).2⟩
  apply congrArg₂ Tapes.mk <;> funext i
  · exact (point i).1
  · exact (point i).2

def cleanup (c : ℕ) := BinaryDescriptorCleanupList.program (a:=2) (by unfold rawCount; omega) (cleanupSlots (c:=c))

theorem cleanup_runs (payload : Tapes (1+c) 2) (ws : Fin 3 → List Bool) :
    HoareTime (cleanup c) (fun v => v=preparedRaw payload ws) (fun v => v=blankRaw payload)
      (BinaryDescriptorCleanupList.cost (cleanupSlots (c:=c)) (cleanupWords ws)) := by
  have hh := BinaryDescriptorCleanupList.cleanup_hoare (by unfold rawCount; omega : 0<rawCount c)
    cleanupSlots cleanupSlots_nodup (cleanupWords ws) (preparedRaw payload ws) (by
      rintro i hi
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
      exact cleanup_ready payload ws j)
  exact hh.consequence (fun _ h => h) (fun _ h => by simpa only [cleared_exact] using h) le_rfl

end
end IntegerMultBounds.Machine.CompactNativeRoleInstall
