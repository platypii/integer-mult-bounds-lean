import IntegerMultBounds.Machine.CompactNativeRoleScalarHeaders
import IntegerMultBounds.Machine.BinaryDescriptorInstallMarkedList

/-! The reservation-derived nine words and six actual retained controller
ports are physically copied into fresh original13+ell/p storage. Controller
ports are slots,count,left,right,source,target; copies preserve every caller
word and no runtime value is built into the finite control. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleStageCopy
noncomputable section
open BinaryDescriptorInstallMarkedList
open ActiveRepairRankHeadersCommands (State)
open RecursiveChildQuotientsConstant (bits)
variable {t : ℕ}

def destination : Fin 15 → Fin 28 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,17,18]
theorem destination_injective : Function.Injective destination := by decide

def values (geometry : Fin 9 → ℕ) (controller : Fin 6 → ℕ) : Fin 15 → ℕ :=
  ![geometry 0,geometry 1,geometry 2,geometry 3,geometry 4,geometry 5,
    controller 0,controller 1,controller 2,controller 3,geometry 6,controller 4,controller 5,geometry 7,geometry 8]
def sources (geometry : Fin 9 → Fin t) (controller : Fin 6 → Fin t) : Fin 15 → Fin t :=
  ![geometry 0,geometry 1,geometry 2,geometry 3,geometry 4,geometry 5,
    controller 0,controller 1,controller 2,controller 3,geometry 6,controller 4,controller 5,geometry 7,geometry 8]
def metadata (vs : Fin 15 → ℕ) : State := fun i =>
  match i.val with
  | 0 => some (vs 0) | 1 => some (vs 1) | 2 => some (vs 2) | 3 => some (vs 3)
  | 4 => some (vs 4) | 5 => some (vs 5) | 6 => some (vs 6) | 7 => some (vs 7)
  | 8 => some (vs 8) | 9 => some (vs 9) | 10 => some (vs 10) | 11 => some (vs 11)
  | 12 => some (vs 12) | 17 => some (vs 13) | 18 => some (vs 14) | _ => none

def instruction (focus : Fin 15 → Fin t) (j : Fin 15) : Instruction (t+28) :=
  ⟨Fin.castAdd 28 (focus j),Fin.natAdd t (destination j),by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
    have := (focus j).isLt
    omega⟩
def instructions (focus : Fin 15 → Fin t) := (List.finRange 15).map (instruction focus)

def wordAt (focus : Fin 15 → Fin t) (vs : Fin 15 → ℕ) (i : Fin (t+28)) :=
  if h : ∃ j,Fin.castAdd 28 (focus j)=i then bits (vs (Classical.choose h)) else []

/-- Repeated source ports are legal only when their physically retained values
agree. This is equality of real descriptor words, not an input-value oracle. -/
def Consistent (focus : Fin 15 → Fin t) (vs : Fin 15 → ℕ) :=
  ∀ i j,focus i=focus j → vs i=vs j

theorem source_word (focus : Fin 15 → Fin t) (vs : Fin 15 → ℕ) (hc : Consistent focus vs) (j : Fin 15) :
    wordAt focus vs (instruction focus j).source=bits (vs j) := by
  unfold wordAt instruction
  have he : ∃ i,Fin.castAdd 28 (focus i)=Fin.castAdd 28 (focus j) := ⟨j,rfl⟩
  rw [dite_eq_left he]
  congr 1
  apply hc
  apply Fin.ext
  have hv := congrArg Fin.val (Classical.choose_spec he)
  simpa only [Fin.val_castAdd] using hv

theorem disjoint (focus : Fin 15 → Fin t) : Disjoint (instructions focus) := by
  rintro a ha b hb h
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hb
  have hv := congrArg Fin.val h
  simp only [instruction,Fin.val_natAdd,Fin.val_castAdd] at hv
  have := (focus j).isLt
  omega

theorem unique (focus : Fin 15 → Fin t) : BinaryDescriptorInstallMarkedList.Unique (instructions focus) := by
  unfold BinaryDescriptorInstallMarkedList.Unique instructions
  rw [List.map_map]
  apply List.Nodup.map
  · intro i j h
    apply destination_injective
    apply Fin.ext
    have hv := congrArg Fin.val h
    change t+(destination i).val=t+(destination j).val at hv
    omega
  · exact List.nodup_finRange _

theorem metadata_dest (vs : Fin 15 → ℕ) (j : Fin 15) : metadata vs (destination j)=some (vs j) := by
  fin_cases j <;> rfl

theorem metadata_outside (vs : Fin 15 → ℕ) (i : Fin 28) (hi : ∀ j,i≠destination j) : metadata vs i=none := by
  fin_cases i
  all_goals first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim |
    exact (hi 4 rfl).elim | exact (hi 5 rfl).elim | exact (hi 6 rfl).elim | exact (hi 7 rfl).elim | exact (hi 8 rfl).elim |
    exact (hi 9 rfl).elim | exact (hi 10 rfl).elim | exact (hi 11 rfl).elim | exact (hi 12 rfl).elim |
    exact (hi 13 rfl).elim | exact (hi 14 rfl).elim

theorem result_exact (focus : Fin 15 → Fin t) (vs : Fin 15 → ℕ) (hc : Consistent focus vs) (caller : Tapes t 2) :
    result (instructions focus) (wordAt focus vs) (caller.append (SharedBank.empty 28 2))=
      caller.append (ActiveRepairRankHeadersCommands.caller (metadata vs)) := by
  have point (i : Fin (t+28)) :
      (result (instructions focus) (wordAt focus vs) (caller.append (SharedBank.empty 28 2))).head i=
        (caller.append (ActiveRepairRankHeadersCommands.caller (metadata vs))).head i ∧
      (result (instructions focus) (wordAt focus vs) (caller.append (SharedBank.empty 28 2))).tape i=
        (caller.append (ActiveRepairRankHeadersCommands.caller (metadata vs))).tape i := by
    induction i using Fin.addCases with
    | left i =>
      have hh := result_frame (instructions focus) (wordAt focus vs) (caller.append (SharedBank.empty 28 2))
        (Fin.castAdd 28 i) (by
          rintro op hop h
          obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
          have hv := congrArg Fin.val h
          simp only [instruction,Fin.val_natAdd,Fin.val_castAdd] at hv
          have := i.isLt
          omega)
      simpa only [Tapes.append,Fin.addCases_left] using hh
    | right i =>
      by_cases hi : ∃ j,i=destination j
      · obtain ⟨j,rfl⟩ := hi
        have hh := result_dest (instructions focus) (unique focus) (wordAt focus vs)
          (caller.append (SharedBank.empty 28 2)) (instruction focus j) (List.mem_map.mpr ⟨j,List.mem_finRange _,rfl⟩)
        rw [source_word focus vs hc] at hh
        simpa only [instruction,Tapes.append,Fin.addCases_right,ActiveRepairRankHeadersCommands.caller,
          metadata_dest,Option.isSome_some,ite_true] using hh
      · have hn : ∀ j,i≠destination j := by simpa only [not_exists] using hi
        have hh := result_frame (instructions focus) (wordAt focus vs) (caller.append (SharedBank.empty 28 2))
          (Fin.natAdd t i) (by
            rintro op hop h
            obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
            exact hn j (Fin.ext (by
              have hv := congrArg Fin.val h
              change t+i.val=t+(destination j).val at hv
              omega)))
        simpa only [Tapes.append,Fin.addCases_right,ActiveRepairRankHeadersCommands.caller,metadata_outside vs i hn,
          Option.isSome_none,Bool.false_eq_true,ite_false,SharedBank.empty] using hh
  apply congrArg₂ Tapes.mk <;> funext i
  · exact (point i).1
  · exact (point i).2

def program (focus : Fin 15 → Fin t) := BinaryDescriptorInstallMarkedList.program 2 (by omega : 0<t+28) (instructions focus)

theorem runs (focus : Fin 15 → Fin t) (vs : Fin 15 → ℕ) (caller : Tapes t 2)
    (hv : ∀ j,caller.head (focus j)=1 ∧ caller.tape (focus j)=RadixZeroFill.encodedBinary (bits (vs j)))
    (hc : Consistent focus vs) :
    HoareTime (program focus) (fun v => v=caller.append (SharedBank.empty 28 2))
      (fun v => v=caller.append (ActiveRepairRankHeadersCommands.caller (metadata vs)))
      (cost (instructions focus) (wordAt focus vs)) := by
  have hh := BinaryDescriptorInstallMarkedList.installs_hoare (by omega : 0<t+28) (instructions focus)
    (disjoint focus) (unique focus) (wordAt focus vs) (caller.append (SharedBank.empty 28 2))
    (by
      rintro op hop
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
      rw [source_word focus vs hc]
      simpa only [instruction,Tapes.append,Fin.addCases_left] using hv j)
    (by
      rintro op hop
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
      simp [instruction,Tapes.append,SharedBank.empty])
  exact hh.consequence (fun _ h => h) (fun _ h => h.trans (result_exact focus vs hc caller)) le_rfl

end
end IntegerMultBounds.Machine.CompactNativeRoleStageCopy
