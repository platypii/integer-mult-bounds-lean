import IntegerMultBounds.Machine.BinaryDescriptorReplaceList
import IntegerMultBounds.Machine.RecursiveChildDimensionsClean
import IntegerMultBounds.Machine.RecursiveHeaderBounds

/-! Physically replace the five changing parent header slots by generated child
headers. The unchanged A header stays in place. Old parent headers must be saved
by the caller before this destructive update; no implicit reset is used. -/
namespace IntegerMultBounds.Machine.RecursiveChildHeaderInstall
open BinaryDescriptorInstallMarkedList
variable {q : ℕ}
noncomputable section

def sourceSlots : Fin 5 → Fin 38 := ![10,15,9,17,18]
def destSlots : Fin 5 → Fin 38 := ![4,5,6,7,8]
def instruction (i : Fin 5) : Instruction 38 :=
  ⟨sourceSlots i,destSlots i,by fin_cases i <;> decide⟩
def instructions := List.ofFn instruction

theorem disjoint : Disjoint instructions := by
  intro a ha b hb
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
  fin_cases i <;> fin_cases j <;> decide

theorem unique : Unique instructions := by
  unfold BinaryDescriptorInstallMarkedList.Unique instructions
  decide

def words (hs : Fin 6 → List Bool) (i : Fin 38) : List Bool :=
  if i = 4 then hs 1 else if i = 5 then hs 2 else if i = 6 then hs 3
  else if i = 7 then hs 4 else if i = 8 then hs 5 else []
def generated (hs : Fin 6 → List Bool) (i : Fin 38) : List Bool :=
  if i = 10 then hs 1 else if i = 15 then hs 2 else if i = 9 then hs 3
  else if i = 17 then hs 4 else if i = 18 then hs 5 else []

def program (q : ℕ) := BinaryDescriptorReplaceList.program (q := q) (by decide : 0 < 38) instructions
def output (hs : Fin 6 → List Bool) (v : Tapes 38 q) :=
  BinaryDescriptorReplaceList.output instructions (generated hs) v

theorem installs (old child : Fin 6 → List Bool) (v : Tapes 38 q)
    (hs : ∀ i : Fin 5, v.head (sourceSlots i) = 1 ∧
      v.tape (sourceSlots i) = RadixZeroFill.encodedBinary (child i.succ))
    (hd : ∀ i : Fin 5, v.head (destSlots i) = 1 ∧
      v.tape (destSlots i) = RadixZeroFill.encodedBinary (old i.succ)) :
    HoareTime (program q) (fun w => w = v) (fun w => w = output child v)
      (BinaryDescriptorReplaceList.cost instructions (words old) (generated child)) := by
  apply BinaryDescriptorReplaceList.replaces_hoare (by decide) instructions disjoint unique
    (words old) (generated child) v
  · intro op hop
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hop
    have h := hs i
    fin_cases i <;> simpa [instruction,sourceSlots,generated] using h
  · intro op hop
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hop
    have h := hd i
    fin_cases i <;> simpa [instruction,destSlots,words] using h

theorem installed (child : Fin 6 → List Bool) (v : Tapes 38 q) (i : Fin 5) :
    (output child v).head (destSlots i) = 1 ∧
    (output child v).tape (destSlots i) = RadixZeroFill.encodedBinary (child i.succ) := by
  have h := BinaryDescriptorReplaceList.output_dest instructions unique (generated child) v
    (instruction i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
  fin_cases i <;> simpa [output,instruction,sourceSlots,destSlots,generated] using h

theorem unchanged_A (child : Fin 6 → List Bool) (v : Tapes 38 q) :
    (output child v).head 3 = v.head 3 ∧ (output child v).tape 3 = v.tape 3 :=
  BinaryDescriptorReplaceList.output_frame instructions (generated child) v 3 (by decide)

/-- Apply the replacement machine to the actual clean child-dimension output.
All source and occupied-destination conditions are discharged here. -/
theorem generated_hoare (hq : 2 ≤ q) (v : RecursiveInterchangeLayout.Descriptor)
    (hs : Fin 6 → List Bool) (bs rs : List Bool) (b : ℕ) {m : ℕ} (i j : Fin m) :
    let ch := RecursiveChildDimensions.childHeaders (q := q) v hs bs rs b i j
    let bank := RecursiveChildDimensionsClean.output hq v hs bs rs b i j
    HoareTime (program q) (fun w => w = bank) (fun w => w = output ch bank)
      (BinaryDescriptorReplaceList.cost instructions (words hs) (generated ch)) := by
  apply installs
  · intro z
    have h := RecursiveChildDimensionsClean.output_headers hq v hs bs rs b i j z.succ
    fin_cases z <;> exact h
  · intro z
    fin_cases z <;> exact ⟨rfl,rfl⟩

/-- Five actual replacements, including erasure of all old header bits. -/
theorem cost_le (old child : Fin 6 → List Bool) (L : ℕ)
    (ho : ∀ i, (old i).length ≤ L) (hn : ∀ i, (child i).length ≤ L) :
    BinaryDescriptorReplaceList.cost instructions (words old) (generated child) ≤ 20*L+56 := by
  have h := BinaryDescriptorReplaceList.cost_le instructions (words old) (generated child) L
    (by
      intro op hop
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hop
      have hh := ho i.succ
      fin_cases i <;> simpa [words,instruction,destSlots] using hh)
    (by
      intro op hop
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hop
      have hh := hn i.succ
      fin_cases i <;> simpa [generated,instruction,sourceSlots] using hh)
  simp only [instructions,List.length_ofFn] at h ⊢
  omega

/-- Installing actual canonical child headers has linear child-volume cost,
including the destruction of the old parent headers. -/
theorem installs_linear {roles m n d k : ℕ}
    {root parent child : RecursiveInterchangeLayout.Descriptor}
    (current : RecursiveInterchangeVolume.Path q roles m root n child)
    (older : RecursiveInterchangeVolume.Path q roles m root d parent)
    (hq : 2 ≤ q) (hr : 0 < roles) (hm : 2 ≤ m)
    (hw : root.width = m^k) (hv : root.Positive)
    (old new : Fin 6 → List Bool) (ho : RecursiveDimensionBank.Headers parent old)
    (hn : RecursiveDimensionBank.Headers child new) (v : Tapes 38 q)
    (hs : ∀ i : Fin 5, v.head (sourceSlots i) = 1 ∧
      v.tape (sourceSlots i) = RadixZeroFill.encodedBinary (new i.succ))
    (hd : ∀ i : Fin 5, v.head (destSlots i) = 1 ∧
      v.tape (destSlots i) = RadixZeroFill.encodedBinary (old i.succ)) :
    HoareTime (program q) (fun w => w = v) (fun w => w = output new v)
      ((40*(Nat.log2 roles+2)+56)*RecursiveInterchangeLayout.volume q child) := by
  have hcost := cost_le old new (2*(Nat.log2 roles+2)*RecursiveInterchangeLayout.volume q child)
    (RecursiveHeaderBounds.saved_header_length_le current older hq hr hm hw hv old ho)
    (RecursiveHeaderBounds.header_length_le current hq hr hm hw hv new hn)
  have hp := current.original_chunks (by omega) hr hv
  have hV : 0 < RecursiveInterchangeLayout.volume q child :=
    lt_of_lt_of_le (pow_pos (by omega : 0 < q) _) hp
  apply (installs old new v hs hd).consequence (fun _ h => h) (fun _ h => h)
  nlinarith

end
end IntegerMultBounds.Machine.RecursiveChildHeaderInstall
