import IntegerMultBounds.Machine.ArbitrarySliceDimensions
import IntegerMultBounds.Machine.RecursiveViewFrame
import IntegerMultBounds.Machine.BinaryDescriptorReplaceList

/-! Paid save, synthesis, header installation and restoration for an arbitrary
slice view. All six original headers are saved on a dedicated physical stack;
occupied changing headers are erased before copying their replacements. -/
namespace IntegerMultBounds.Machine.ArbitrarySliceHeaders
open RecursiveInterchangeLayout (Descriptor volume)
open BinaryDescriptorInstallMarkedList
variable {q : ℕ}
noncomputable section

/-- Eighteen tapes: the slice-dimension bank followed by its header stack. -/
def canonical (hs : Fin 6 → List Bool) (ts bs : List Bool) (st : Tapes 1 q) : Tapes 18 q :=
  (ArbitrarySliceDimensions.input hs ts bs).append st

def prepared (hs : Fin 6 → List Bool) (ts bs : List Bool) (v : Descriptor) (t b : ℕ)
    (st : Tapes 1 q) : Tapes 18 q :=
  canonical (ArbitrarySliceDimensions.headers (q := q) hs bs v t b) ts bs (RecursiveViewFrame.savedStack hs st)

def framePlacement : Fin (7+11) ≃ Fin 18 where
  toFun := ![0,1,2,3,4,5,17,6,7,8,9,10,11,12,13,14,15,16]
  invFun := ![0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,6]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def pushProgram := Placement.placed (RecursiveViewFrame.pushProgram (q := q)) framePlacement
def restoreProgram := Placement.placed (RecursiveViewFrame.restoreProgram (q := q)) framePlacement

private theorem placed_exact {s u t r cost : ℕ} {M : Program s r q}
    (e : Fin (s+u) ≃ Fin t) (v w : Tapes t q) (small small' : Tapes s q)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

private theorem frame_active (hs : Fin 6 → List Bool) (ts bs : List Bool) (st : Tapes 1 q) :
    Placement.active framePlacement (canonical hs ts bs st) = RecursiveViewFrame.bank hs st := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem frame_extra (hs hs' : Fin 6 → List Bool) (ts bs : List Bool) (st st' : Tapes 1 q) :
    Placement.extra framePlacement (canonical hs ts bs st) = Placement.extra framePlacement (canonical hs' ts bs st') := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [framePlacement,canonical,ArbitrarySliceDimensions.input,ArbitrarySliceDimensions.bank,Tapes.append,Fin.addCases] <;> rfl

theorem push_hoare (hs : Fin 6 → List Bool) (ts bs : List Bool) (st : Tapes 1 q) :
    HoareTime (pushProgram (q := q)) (fun z => z = canonical hs ts bs st)
      (fun z => z = canonical hs ts bs (RecursiveViewFrame.savedStack hs st)) (RecursiveViewFrame.pushCost hs) :=
  placed_exact framePlacement _ _ _ _ (frame_active _ _ _ _) (frame_active _ _ _ _)
    (frame_extra _ _ _ _ _ _) (RecursiveViewFrame.push_hoare hs st)

/-- Restore works after any slice call that has returned its headers and
scratch bank. The old stack contents are recovered exactly from the saved frame. -/
theorem restore_hoare (old current : Fin 6 → List Bool) (ts bs : List Bool) (st : Tapes 1 q)
    (hf : RecursiveViewFrame.Free old st) :
    HoareTime (restoreProgram (q := q))
      (fun z => z = canonical current ts bs (RecursiveViewFrame.savedStack old st))
      (fun z => z = canonical old ts bs st) (RecursiveViewFrame.restoreCost old current) :=
  placed_exact framePlacement _ _ _ _ (frame_active _ _ _ _) (frame_active _ _ _ _)
    (frame_extra _ _ _ _ _ _) (RecursiveViewFrame.restore_hoare old current st hf)

def sourceSlots : Fin 4 → Fin 17 := ![10,7,12,13]
def destSlots : Fin 4 → Fin 17 := ![2,3,4,5]
def instruction (i : Fin 4) : Instruction 17 := ⟨sourceSlots i,destSlots i,by fin_cases i <;> decide⟩
def instructions := List.ofFn instruction

theorem disjoint : Disjoint instructions := by
  intro a ha b hb
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
  fin_cases i <;> fin_cases j <;> decide

theorem unique : Unique instructions := by
  unfold BinaryDescriptorInstallMarkedList.Unique instructions
  decide

def oldWords (hs : Fin 6 → List Bool) (i : Fin 17) : List Bool :=
  if i = 2 then hs 2 else if i = 3 then hs 3 else if i = 4 then hs 4 else if i = 5 then hs 5 else []
def newWords (hs : Fin 6 → List Bool) (i : Fin 17) : List Bool :=
  if i = 10 then hs 2 else if i = 7 then hs 3 else if i = 12 then hs 4 else if i = 13 then hs 5 else []

def replacements := BinaryDescriptorReplaceList.program (q := q) (by decide : 0 < 17) instructions
private def generatedSlots : List (Fin 17) := [10,12,13]
def handoffProgram := seq (replacements (q := q))
  (BinaryDescriptorCleanupList.program (a := q) (by decide : 0 < 17) generatedSlots)

def installed (child : Fin 6 → List Bool) (v : Tapes 17 q) :=
  BinaryDescriptorReplaceList.output instructions (newWords child) v

def handedOff (child : Fin 6 → List Bool) (v : Tapes 17 q) :=
  BinaryDescriptorCleanupList.cleared generatedSlots (installed child v)

def handoffCost (old child : Fin 6 → List Bool) :=
  BinaryDescriptorReplaceList.cost instructions (oldWords old) (newWords child)+1+
    BinaryDescriptorCleanupList.cost generatedSlots (newWords child)

private theorem install_hoare (old child : Fin 6 → List Bool) (v : Tapes 17 q)
    (hs : ∀ i : Fin 4, v.head (sourceSlots i) = 1 ∧
      v.tape (sourceSlots i) = RadixZeroFill.encodedBinary (child ⟨i.val+2,by omega⟩))
    (hd : ∀ i : Fin 4, v.head (destSlots i) = 1 ∧
      v.tape (destSlots i) = RadixZeroFill.encodedBinary (old ⟨i.val+2,by omega⟩)) :
    HoareTime (replacements (q := q)) (fun z => z = v) (fun z => z = installed child v)
      (BinaryDescriptorReplaceList.cost instructions (oldWords old) (newWords child)) := by
  apply BinaryDescriptorReplaceList.replaces_hoare (by decide) instructions disjoint unique
    (oldWords old) (newWords child) v
  · intro op hop
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hop
    have hh := hs i
    fin_cases i <;> simpa [instruction,sourceSlots,newWords] using hh
  · intro op hop
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hop
    have hh := hd i
    fin_cases i <;> simpa [instruction,destSlots,oldWords] using hh

private theorem handoff_hoare (old child : Fin 6 → List Bool) (v : Tapes 17 q)
    (hs : ∀ i : Fin 4, v.head (sourceSlots i) = 1 ∧
      v.tape (sourceSlots i) = RadixZeroFill.encodedBinary (child ⟨i.val+2,by omega⟩))
    (hd : ∀ i : Fin 4, v.head (destSlots i) = 1 ∧
      v.tape (destSlots i) = RadixZeroFill.encodedBinary (old ⟨i.val+2,by omega⟩)) :
    HoareTime (handoffProgram (q := q)) (fun z => z = v) (fun z => z = handedOff child v)
      (handoffCost old child) := by
  have hi := install_hoare old child v hs hd
  have hc := BinaryDescriptorCleanupList.cleanup_hoare (by decide : 0 < 17) generatedSlots (by decide)
    (newWords child) (installed child v) (by
      intro i hi
      have hn : i ∉ BinaryDescriptorReplaceList.destinations instructions := by
        simp only [generatedSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl <;> decide
      have hf := BinaryDescriptorReplaceList.output_frame instructions (newWords child) v i hn
      change (installed child v).head i = v.head i ∧ (installed child v).tape i = v.tape i at hf
      rw [hf.1,hf.2]
      simp only [generatedSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl
      · simpa [sourceSlots,newWords,BinaryDescriptorStackRoundtrip.descriptor_encoded] using hs 0
      · simpa [sourceSlots,newWords,BinaryDescriptorStackRoundtrip.descriptor_encoded] using hs 2
      · simpa [sourceSlots,newWords,BinaryDescriptorStackRoundtrip.descriptor_encoded] using hs 3)
  exact hi.seq hc

private theorem handedOff_exact (hs : Fin 6 → List Bool) (ts bs : List Bool) (v : Descriptor) (t b : ℕ) :
    handedOff (q := q) (ArbitrarySliceDimensions.headers (q := q) hs bs v t b)
      (ArbitrarySliceDimensions.output hs ts bs v t b) =
      ArbitrarySliceDimensions.input (ArbitrarySliceDimensions.headers (q := q) hs bs v t b) ts bs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem generated_handoff (hs : Fin 6 → List Bool) (ts bs : List Bool) (v : Descriptor) (t b : ℕ) :
    HoareTime (handoffProgram (q := q))
      (fun z => z = ArbitrarySliceDimensions.output hs ts bs v t b)
      (fun z => z = ArbitrarySliceDimensions.input (ArbitrarySliceDimensions.headers (q := q) hs bs v t b) ts bs)
      (handoffCost hs (ArbitrarySliceDimensions.headers (q := q) hs bs v t b)) := by
  have h := handoff_hoare (q := q) hs (ArbitrarySliceDimensions.headers (q := q) hs bs v t b)
    (ArbitrarySliceDimensions.output hs ts bs v t b)
    (by intro i; fin_cases i <;> exact ⟨rfl,rfl⟩)
    (by intro i; fin_cases i <;> exact ⟨rfl,rfl⟩)
  simpa only [handedOff_exact] using h

private theorem handoffCost_le (old child : Fin 6 → List Bool) (L : ℕ)
    (ho : ∀ i, (old i).length ≤ L) (hc : ∀ i, (child i).length ≤ L) :
    handoffCost old child ≤ 22*L+61 := by
  have hi := BinaryDescriptorReplaceList.cost_le instructions (oldWords old) (newWords child) L
    (by
      intro op hop
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hop
      have hh := ho ⟨i.val+2,by omega⟩
      fin_cases i <;> simpa [instruction,destSlots,oldWords] using hh)
    (by
      intro op hop
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hop
      have hh := hc ⟨i.val+2,by omega⟩
      fin_cases i <;> simpa [instruction,sourceSlots,newWords] using hh)
  have he := BinaryDescriptorCleanupList.cost_le generatedSlots (newWords child) L (by
    intro i hi
    simp only [generatedSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl
    · simpa [newWords] using hc 2
    · simpa [newWords] using hc 4
    · simpa [newWords] using hc 5)
  simp only [instructions,List.length_ofFn] at hi
  simp only [generatedSlots,List.length_cons,List.length_nil] at he
  unfold handoffCost
  dsimp only [instructions,generatedSlots]
  omega

def prepareProgram (hq : 2 ≤ q) := seq (seq (pushProgram (q := q))
  (extend (ArbitrarySliceDimensions.program hq) 1)) (extend (handoffProgram (q := q)) 1)

private theorem header_length (hq : 2 ≤ q) (v : Descriptor) (hp : v.Positive)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs) (i : Fin 6) :
    (hs i).length ≤ 2*volume q v := by
  have hw := RecursiveAffinePrepare.header_log hq v hp hs hv i
  have hl := Nat.log2_le_self (volume q v)
  have hV := RecursiveAffinePrepare.volume_positive hq v hp
  omega

/-- Save the six old headers, synthesize actual slice dimensions, erase occupied
changing headers, copy replacements, and erase the three generated copies. -/
theorem prepares (hq : 2 ≤ q) (hs : Fin 6 → List Bool) (ts bs : List Bool)
    (v : Descriptor) (t b : ℕ) (st : Tapes 1 q)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive)
    (ht : Counter.value ts = t) (hb : Counter.value bs = b)
    (ct : GrowingCounterData.Canonical ts) (cb : GrowingCounterData.Canonical bs)
    (hfit : t+b ≤ v.width) :
    HoareTime (prepareProgram hq) (fun z => z = canonical hs ts bs st)
      (fun z => z = prepared hs ts bs v t b st) (900*volume q v) := by
  let child := ArbitrarySliceDimensions.headers (q := q) hs bs v t b
  have hd := hoare_extend_eq (ArbitrarySliceDimensions.construct_hoare hq hs ts bs v t b hv hp ht hb ct cb hfit)
    (RecursiveViewFrame.savedStack hs st)
  have hh := hoare_extend_eq (generated_handoff (q := q) hs ts bs v t b) (RecursiveViewFrame.savedStack hs st)
  have h := ((push_hoare hs ts bs st).seq hd).seq hh
  have hc : RecursiveDimensionBank.Headers (ArbitraryWidthPieces.slice q v t b) child :=
    ArbitrarySliceDimensions.headers_valid hs bs v t b hv hb cb
  have hpchild := ArbitraryWidthPieces.slice_positive q (by omega) v hp t b
  have hvchild := ArbitraryWidthPieces.slice_volume q v t b hfit
  have wo : ∀ i, (hs i).length ≤ 2*volume q v := header_length hq v hp hs hv
  have wn : ∀ i, (child i).length ≤ 2*volume q v := by
    intro i
    simpa only [hvchild] using header_length hq _ hpchild child hc i
  have hpCost := RecursiveViewFrame.pushCost_le hs _ wo
  have hiCost := handoffCost_le hs child _ wo wn
  have hV := RecursiveAffinePrepare.volume_positive hq v hp
  apply h.consequence (fun _ h => h) (fun _ h => h) _
  change RecursiveViewFrame.pushCost hs+1+700*volume q v+1+handoffCost hs child ≤ _
  omega

/-- Restoration erases the returned slice headers and pops every saved field,
returning all stack cells and all scratch tapes to their original contents. -/
theorem restores (hq : 2 ≤ q) (hs : Fin 6 → List Bool) (ts bs : List Bool)
    (v : Descriptor) (t b : ℕ) (st : Tapes 1 q)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive)
    (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs)
    (hfit : t+b ≤ v.width) (hf : RecursiveViewFrame.Free hs st) :
    HoareTime (restoreProgram (q := q)) (fun z => z = prepared hs ts bs v t b st)
      (fun z => z = canonical hs ts bs st) (128*volume q v) := by
  let child := ArbitrarySliceDimensions.headers (q := q) hs bs v t b
  have hc : RecursiveDimensionBank.Headers (ArbitraryWidthPieces.slice q v t b) child :=
    ArbitrarySliceDimensions.headers_valid hs bs v t b hv hb cb
  have hpchild := ArbitraryWidthPieces.slice_positive q (by omega) v hp t b
  have hvchild := ArbitraryWidthPieces.slice_volume q v t b hfit
  have wo : ∀ i, (hs i).length ≤ 2*volume q v := header_length hq v hp hs hv
  have wn : ∀ i, (child i).length ≤ 2*volume q v := by
    intro i
    simpa only [hvchild] using header_length hq _ hpchild child hc i
  have hcCost := RecursiveViewFrame.restoreCost_le hs child _ wo wn
  have hV := RecursiveAffinePrepare.volume_positive hq v hp
  exact (restore_hoare hs child ts bs st hf).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.ArbitrarySliceHeaders
