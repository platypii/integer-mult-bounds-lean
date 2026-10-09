import IntegerMultBounds.Machine.Gather
import IntegerMultBounds.Machine.BinaryDescriptorDifference
import IntegerMultBounds.Machine.InjectivePlacement

/-! Four actual descriptor subtractions construct the two gather suffixes.
The fixed ten-tape machine retains the six original runtime dimensions and
cleans every generated header, including zero-valued marked descriptors. -/
namespace IntegerMultBounds.Machine.CountedGatherMetadata
noncomputable section
variable {a : ℕ}
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)

/-- Originals are sx, ox, d, st, ot, n. -/
def originalValues (S : Gather.Shape) (n : ℕ) : Fin 6 → ℕ := ![S.sx,S.ox,S.d,S.st,S.ot,n]
def values (S : Gather.Shape) : Fin 4 → ℕ := ![S.sx-S.ox,S.sx-S.ox-S.d,S.st-S.ot,S.st-S.ot-S.d]
def words (S : Gather.Shape) (i : Fin 4) := bits (values S i)

def state (S : Gather.Shape) (hs : Fin 6 → List Bool) (stage : ℕ) : Tapes 10 a :=
  ⟨fun i => if i.val < 6 then 1 else if i.val < 6+stage then 1 else 0,
   fun i => if h : i.val < 6 then RadixZeroFill.encodedBinary (hs ⟨i.val,h⟩)
     else if h' : i.val < 6+stage ∧ i.val < 10 then
       RadixZeroFill.encodedBinary (words S ⟨i.val-6,by omega⟩) else fun _ => blank⟩

def input (hs : Fin 6 → List Bool) : Tapes 10 a :=
  ⟨fun i => if i.val < 6 then 1 else 0,
   fun i => if h : i.val < 6 then RadixZeroFill.encodedBinary (hs ⟨i.val,h⟩) else fun _ => blank⟩
def output (S : Gather.Shape) (hs : Fin 6 → List Bool) := state (a := a) S hs 4

theorem state_zero (S : Gather.Shape) (hs : Fin 6 → List Bool) : state (a := a) S hs 0 = input hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def slots (k : Fin 4) : Fin 3 → Fin 10 :=
  ![![0,1,6],![6,2,7],![3,4,8],![8,2,9]] k

theorem slots_injective (k : Fin 4) : Function.Injective (slots k) := by
  intro i j h
  fin_cases k <;> fin_cases i <;> fin_cases j <;> first | rfl | norm_num [slots] at h

def placement (k : Fin 4) : Fin (3+7) ≃ Fin 10 :=
  InjectivePlacement.placement (slots k) (slots_injective k) (by decide)
@[simp] theorem active_slot (k : Fin 4) (i : Fin 3) :
    placement k (Fin.castAdd 7 i) = slots k i := InjectivePlacement.active_slot _ _ _ _
def stageProgram (k : Fin 4) := Placement.placed (BinaryDescriptorDifference.program (a := a)) (placement k)
def program := seq (seq (seq (stageProgram (a := a) 0) (stageProgram 1)) (stageProgram 2)) (stageProgram 3)

def leftWord (S : Gather.Shape) (hs : Fin 6 → List Bool) : Fin 4 → List Bool :=
  ![hs 0,words S 0,hs 3,words S 2]
def rightWord (hs : Fin 6 → List Bool) : Fin 4 → List Bool := ![hs 1,hs 2,hs 4,hs 2]
def width (S : Gather.Shape) : Fin 4 → ℕ := ![S.sx,S.sx,S.st,S.st]

theorem words_value (S : Gather.Shape) (i : Fin 4) : Counter.value (words S i) = values S i :=
  RecursiveChildQuotientsConstant.bits_value _
theorem words_canonical (S : Gather.Shape) (i : Fin 4) : GrowingCounterData.Canonical (words S i) :=
  RecursiveChildQuotientsConstant.bits_canonical _

private theorem encoded_binary (bs : List Bool) : RadixZeroFill.encodedBinary (q := a) bs =
    CountedLoopReuseAlphabet.binary bs := by
  change (fun j => (CountedLoopReuseAlphabet.encoding a).encode (CountedCopyReuse.binary bs j)) = _
  exact CountedLoopReuseAlphabet.encoding_binary bs

private theorem encoded_descriptor (bs : List Bool) : RadixZeroFill.encodedBinary (q := a) bs =
    BinaryDescriptorStack.descriptor bs := (BinaryDescriptorStackRoundtrip.descriptor_encoded bs).symm

private theorem active_before (S : Gather.Shape) (hs : Fin 6 → List Bool) (k : Fin 4) :
    Placement.active (placement k) (state (a := a) S hs k.val) =
      BinaryDescriptorDifference.input (leftWord S hs k) (rightWord hs k) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [active_slot]
  all_goals fin_cases k <;> fin_cases i
  all_goals first | rfl | exact encoded_binary _

private theorem active_after (S : Gather.Shape) (hs : Fin 6 → List Bool) (k : Fin 4) :
    Placement.active (placement k) (state (a := a) S hs (k.val+1)) =
      BinaryDescriptorDifference.output (leftWord S hs k) (rightWord hs k) (words S k) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [active_slot]
  all_goals fin_cases k <;> fin_cases i
  all_goals first | rfl | exact encoded_binary _ | exact encoded_descriptor _

private theorem extra_ne (k : Fin 4) (i : Fin 7) (j : Fin 3) :
    placement k (Fin.natAdd 3 i) ≠ slots k j := by
  intro h
  rw [← active_slot k j] at h
  have hv := congrArg Fin.val ((placement k).injective h)
  simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
  have hj := j.isLt
  omega

private theorem extra_unchanged (S : Gather.Shape) (hs : Fin 6 → List Bool) (k : Fin 4) :
    Placement.extra (placement k) (state (a := a) S hs k.val) =
      Placement.extra (placement k) (state (a := a) S hs (k.val+1)) := by
  have he (i : Fin 10) (hi : i ≠ slots k 2) :
      (state (a := a) S hs k.val).head i = (state (a := a) S hs (k.val+1)).head i ∧
      (state (a := a) S hs k.val).tape i = (state S hs (k.val+1)).tape i := by
    fin_cases k <;> fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact (hi rfl).elim
  apply congrArg₂ Tapes.mk <;> funext i
  · exact (he _ (extra_ne k i 2)).1
  · exact (he _ (extra_ne k i 2)).2

private theorem operand_specs (S : Gather.Shape) (n : ℕ) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = originalValues S n i) (k : Fin 4) :
    Counter.value (rightWord hs k) ≤ Counter.value (leftWord S hs k) ∧
    Counter.value (leftWord S hs k)-Counter.value (rightWord hs k) = values S k ∧
    Counter.value (leftWord S hs k) ≤ width S k := by
  have h0 := hv 0; have h1 := hv 1; have h2 := hv 2
  have h3 := hv 3; have h4 := hv 4
  change Counter.value (hs 0) = S.sx at h0
  change Counter.value (hs 1) = S.ox at h1
  change Counter.value (hs 2) = S.d at h2
  change Counter.value (hs 3) = S.st at h3
  change Counter.value (hs 4) = S.ot at h4
  have hx := S.hx; have ht := S.ht
  fin_cases k <;> simp [leftWord,rightWord,words_value,values,width,h0,h1,h2,h3,h4] <;> omega

private theorem left_canonical (S : Gather.Shape) (hs : Fin 6 → List Bool)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (k : Fin 4) :
    GrowingCounterData.Canonical (leftWord S hs k) := by
  fin_cases k
  · exact hc 0
  · exact words_canonical S 0
  · exact hc 3
  · exact words_canonical S 2
private theorem right_canonical (hs : Fin 6 → List Bool)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (k : Fin 4) :
    GrowingCounterData.Canonical (rightWord hs k) := by
  fin_cases k
  · exact hc 1
  · exact hc 2
  · exact hc 4
  · exact hc 2

private theorem stage_hoare (S : Gather.Shape) (n : ℕ) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = originalValues S n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (k : Fin 4) :
    HoareTime (stageProgram (a := a) k) (fun v => v = state S hs k.val)
      (fun v => v = state S hs (k.val+1)) (6*width S k+27) := by
  obtain ⟨hle,hvalue,hwidth⟩ := operand_specs S n hs hv k
  have h := BinaryDescriptorDifference.difference_linear (a := a) (leftWord S hs k) (rightWord hs k)
    hle (left_canonical S hs hc k) (right_canonical hs hc k)
  rw [hvalue] at h
  change HoareTime _ _ (fun v => v = BinaryDescriptorDifference.output _ _ (words S k)) _ at h
  have hh := Placement.hoare_at h (placement k) (state S hs k.val) (active_before S hs k)
  apply hh.consequence (fun _ h => h) _ (by omega)
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,extra_unchanged,← active_after]
  exact Placement.view _ _

def constructCost (S : Gather.Shape) := 12*(S.sx+S.st)+111

theorem constructs (S : Gather.Shape) (n : ℕ) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = originalValues S n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun v => v = input hs)
      (fun v => v = output S hs) (constructCost S) := by
  have h := (((stage_hoare (a := a) S n hs hv hc 0).seq (stage_hoare S n hs hv hc 1)).seq
    (stage_hoare S n hs hv hc 2)).seq (stage_hoare S n hs hv hc 3)
  change HoareTime _ (fun v => v = state S hs 0) (fun v => v = state S hs 4) _ at h
  rw [state_zero] at h
  apply h.consequence (fun _ h => h) (fun _ h => h)
  norm_num [width,constructCost]
  omega

theorem original_cells (S : Gather.Shape) (hs : Fin 6 → List Bool) (i : Fin 6) :
    (output (a := a) S hs).head (Fin.castAdd 4 i) = 1 ∧
    (output (a := a) S hs).tape (Fin.castAdd 4 i) = RadixZeroFill.encodedBinary (hs i) := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

theorem generated_cells (S : Gather.Shape) (hs : Fin 6 → List Bool) (i : Fin 4) :
    (output (a := a) S hs).head (Fin.natAdd 6 i) = 1 ∧
    (output (a := a) S hs).tape (Fin.natAdd 6 i) = RadixZeroFill.encodedBinary (words S i) := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

/-- The retained input n remains available separately to the outer loop. -/
def digitSources : Fin 5 → Fin 10 := ![1,4,2,7,9]
def digitWords (S : Gather.Shape) (hs : Fin 6 → List Bool) : Fin 5 → List Bool :=
  ![hs 1,hs 4,hs 2,words S 1,words S 3]
def digitValues (S : Gather.Shape) : Fin 5 → ℕ :=
  ![S.ox,S.ot,S.d,S.sx-S.ox-S.d,S.st-S.ot-S.d]

theorem digit_cells (S : Gather.Shape) (hs : Fin 6 → List Bool) (i : Fin 5) :
    (output (a := a) S hs).head (digitSources i) = 1 ∧
    (output (a := a) S hs).tape (digitSources i) = RadixZeroFill.encodedBinary (digitWords S hs i) := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

theorem digit_values (S : Gather.Shape) (n : ℕ) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = originalValues S n i) :
    ∀ i, Counter.value (digitWords S hs i) = digitValues S i := by
  intro i; fin_cases i
  · exact hv 1
  · exact hv 4
  · exact hv 2
  · exact words_value S 1
  · exact words_value S 3

theorem digit_canonical (S : Gather.Shape) (hs : Fin 6 → List Bool)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    ∀ i, GrowingCounterData.Canonical (digitWords S hs i) := by
  intro i; fin_cases i
  · exact hc 1
  · exact hc 4
  · exact hc 2
  · exact words_canonical S 1
  · exact words_canonical S 3

def eraseSlots : List (Fin 10) := [6,7,8,9]
def cleanup := BinaryDescriptorCleanupList.program (a := a) (by decide : 0 < 10) eraseSlots
def wordsAt (S : Gather.Shape) (i : Fin 10) :=
  if h : 6 ≤ i.val then words S ⟨i.val-6,by omega⟩ else []
def cleanupCost (S : Gather.Shape) := BinaryDescriptorCleanupList.cost eraseSlots (wordsAt S)

private theorem eraseSlots_nodup : eraseSlots.Nodup := by decide

private theorem cleanup_descriptors (S : Gather.Shape) (hs : Fin 6 → List Bool)
    (i : Fin 10) (hi : i ∈ eraseSlots) :
    (output (a := a) S hs).head i = 1 ∧
    (output (a := a) S hs).tape i = BinaryDescriptorStack.descriptor (wordsAt S i) := by
  fin_cases i
  all_goals first | (simp [eraseSlots] at hi; done) | exact ⟨rfl,encoded_descriptor _⟩

private theorem cleared_eq (S : Gather.Shape) (hs : Fin 6 → List Bool) :
    BinaryDescriptorCleanupList.cleared eraseSlots (output (a := a) S hs) = input hs := by
  apply congrArg₂ Tapes.mk
  · funext i
    change (BinaryDescriptorCleanupList.cleared eraseSlots (output (a := a) S hs)).head i = (input (a := a) hs).head i
    by_cases hi : i ∈ eraseSlots
    · rw [(BinaryDescriptorCleanupList.cleared_slot eraseSlots eraseSlots_nodup _ i hi).1]
      fin_cases i <;> first | (simp [eraseSlots] at hi; done) | rfl
    · rw [(BinaryDescriptorCleanupList.cleared_frame eraseSlots _ i hi).1]
      fin_cases i <;> first | (simp [eraseSlots] at hi; done) | rfl
  · funext i
    change (BinaryDescriptorCleanupList.cleared eraseSlots (output (a := a) S hs)).tape i = (input (a := a) hs).tape i
    by_cases hi : i ∈ eraseSlots
    · rw [(BinaryDescriptorCleanupList.cleared_slot eraseSlots eraseSlots_nodup _ i hi).2]
      fin_cases i <;> first | (simp [eraseSlots] at hi; done) | rfl
    · rw [(BinaryDescriptorCleanupList.cleared_frame eraseSlots _ i hi).2]
      fin_cases i <;> first | (simp [eraseSlots] at hi; done) | rfl

/-- Physically erase all four generated outputs, including the two temporary
subtraction results. Every generated tape returns to blank with head zero. -/
theorem cleans (S : Gather.Shape) (hs : Fin 6 → List Bool) :
    HoareTime (cleanup (a := a)) (fun v => v = output S hs)
      (fun v => v = input hs) (cleanupCost S) := by
  have h := BinaryDescriptorCleanupList.cleanup_hoare (a := a) (by decide : 0 < 10)
    eraseSlots eraseSlots_nodup (wordsAt S) (output S hs) (cleanup_descriptors S hs)
  rw [cleared_eq] at h
  exact h

theorem cleanup_cost_bound (S : Gather.Shape) : cleanupCost S ≤ 4*(S.sx+S.st)+28 := by
  have hl (i : Fin 4) : (words S i).length ≤ values S i+1 := by
    have h := GrowingCounterData.canonical_width (words S i) (words_canonical S i)
    rw [words_value] at h
    exact h.trans (Nat.add_le_add_right (Nat.log2_le_self _) 1)
  have h0 := hl 0; have h1 := hl 1; have h2 := hl 2; have h3 := hl 3
  change (words S 0).length ≤ S.sx-S.ox+1 at h0
  change (words S 1).length ≤ S.sx-S.ox-S.d+1 at h1
  change (words S 2).length ≤ S.st-S.ot+1 at h2
  change (words S 3).length ≤ S.st-S.ot-S.d+1 at h3
  norm_num [cleanupCost,BinaryDescriptorCleanupList.cost,eraseSlots,wordsAt]
  omega

theorem cleans_linear (S : Gather.Shape) (hs : Fin 6 → List Bool) :
    HoareTime (cleanup (a := a)) (fun v => v = output S hs)
      (fun v => v = input hs) (4*(S.sx+S.st)+28) :=
  (cleans S hs).consequence (fun _ h => h) (fun _ h => h) (cleanup_cost_bound S)

/-- All-zero dimensions are permitted by the same program and contracts;
only the six original marked descriptors remain initialized at either end. -/
theorem construct_cost_volume (S : Gather.Shape) (V : ℕ) (hV : 0 < V) (hS : S.sx+S.st ≤ V) :
    constructCost S ≤ 123*V := by unfold constructCost; omega

theorem cleanup_cost_volume (S : Gather.Shape) (V : ℕ) (hV : 0 < V) (hS : S.sx+S.st ≤ V) :
    cleanupCost S ≤ 32*V := by have h := cleanup_cost_bound S; omega

end
end IntegerMultBounds.Machine.CountedGatherMetadata
