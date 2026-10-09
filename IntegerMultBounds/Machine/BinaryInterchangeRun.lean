import IntegerMultBounds.Machine.BinaryRadixEqualShared
import IntegerMultBounds.Machine.BinaryAdjacentWidthRun
import IntegerMultBounds.Machine.BinaryAdjacentWidthPrefixShared
import IntegerMultBounds.Machine.BinaryAdjacentWidthMovementShared
import IntegerMultBounds.Machine.BinaryAdjacentWidthInterchange
import IntegerMultBounds.Machine.BinaryAdjacentWidthSelectorDispatch

/-! Physical binary rectangular interchange from five caller-owned headers. -/
namespace IntegerMultBounds.Machine.BinaryInterchangeRun
noncomputable section
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open BinaryAdjacentWidthHeadersShared (Sources)
variable {t : ℕ}

def values (P G B h d : ℕ) : Fin 5 → ℕ := ![P,G,B,h,d]
def shortWords (hs : Fin 5 → List Bool) (i : Fin 5) : Fin 4 → List Bool :=
  ![hs 0,hs 1,hs 2,hs i]
def shortFocus (focus : Fin 5 → Fin t) (i : Fin 5) : Fin 4 → Fin t :=
  ![focus 0,focus 1,focus 2,focus i]
def prefixSlot (i : Fin t) := Fin.castAdd 17 (Fin.castAdd 1 i)
def middle (caller : Tapes t prime) :=
  BinaryRadixEqualShared.input (BinaryAdjacentWidthPrefixShared.input caller)
def bankInput (caller : Tapes t prime) := BinaryAdjacentWidthMovementShared.input (middle caller)
def input (caller : Tapes t prime) := (bankInput caller).append (FixedHeaderBankCopy.empty 1)

abbrev bankCount (t : ℕ) := (((((t+1)+17)+BinaryRadixEqualShared.count)+1)+17)+22
def slot (i : Fin t) : Fin (bankCount t+1) := Fin.castAdd 1 (Fin.castAdd 22
  (Fin.castAdd 17 (Fin.castAdd 1 (Fin.castAdd BinaryRadixEqualShared.count (prefixSlot i)))))
def flag : Fin (bankCount t+1) := Fin.natAdd (bankCount t) 0

theorem slot_injective : Function.Injective (slot (t := t)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  exact hv

theorem slot_ne_flag (i : Fin t) : slot i ≠ flag := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = bankCount t at hv
  have hroom : t ≤ bankCount t := by unfold bankCount; omega
  omega

theorem input_cells (caller : Tapes t prime) (i : Fin t) :
    (input caller).head (slot i) = caller.head i ∧ (input caller).tape (slot i) = caller.tape i := by
  simp only [input,bankInput,middle,BinaryAdjacentWidthMovementShared.input,
    BinaryRadixEqualShared.input,BinaryAdjacentWidthPrefixShared.input,BinaryAdjacentWidthHeadersShared.input,slot,prefixSlot,
    Tapes.append,Fin.addCases_left]
  exact ⟨trivial,trivial⟩

theorem flag_cells (caller : Tapes t prime) :
    (input caller).head flag = 0 ∧ (input caller).tape flag = fun _ => blank := by
  simp only [input,flag,Tapes.append,Fin.addCases_right]
  exact ⟨rfl,rfl⟩

def equalProgram (focus : Fin 5 → Fin t) (payload : Fin t) :=
  extend (extend (extend (extend (BinaryRadixEqualShared.program
    (fun i => prefixSlot (shortFocus focus 3 i)) (prefixSlot payload)) 1) 17) 22) 1

def longHProgram (focus : Fin 5 → Fin t) (payload : Fin t) :=
  extend (BinaryAdjacentWidthRun.longHProgram (shortFocus focus 4) payload) 1
def longDProgram (focus : Fin 5 → Fin t) (payload : Fin t) :=
  extend (BinaryAdjacentWidthRun.longDProgram (shortFocus focus 3) payload) 1

def program (focus : Fin 5 → Fin t) (payload : Fin t) (hi : Function.Injective focus) :=
  BinaryAdjacentWidthSelectorDispatch.program (slot (focus 3)) (slot (focus 4)) flag
    (fun h => (by decide : (3 : Fin 5) ≠ 4) (hi (slot_injective h)))
    (slot_ne_flag _) (slot_ne_flag _) (equalProgram focus payload)
    (longHProgram focus payload) (longDProgram focus payload)

def cost (P G B h d : ℕ) (hs : Fin 5 → List Bool) :=
  BinaryAdjacentWidthSelector.cost (hs 3) (hs 4)+1+
    BinaryAdjacentWidthSelectorDispatch.chosen h d
      (BinaryRadixEqualShared.cost P G B h (shortWords hs 3))
      (BinaryAdjacentWidthRun.cost P G B d (shortWords hs 4))
      (BinaryAdjacentWidthRun.cost P G B h (shortWords hs 3))

private theorem short_sources (caller : Tapes t prime) (focus : Fin 5 → Fin t)
    (hs : Fin 5 → List Bool)
    (ht : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (focus i) = 1) (j : Fin 5) :
    Sources caller (shortFocus focus j) (shortWords hs j) := by
  constructor
  · intro i; fin_cases i
    · exact ht 0
    · exact ht 1
    · exact ht 2
    · exact ht j
  · intro i; fin_cases i
    · exact hh 0
    · exact hh 1
    · exact hh 2
    · exact hh j

private theorem short_canonical (hs : Fin 5 → List Bool)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (j : Fin 5) :
    ∀ i, GrowingCounterData.Canonical (shortWords hs j i) := by
  intro i; fin_cases i
  · exact hc 0
  · exact hc 1
  · exact hc 2
  · exact hc j

private theorem prefix_sources (caller : Tapes t prime) (focus : Fin 4 → Fin t)
    (hs : Fin 4 → List Bool) (hsrc : Sources caller focus hs) :
    Sources (BinaryAdjacentWidthPrefixShared.input caller) (fun i => prefixSlot (focus i)) hs := by
  constructor
  · intro i
    simpa only [BinaryAdjacentWidthPrefixShared.input,prefixSlot,Tapes.append,Fin.addCases_left] using hsrc.tape i
  · intro i
    simpa only [BinaryAdjacentWidthPrefixShared.input,prefixSlot,Tapes.append,Fin.addCases_left] using hsrc.head i

/-- Equal-width branch on the same fully blank private layout as both adjacent branches. -/
theorem equal_runs (caller : Tapes t prime) (focus : Fin 5 → Fin t) (payload : Fin t)
    (P G B u : ℕ) (hs : Fin 5 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = values P G B u u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (htapes : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (hs i))
    (hheads : ∀ i, caller.head (focus i) = 1)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P (2^u) G (2^u) B) → Bool)
    (ht : caller.tape payload = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head payload = 0) :
    HoareTime (equalProgram focus payload) (fun z => z = input caller)
      (fun z => z = input (setTape caller payload
        (BinaryRadixRangePrepareAlphabet.word (BinaryAdjacentWidthInterchange.transpose (fun i => bitSymbol (x i)))) 0))
      (BinaryRadixEqualShared.cost P G B u (shortWords hs 3)) := by
  have hvalues : ∀ i, Counter.value (shortWords hs 3 i) = BinaryRadixRangePrepare.values P G B u i := by
    intro i; fin_cases i
    · exact hv 0
    · exact hv 1
    · exact hv 2
    · exact hv 3
  have hcanonical : ∀ i, GrowingCounterData.Canonical (shortWords hs 3 i) := by
    intro i; fin_cases i
    · exact hc 0
    · exact hc 1
    · exact hc 2
    · exact hc 3
  have hsources : Sources caller (shortFocus focus 3) (shortWords hs 3) := by
    constructor
    · intro i; fin_cases i
      · exact htapes 0
      · exact htapes 1
      · exact htapes 2
      · exact htapes 3
    · intro i; fin_cases i
      · exact hheads 0
      · exact hheads 1
      · exact hheads 2
      · exact hheads 3
  have h := BinaryRadixEqualShared.runs (BinaryAdjacentWidthPrefixShared.input caller)
    (fun i => prefixSlot (shortFocus focus 3 i)) (prefixSlot payload) P G B u (shortWords hs 3)
    hvalues hcanonical hP hG hB (prefix_sources caller _ _ hsources) x
    (by simp only [BinaryAdjacentWidthPrefixShared.input,prefixSlot,Tapes.append,Fin.addCases_left]; exact ht)
    (by simpa only [BinaryAdjacentWidthPrefixShared.input,prefixSlot,Tapes.append,Fin.addCases_left] using hh)
  simp only [BinaryAdjacentWidthPrefixShared.input,prefixSlot,SharedPlacementAlphabet.setTape_append_left] at h
  exact hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq h
    (FixedHeaderBankCopy.empty 1)) (FixedHeaderBankCopy.empty 17)) (FixedHeaderBankCopy.empty 22))
    (FixedHeaderBankCopy.empty 1)


/-- Actual longer-H branch from the original shorter-D descriptor. -/
theorem longH_runs (caller : Tapes t prime) (focus : Fin 5 → Fin t) (payload : Fin t)
    (P G B h d : ℕ) (hs : Fin 5 → List Bool) (hadj : h = d+1)
    (hv : ∀ i, Counter.value (hs i) = values P G B h d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (htapes : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (hs i))
    (hheads : ∀ i, caller.head (focus i) = 1)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B) → Bool)
    (ht : caller.tape payload = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head payload = 0) :
    HoareTime (longHProgram focus payload) (fun z => z = input caller)
      (fun z => z = input (setTape caller payload
        (BinaryRadixRangePrepareAlphabet.word (BinaryAdjacentWidthInterchange.transpose (fun i => bitSymbol (x i)))) 0))
      (BinaryAdjacentWidthRun.cost P G B d (shortWords hs 4)) := by
  subst h
  have hvalues : ∀ i, Counter.value (shortWords hs 4 i) = BinaryAdjacentWidthHeadersShared.values P G B d i := by
    intro i; fin_cases i
    · exact hv 0
    · exact hv 1
    · exact hv 2
    · exact hv 4
  revert ht; revert x
  rw [pow_succ, Nat.mul_comm (2^d) 2]
  intro x ht
  exact hoare_extend_eq (BinaryAdjacentWidthRun.longH_runs caller (shortFocus focus 4) payload
    P G B d (shortWords hs 4) hP hG hB hvalues (short_canonical hs hc 4)
    (short_sources caller focus hs htapes hheads 4) x ht hh) (FixedHeaderBankCopy.empty 1)

/-- Actual longer-D branch from the original shorter-H descriptor. -/
theorem longD_runs (caller : Tapes t prime) (focus : Fin 5 → Fin t) (payload : Fin t)
    (P G B h d : ℕ) (hs : Fin 5 → List Bool) (hadj : d = h+1)
    (hv : ∀ i, Counter.value (hs i) = values P G B h d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (htapes : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (hs i))
    (hheads : ∀ i, caller.head (focus i) = 1)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B) → Bool)
    (ht : caller.tape payload = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head payload = 0) :
    HoareTime (longDProgram focus payload) (fun z => z = input caller)
      (fun z => z = input (setTape caller payload
        (BinaryRadixRangePrepareAlphabet.word (BinaryAdjacentWidthInterchange.transpose (fun i => bitSymbol (x i)))) 0))
      (BinaryAdjacentWidthRun.cost P G B h (shortWords hs 3)) := by
  subst d
  have hvalues : ∀ i, Counter.value (shortWords hs 3 i) = BinaryAdjacentWidthHeadersShared.values P G B h i := by
    intro i; fin_cases i
    · exact hv 0
    · exact hv 1
    · exact hv 2
    · exact hv 3
  revert ht; revert x
  rw [pow_succ, Nat.mul_comm (2^h) 2]
  intro x ht
  exact hoare_extend_eq (BinaryAdjacentWidthRun.longD_runs caller (shortFocus focus 3) payload
    P G B h (shortWords hs 3) hP hG hB hvalues (short_canonical hs hc 3)
    (short_sources caller focus hs htapes hheads 3) x ht hh) (FixedHeaderBankCopy.empty 1)


/-- A concrete finite-control machine compares the two retained widths and
executes the appropriate verified branch, restoring every private tape. -/
theorem runs (caller : Tapes t prime) (focus : Fin 5 → Fin t) (payload : Fin t)
    (hi : Function.Injective focus) (P G B h d : ℕ) (hs : Fin 5 → List Bool)
    (hhd : h ≤ d+1) (hdh : d ≤ h+1)
    (hv : ∀ i, Counter.value (hs i) = values P G B h d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (htapes : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (hs i))
    (hheads : ∀ i, caller.head (focus i) = 1)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B) → Bool)
    (ht : caller.tape payload = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head payload = 0) :
    HoareTime (program focus payload hi) (fun z => z = input caller)
      (fun z => z = input (setTape caller payload
        (BinaryRadixRangePrepareAlphabet.word (BinaryAdjacentWidthInterchange.transpose (fun i => bitSymbol (x i)))) 0))
      (cost P G B h d hs) := by
  let out := input (setTape caller payload
    (BinaryRadixRangePrepareAlphabet.word (BinaryAdjacentWidthInterchange.transpose (fun i => bitSymbol (x i)))) 0)
  have hhv : Counter.value (hs 3) = h := hv 3
  have hdv : Counter.value (hs 4) = d := hv 4
  have he : Counter.value (hs 3) = Counter.value (hs 4) →
      HoareTime (equalProgram focus payload) (fun z => z = input caller) (fun z => z = out)
        (BinaryRadixEqualShared.cost P G B h (shortWords hs 3)) := by
    intro he
    have hed : h = d := by omega
    clear he hdv
    subst d
    exact equal_runs caller focus payload P G B h hs hv hc hP hG hB htapes hheads x ht hh
  have hlh : Counter.value (hs 4) < Counter.value (hs 3) →
      HoareTime (longHProgram focus payload) (fun z => z = input caller) (fun z => z = out)
        (BinaryAdjacentWidthRun.cost P G B d (shortWords hs 4)) := by
    intro hlt
    exact longH_runs caller focus payload P G B h d hs (by omega) hv hc hP hG hB htapes hheads x ht hh
  have hld : Counter.value (hs 3) < Counter.value (hs 4) →
      HoareTime (longDProgram focus payload) (fun z => z = input caller) (fun z => z = out)
        (BinaryAdjacentWidthRun.cost P G B h (shortWords hs 3)) := by
    intro hlt
    exact longD_runs caller focus payload P G B h d hs (by omega) hv hc hP hG hB htapes hheads x ht hh
  have hr := BinaryAdjacentWidthSelectorDispatch.runs (slot (focus 3)) (slot (focus 4)) flag
    (fun he => (by decide : (3 : Fin 5) ≠ 4) (hi (slot_injective he)))
    (slot_ne_flag _) (slot_ne_flag _) (equalProgram focus payload) (longHProgram focus payload)
    (longDProgram focus payload) (input caller) out out out
    (BinaryRadixEqualShared.cost P G B h (shortWords hs 3))
    (BinaryAdjacentWidthRun.cost P G B d (shortWords hs 4))
    (BinaryAdjacentWidthRun.cost P G B h (shortWords hs 3)) (hs 3) (hs 4)
    ((input_cells caller _).2.trans ((htapes 3).trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm)) ((input_cells caller _).1.trans (hheads 3))
    ((input_cells caller _).2.trans ((htapes 4).trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm)) ((input_cells caller _).1.trans (hheads 4))
    (flag_cells caller).2 (flag_cells caller).1 he hlh hld
  simpa only [program,cost,hhv,hdv,BinaryAdjacentWidthSelectorDispatch.chosen,ite_self] using hr

end
end IntegerMultBounds.Machine.BinaryInterchangeRun
