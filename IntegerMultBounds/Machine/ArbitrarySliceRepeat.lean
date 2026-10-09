import IntegerMultBounds.Machine.ArbitrarySliceStep
import IntegerMultBounds.Machine.ArbitrarySliceStepBudget
import IntegerMultBounds.Machine.BinaryCanonicalData

/-! Runtime-counted consecutive selected-slice calls. The runtime digit is
copied into a physically initialized countdown clock; the clock is erased at
the end. Every call runs the proved slice machine and actual offset advance. -/
namespace IntegerMultBounds.Machine.ArbitrarySliceRepeat
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ArbitrarySliceCall (bank data)

def offsets (b : ℕ) (ts : List Bool) : ℕ → List Bool
  | 0 => ts
  | i+1 => GrowingCounterData.advance b (offsets b ts i)

theorem offsets_value (b t i : ℕ) (ts : List Bool) (ht : Counter.value ts = t) :
    Counter.value (offsets b ts i) = t+i*b := by
  induction i with
  | zero => simpa [offsets] using ht
  | succ i ih => rw [offsets,GrowingCounterData.advance_value,ih]; ring

theorem offsets_canonical (b i : ℕ) (ts : List Bool) (ct : GrowingCounterData.Canonical ts) :
    GrowingCounterData.Canonical (offsets b ts i) := by
  induction i with
  | zero => exact ct
  | succ i ih => exact GrowingCounterData.advance_canonical b _ ih

theorem offsets_eq (b i : ℕ) (ts : List Bool) (ct : GrowingCounterData.Canonical ts) :
    offsets b ts i = GrowingCounterData.advance (i*b) ts :=
  BinaryCanonicalData.value_injective _ _ (offsets_canonical b i ts ct)
    (GrowingCounterData.advance_canonical _ _ ct) (by
      rw [offsets_value b (Counter.value ts) i ts rfl,GrowingCounterData.advance_value])

theorem offsets_length_le (b t i V : ℕ) (ts : List Bool) (ht : Counter.value ts = t)
    (ct : GrowingCounterData.Canonical ts) (hV : 0 < V) (hfit : t+i*b ≤ V) :
    (offsets b ts i).length ≤ 2*V := by
  have hw := GrowingCounterData.canonical_width (offsets b ts i) (offsets_canonical b i ts ct)
  rw [offsets_value b t i ts ht] at hw
  have hl := Nat.log2_le_self (t+i*b)
  omega

private theorem prefix_fit {v : Descriptor} (ws us : List ℕ) (t : ℕ)
    (h : t+(ws++us).sum ≤ v.width) : t+ws.sum ≤ v.width := by
  rw [List.sum_append] at h
  omega

private theorem suffix_fit {v : Descriptor} (ws us : List ℕ) (t : ℕ)
    (h : t+(ws++us).sum ≤ v.width) : t+ws.sum+us.sum ≤ v.width := by
  simpa [List.sum_append,Nat.add_assoc] using h

theorem run_append {v : Descriptor} {α : Type*} (ws us : List ℕ) (t : ℕ)
    (h : t+(ws++us).sum ≤ v.width) (x : Fin (volume prime v) → α) :
    ArbitraryWidthSchedule.run (ws++us) t h x =
      ArbitraryWidthSchedule.run us (t+ws.sum) (suffix_fit ws us t h)
        (ArbitraryWidthSchedule.run ws t (prefix_fit ws us t h) x) := by
  induction ws generalizing t x with
  | nil => simp [ArbitraryWidthSchedule.run]
  | cons w ws ih =>
    simp only [List.cons_append,ArbitraryWidthSchedule.run]
    rw [ih]
    simp only [List.sum_cons]
    congr 1; omega

def images (v : Descriptor) (t b i : ℕ) (h : t+i*b ≤ v.width)
    (x : Fin (volume prime v) → ZMod 2) :=
  ArbitraryWidthSchedule.run (List.replicate i b) t
    (by simpa [List.sum_replicate] using h) x

theorem images_zero (v : Descriptor) (t b : ℕ) (h : t+0*b ≤ v.width)
    (x : Fin (volume prime v) → ZMod 2) : images v t b 0 h x = x := rfl

private theorem run_eq {v : Descriptor} {α : Type*} (ws us : List ℕ) (he : ws = us)
    (t : ℕ) (hw : t+ws.sum ≤ v.width) (hu : t+us.sum ≤ v.width)
    (x : Fin (volume prime v) → α) :
    ArbitraryWidthSchedule.run ws t hw x = ArbitraryWidthSchedule.run us t hu x := by
  subst us
  rfl

theorem images_succ (v : Descriptor) (t b i : ℕ) (h : t+(i+1)*b ≤ v.width)
    (x : Fin (volume prime v) → ZMod 2) :
    images v t b (i+1) h x = ArbitraryWidthSliceTranspose.array (t+i*b) b
      (by nlinarith) (images v t b i (by nlinarith) x) := by
  have hf : t+(List.replicate i b++[b]).sum ≤ v.width := by
    simpa [List.sum_append,List.sum_replicate,Nat.add_mul,Nat.add_assoc] using h
  have hr := run_append (v := v) (List.replicate i b) [b] t hf x
  have he := run_eq (v := v) (List.replicate (i+1) b) (List.replicate i b++[b])
    List.replicate_succ' t (by simpa [List.sum_replicate] using h) hf x
  apply he.trans
  simp only [ArbitraryWidthSchedule.run] at hr
  convert hr using 2 <;> simp [List.sum_replicate,images]

abbrev sliceCount := ArbitrarySliceCall.tapeCount
abbrev tapeCount := sliceCount+2

def counted (v : Tapes sliceCount prime) (clock : ℤ → Fin (prime+4)) (p : ℤ)
    (as : List Bool) : Tapes tapeCount prime :=
  CountedLoopReuseAlphabet.bank v clock (CountedLoopReuseAlphabet.binary as) p 1

def input (v : Tapes sliceCount prime) (as : List Bool) : Tapes tapeCount prime := counted v (fun _ => blank) 0 as
def output (v : Tapes sliceCount prime) (as : List Bool) : Tapes tapeCount prime := input v as

def clockSlot : Fin tapeCount := Fin.natAdd sliceCount (0 : Fin 2)
def digitSlot : Fin tapeCount := Fin.natAdd sliceCount (1 : Fin 2)

private theorem clock_replace (v : Tapes sliceCount prime) (as : List Bool)
    (f g : ℤ → Fin (prime+4)) (p r : ℤ) :
    SharedPlacementAlphabet.setTape (counted v f p as) clockSlot g r = counted v g r as := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i =>
      have hn : Fin.castAdd 2 i ≠ clockSlot := by
        intro he
        have hh := congrArg Fin.val he
        simp only [clockSlot,Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero] at hh
        have := i.isLt
        omega
      change Function.update _ clockSlot _ (Fin.castAdd 2 i) = _
      rw [Function.update_of_ne hn]
      simp only [counted,
        CountedLoopReuseAlphabet.bank,Tapes.append,Fin.addCases_left]
  | right i =>
      by_cases hi : i = 0
      · subst i
        change Function.update _ clockSlot _ clockSlot = _
        rw [Function.update_self]
        simp only [Fin.addCases_right,CountedLoopReuseAlphabet.controls,ite_true]
      · have hn : Fin.natAdd sliceCount i ≠ clockSlot := by
          intro he
          have hh := congrArg Fin.val he
          simp only [clockSlot,Fin.val_natAdd,Fin.val_zero] at hh
          apply hi
          apply Fin.ext
          omega
        change Function.update _ clockSlot _ (Fin.natAdd sliceCount i) = _
        rw [Function.update_of_ne hn]
        simp only [counted,CountedLoopReuseAlphabet.bank,Tapes.append,Fin.addCases_right,
          CountedLoopReuseAlphabet.controls,ite_eq_right hi]

def initializeClock := Placement.placed (RecursiveChildQuotientsConstant.program (a := prime) 0)
  (FiniteReturnStackAt.placement clockSlot)
def cleanClock := BinaryDescriptorCleanupList.oneProgram (a := prime) clockSlot
def loop := CountedLoopReuseAlphabet.program ArbitrarySliceStep.program
def program := seq (seq initializeClock loop) cleanClock

private theorem initialize_hoare (v : Tapes sliceCount prime) (as : List Bool) :
    HoareTime initializeClock (fun w => w = input v as)
      (fun w => w = counted v CountedLoopReuseAlphabet.empty 1 as)
      (RecursiveChildQuotientsConstant.cost 0) := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := prime) 0)
    (FiniteReturnStackAt.placement clockSlot) (input v as)
    (by rw [FiniteReturnStackAt.active_bank];
        simp [input,counted,clockSlot,CountedLoopReuseAlphabet.bank,
          CountedLoopReuseAlphabet.controls,Tapes.append])
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  rw [FiniteReturnStackAt.replace_bank]
  unfold input
  rw [clock_replace]
  rfl

private theorem cleanup_hoare (v : Tapes sliceCount prime) (as : List Bool) :
    HoareTime cleanClock (fun w => w = counted v CountedLoopReuseAlphabet.empty 1 as)
      (fun w => w = output v as) 4 := by
  have h := BinaryDescriptorCleanupList.one_hoare clockSlot
    (counted v CountedLoopReuseAlphabet.empty 1 as) []
    (by simp [counted,clockSlot,CountedLoopReuseAlphabet.bank,
      CountedLoopReuseAlphabet.controls,Tapes.append]; rfl)
    (by simp [counted,clockSlot,CountedLoopReuseAlphabet.bank,
      CountedLoopReuseAlphabet.controls,Tapes.append])
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w rfl
  exact clock_replace v as _ _ _ _

def exactCost (depth V b a : ℕ) (ts bs as : List Bool) :=
  (∑ i ∈ Finset.range a, ArbitrarySliceStep.cost depth V b (offsets b ts i) bs)+
    6*a+7*as.length+16+RecursiveChildQuotientsConstant.cost 0+6

theorem repeat_hoare (depth : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool)
    (ts bs as : List Bool) (t b a : ℕ) (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (ht : Counter.value ts = t) (hb : Counter.value bs = b) (ha : Counter.value as = a)
    (ct : GrowingCounterData.Canonical ts) (cb : GrowingCounterData.Canonical bs)
    (hfit : t+a*b ≤ v.width) (hw : b = 125000^depth)
    (hr : Shared50TapeGlobal.roleCount^depth ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Shared50RecursiveCallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2) :
    HoareTime program (fun z => z = input (bank (data x) hs ts bs f p node scalar st frame) as)
      (fun z => z = output (bank (data (images v t b a hfit x)) hs
        (GrowingCounterData.advance (a*b) ts) bs f p node scalar st frame) as)
      (exactCost depth (volume prime v) b a ts bs as) := by
  let valid (i : ℕ) (hi : i ≤ a) : t+i*b ≤ v.width := by nlinarith
  let xs (i : ℕ) : Fin (volume prime v) → ZMod 2 :=
    if hi : i ≤ a then images v t b i (valid i hi) x else x
  let vs (i : ℕ) := bank (data (xs i)) hs (offsets b ts i) bs f p node scalar st frame
  have hi := initialize_hoare (bank (data x) hs ts bs f p node scalar st frame) as
  have hl := CountedLoopReuseAlphabet.loop_hoare ArbitrarySliceStep.program as a vs
    (fun i => ArbitrarySliceStep.cost depth (volume prime v) b (offsets b ts i) bs) ha (by
      intro i hia
      have hstep := ArbitrarySliceStep.step_hoare depth v hs (offsets b ts i) bs (t+i*b) b hp hv
        (offsets_value b t i ts ht) hb (offsets_canonical b i ts ct) cb (by nlinarith) hw hr
        f p node scalar st ready frame hfree (xs i)
      have hx : xs (i+1) = ArbitraryWidthSliceTranspose.array (t+i*b) b (by nlinarith) (xs i) := by
        simp only [xs,dite_eq_left (show i ≤ a by omega),dite_eq_left (show i+1 ≤ a by omega)]
        exact images_succ v t b i _ x
      simpa only [vs,offsets,hx] using hstep)
  have hzero : vs 0 = bank (data x) hs ts bs f p node scalar st frame := by
    simp [vs,xs,images,ArbitraryWidthSchedule.run,offsets]
  have hlast : vs a = bank (data (images v t b a hfit x)) hs
      (GrowingCounterData.advance (a*b) ts) bs f p node scalar st frame := by
    simp only [vs,xs,dite_eq_left (show a ≤ a by rfl),offsets_eq b a ts ct]
  rw [hzero,hlast] at hl
  have hc := cleanup_hoare (bank (data (images v t b a hfit x)) hs
    (GrowingCounterData.advance (a*b) ts) bs f p node scalar st frame) as
  exact ((hi.seq hl).seq hc).consequence (fun _ h => h) (fun _ h => h) (by unfold exactCost; omega)

def eraseDigit := BinaryDescriptorCleanupList.oneProgram (a := prime) digitSlot
def consume := seq program eraseDigit

theorem eraseDigit_hoare (v : Tapes sliceCount prime) (as : List Bool) :
    HoareTime eraseDigit (fun w => w = output v as)
      (fun w => w = v.append (SharedBank.empty 2 prime)) (2*as.length+4) := by
  have ht : (input v as).tape digitSlot = BinaryDescriptorStack.descriptor as := by
    simp only [input,counted,digitSlot,CountedLoopReuseAlphabet.bank,Tapes.append,
      Fin.addCases_right,CountedLoopReuseAlphabet.controls]
    change CountedLoopReuseAlphabet.binary as = BinaryDescriptorStack.descriptor as
    rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]
    change CountedLoopReuseAlphabet.binary as =
      (fun z => (RadixToBinary.binaryEncoding (q := prime)).encode (CountedCopyReuse.binary as z))
    exact (CountedLoopReuseAlphabet.encoding_binary (a := prime) as).symm
  have hh : (input v as).head digitSlot = 1 := by
    simp [input,counted,digitSlot,CountedLoopReuseAlphabet.bank,Tapes.append,CountedLoopReuseAlphabet.controls]
  have h := BinaryDescriptorCleanupList.one_hoare digitSlot (input v as) as ht hh
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w rfl
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i =>
      have hn : Fin.castAdd 2 i ≠ digitSlot := by
        intro he
        have hv := congrArg Fin.val he
        simp only [digitSlot,Fin.val_castAdd,Fin.val_natAdd,Fin.val_one] at hv
        have := i.isLt
        omega
      change Function.update _ digitSlot _ (Fin.castAdd 2 i) = _
      rw [Function.update_of_ne hn]
      simp only [input,counted,CountedLoopReuseAlphabet.bank,Tapes.append,Fin.addCases_left]
  | right i =>
      by_cases hi : i = 1
      · subst i
        change Function.update _ digitSlot _ digitSlot = _
        rw [Function.update_self]
        simp only [Fin.addCases_right,SharedBank.empty]
      · have hn : Fin.natAdd sliceCount i ≠ digitSlot := by
          intro he
          have hv := congrArg Fin.val he
          simp only [digitSlot,Fin.val_natAdd,Fin.val_one] at hv
          apply hi
          apply Fin.ext
          omega
        change Function.update _ digitSlot _ (Fin.natAdd sliceCount i) = _
        rw [Function.update_of_ne hn]
        have hz : i = 0 := by apply Fin.ext; have := i.isLt; have hh : i.val ≠ 1 := fun h => hi (Fin.ext h); omega
        subst i
        simp [input,counted,CountedLoopReuseAlphabet.bank,Tapes.append,CountedLoopReuseAlphabet.controls,SharedBank.empty]

/-- A bound for runtime-counted repetition, including its copied countdown,
initializer and clock cleanup, suitable for the digit-weighted piece budget. -/
theorem cost_bound (depth V b a : ℕ) (ts bs as : List Bool)
    (hV : 0 < V) (hb : b ≤ V) (hs : bs.length ≤ 2*V)
    (ht : ∀ i < a, (offsets b ts i).length ≤ 2*V) :
    exactCost depth V b a ts bs as ≤
      a*(ArbitrarySliceStepBudget.budget depth V+6)+7*as.length+28 := by
  have hsum : (∑ i ∈ Finset.range a, ArbitrarySliceStep.cost depth V b (offsets b ts i) bs) ≤
      a*ArbitrarySliceStepBudget.budget depth V := by
    calc
      _ ≤ ∑ _i ∈ Finset.range a, ArbitrarySliceStepBudget.budget depth V := by
        apply Finset.sum_le_sum
        intro i hi
        exact ArbitrarySliceStepBudget.cost_le depth V b _ bs hV hb (ht i (Finset.mem_range.mp hi)) hs
      _ = _ := by simp
  unfold exactCost
  have hc : RecursiveChildQuotientsConstant.cost 0 = 6 := rfl
  rw [hc]
  nlinarith

/-- Compose a proved repeated-call run with real digit erasure. The returned
slice bank is literal, and both appended controller tapes are now blank/head0. -/
theorem consume_hoare {v w : Tapes sliceCount prime} {as : List Bool} {bound : ℕ}
    (h : HoareTime program (fun z => z = input v as) (fun z => z = output w as) bound) :
    HoareTime consume (fun z => z = input v as)
      (fun z => z = w.append (SharedBank.empty 2 prime)) (bound+2*as.length+5) :=
  (h.seq (eraseDigit_hoare w as)).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem consumeCost_bound (depth V b a : ℕ) (ts bs as : List Bool)
    (hV : 0 < V) (hb : b ≤ V) (hs : bs.length ≤ 2*V)
    (ht : ∀ i < a, (offsets b ts i).length ≤ 2*V) :
    exactCost depth V b a ts bs as+2*as.length+5 ≤
      a*(ArbitrarySliceStepBudget.budget depth V+6)+9*as.length+33 := by
  have hh := cost_bound depth V b a ts bs as hV hb hs ht
  omega

theorem consumeCost_canonical (depth V t b a : ℕ) (ts bs as : List Bool)
    (hV : 0 < V) (hbV : b ≤ V) (hfit : t+a*b ≤ V)
    (ht : Counter.value ts = t) (hb : Counter.value bs = b)
    (ct : GrowingCounterData.Canonical ts) (cb : GrowingCounterData.Canonical bs) :
    exactCost depth V b a ts bs as+2*as.length+5 ≤
      a*(ArbitrarySliceStepBudget.budget depth V+6)+9*as.length+33 := by
  apply consumeCost_bound depth V b a ts bs as hV hbV
  · have hw := GrowingCounterData.canonical_width bs cb
    rw [hb] at hw
    have hl := Nat.log2_le_self b
    omega
  · intro i hi
    exact offsets_length_le b t i V ts ht ct hV (by nlinarith)

end
end IntegerMultBounds.Machine.ArbitrarySliceRepeat
