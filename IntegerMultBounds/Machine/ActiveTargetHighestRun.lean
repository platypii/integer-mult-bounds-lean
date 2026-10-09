import IntegerMultBounds.Machine.FlatControlledShiftPayload
import IntegerMultBounds.Machine.CleanExecution
import IntegerMultBounds.Compact.ActiveTargetSubsegmentWords

/-! Actual radix-two controlled one-bit rotation, followed by physical cleanup.
Stage inputs supply canonical widths and B/Q/P descriptors; no offset table or
initialized private tape is supplied. Arbitrary preceding/intervening/suffix
spectators are included in the exact array. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestRun
noncomputable section
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

abbrev width (G L : ℕ) : Fin 3 → ℕ := ![1,G,L]
def low : List (Fin 3) := [1]
def high : List (Fin 3) := [2]
def order : List (Fin 3) := low++0::high

abbrev prefixSize (G L : ℕ) := 2^PrefixAddressData.widthSum order (width G L)
abbrev volume (G L B : ℕ) := prefixSize G L*(2^(width G L 0)*B)
abbrev Array (G L B : ℕ) := Fin (volume G L B) → Fin 4

def right (i : Fin 27) : Bool := decide (i.val=2 ∨ i.val=5 ∨ i.val=8 ∨ i.val=15 ∨ i.val=17 ∨ i.val=26)
def keep (i : Fin 27) : Bool := right i || decide (i.val=20)
def base := FlatControlledShiftReady.program (radix := 2) (1 : ℚ) order (by decide)
def program := CleanExecution.program base right keep

def initial (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool) : Tapes 27 2 :=
  RationalPrefixTranslationBootstrap.input (radix := 2) 1 order (width G L) ws a
    (fun _ => blank) (fun _ => blank) 0 0 bs qs ns

def stageOutput (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool) : Tapes 27 2 :=
  FlatControlledShiftReady.output (radix := 2) 1 low high (width G L) ws a
    (fun _ => blank) (fun _ => blank) 0 0 bs qs ns

def input (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool) :=
  (initial G L ws a bs qs ns).append (SharedBank.empty 27 2)
def output (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool) :=
  (TrackedCleanupList.retained keep (stageOutput G L ws a bs qs ns)).append (SharedBank.empty 27 2)

private theorem initial_heads (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool) :
    (initial G L ws a bs qs ns).head=TrackedInit.position right := by
  rw [initial,FlatControlledShiftLayout.input_layout]
  funext i
  fin_cases i <;> rfl

private theorem initial_blank (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool)
    (i : Fin 27) (hi : keep i=false) : (initial G L ws a bs qs ns).tape i=fun _ => blank := by
  rw [initial,FlatControlledShiftLayout.input_layout]
  fin_cases i
  all_goals first | rfl | simp [keep,right] at hi

def constant := 137*1002+301

theorem runs (G L B : ℕ) (hB : 0<B) (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool)
    (hw : ∀ i, Counter.value (ws i)=width G L i) (cw : ∀ i, GrowingCounterData.Canonical (ws i))
    (hb : Counter.value bs=B) (hq : Counter.value qs=2) (hn : Counter.value ns=prefixSize G L)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) (cn : GrowingCounterData.Canonical ns) :
    HoareTime program (fun v => v=input G L ws a bs qs ns) (fun v => v=output G L ws a bs qs ns)
      (constant*volume G L B) := by
  have hp : order.Perm (List.finRange 3) := by decide
  have h := FlatControlledShiftReady.realizes_hoare (radix := 2) (1 : ℚ) (by decide) low high hp
    (width G L) ws hw cw hB a (fun _ => blank) (fun _ => blank) 0 0 bs qs ns hb hq hn cb cq cn
    (by intros; rfl)
  have hc := CleanExecution.realizes base right keep (initial G L ws a bs qs ns)
    (stageOutput G L ws a bs qs ns) (886*volume G L B+116) (initial_heads G L ws a bs qs ns)
    (initial_blank G L ws a bs qs ns) h
  apply hc.consequence (fun _ h => h) (fun _ h => h)
  have hV : 0<volume G L B := by unfold volume prefixSize; positivity
  norm_num [constant,PrefixCounterInit.tapeCount]
  nlinarith

def descriptorSlot : Fin 6 → Fin 27 := ![2,5,8,15,17,26]

private theorem descriptor_0 (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool) :
    (output G L ws a bs qs ns).head (2 : Fin 54)=(input G L ws a bs qs ns).head (2 : Fin 54) ∧
    (output G L ws a bs qs ns).tape (2 : Fin 54)=(input G L ws a bs qs ns).tape (2 : Fin 54) := by
  rw [input,initial,FlatControlledShiftLayout.input_layout]
  exact ⟨rfl,rfl⟩

private theorem descriptor_1 (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool) :
    (output G L ws a bs qs ns).head (5 : Fin 54)=(input G L ws a bs qs ns).head (5 : Fin 54) ∧
    (output G L ws a bs qs ns).tape (5 : Fin 54)=(input G L ws a bs qs ns).tape (5 : Fin 54) := by
  rw [input,initial,FlatControlledShiftLayout.input_layout]
  exact ⟨rfl,rfl⟩

private theorem descriptor_2 (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool) :
    (output G L ws a bs qs ns).head (8 : Fin 54)=(input G L ws a bs qs ns).head (8 : Fin 54) ∧
    (output G L ws a bs qs ns).tape (8 : Fin 54)=(input G L ws a bs qs ns).tape (8 : Fin 54) := by
  rw [input,initial,FlatControlledShiftLayout.input_layout]
  exact ⟨rfl,rfl⟩

private theorem descriptor_3 (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool) :
    (output G L ws a bs qs ns).head (15 : Fin 54)=(input G L ws a bs qs ns).head (15 : Fin 54) ∧
    (output G L ws a bs qs ns).tape (15 : Fin 54)=(input G L ws a bs qs ns).tape (15 : Fin 54) := by
  rw [input,initial,FlatControlledShiftLayout.input_layout]
  have ha := FlatControlledShiftReady.output_active (radix := 2) 1 low high (width G L) ws a
    (fun _ => blank) (fun _ => blank) 0 0 bs qs ns
  have hh := congrFun (congrArg Tapes.head ha) (5 : Fin 20)
  have ht := congrFun (congrArg Tapes.tape ha) (5 : Fin 20)
  change (stageOutput G L ws a bs qs ns).head (15 : Fin 27)=_ at hh
  change (stageOutput G L ws a bs qs ns).tape (15 : Fin 27)=_ at ht
  change (stageOutput G L ws a bs qs ns).head (15 : Fin 27)=1 ∧
    (stageOutput G L ws a bs qs ns).tape (15 : Fin 27)=RadixZeroFill.encodedBinary bs
  rw [hh,ht]
  constructor
  · rfl
  · rfl

private theorem descriptor_4 (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool) :
    (output G L ws a bs qs ns).head (17 : Fin 54)=(input G L ws a bs qs ns).head (17 : Fin 54) ∧
    (output G L ws a bs qs ns).tape (17 : Fin 54)=(input G L ws a bs qs ns).tape (17 : Fin 54) := by
  rw [input,initial,FlatControlledShiftLayout.input_layout]
  have ha := FlatControlledShiftReady.output_active (radix := 2) 1 low high (width G L) ws a
    (fun _ => blank) (fun _ => blank) 0 0 bs qs ns
  have hh := congrFun (congrArg Tapes.head ha) (7 : Fin 20)
  have ht := congrFun (congrArg Tapes.tape ha) (7 : Fin 20)
  change (stageOutput G L ws a bs qs ns).head (17 : Fin 27)=_ at hh
  change (stageOutput G L ws a bs qs ns).tape (17 : Fin 27)=_ at ht
  change (stageOutput G L ws a bs qs ns).head (17 : Fin 27)=1 ∧
    (stageOutput G L ws a bs qs ns).tape (17 : Fin 27)=RadixZeroFill.encodedBinary qs
  rw [hh,ht]
  constructor
  · rfl
  · rfl

private theorem descriptor_5 (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool) :
    (output G L ws a bs qs ns).head (26 : Fin 54)=(input G L ws a bs qs ns).head (26 : Fin 54) ∧
    (output G L ws a bs qs ns).tape (26 : Fin 54)=(input G L ws a bs qs ns).tape (26 : Fin 54) := by
  rw [input,initial,FlatControlledShiftLayout.input_layout]
  have ha := FlatControlledShiftReady.output_active (radix := 2) 1 low high (width G L) ws a
    (fun _ => blank) (fun _ => blank) 0 0 bs qs ns
  have hh := congrFun (congrArg Tapes.head ha) (19 : Fin 20)
  have ht := congrFun (congrArg Tapes.tape ha) (19 : Fin 20)
  change (stageOutput G L ws a bs qs ns).head (26 : Fin 27)=_ at hh
  change (stageOutput G L ws a bs qs ns).tape (26 : Fin 27)=_ at ht
  change (stageOutput G L ws a bs qs ns).head (26 : Fin 27)=1 ∧
    (stageOutput G L ws a bs qs ns).tape (26 : Fin 27)=RadixZeroFill.encodedBinary ns
  rw [hh,ht]
  constructor
  · rfl
  · exact (CountedLoopReuseAlphabet.encoding_binary ns).symm

theorem descriptors_retained (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool)
    (j : Fin 6) :
    (output G L ws a bs qs ns).head (Fin.castAdd 27 (descriptorSlot j))=
      (input G L ws a bs qs ns).head (Fin.castAdd 27 (descriptorSlot j)) ∧
    (output G L ws a bs qs ns).tape (Fin.castAdd 27 (descriptorSlot j))=
      (input G L ws a bs qs ns).tape (Fin.castAdd 27 (descriptorSlot j)) := by
  fin_cases j
  · exact descriptor_0 G L ws a bs qs ns
  · exact descriptor_1 G L ws a bs qs ns
  · exact descriptor_2 G L ws a bs qs ns
  · exact descriptor_3 G L ws a bs qs ns
  · exact descriptor_4 G L ws a bs qs ns
  · exact descriptor_5 G L ws a bs qs ns

theorem private_blank (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool)
    (i : Fin 27) (hi : keep i=false) :
    (output G L ws a bs qs ns).head (Fin.castAdd 27 i)=0 ∧
    (output G L ws a bs qs ns).tape (Fin.castAdd 27 i)=fun _ => blank := by
  simp only [output,Tapes.append,Fin.addCases_left,TrackedCleanupList.retained,hi,Bool.false_eq_true,ite_false]
  exact ⟨trivial,trivial⟩

theorem trackers_blank (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool)
    (i : Fin 27) : (output G L ws a bs qs ns).head (Fin.natAdd 27 i)=0 ∧
    (output G L ws a bs qs ns).tape (Fin.natAdd 27 i)=fun _ => blank := by
  simp only [output,Tapes.append,Fin.addCases_right,SharedBank.empty]
  exact ⟨trivial,trivial⟩

def array (G L : ℕ) {B : ℕ} (a : Array G L B) : Array G L B :=
  FlatControlledShiftArray.array (radix := 2) 1 low high (width G L) a

theorem output_array (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool) :
    (output G L ws a bs qs ns).tape (20 : Fin 54)=
      fun z => (RadixToBinary.binaryEncoding (q := 2)).encode
        (putWord (fun _ => blank) 0 (List.ofFn (array G L a)) z) := by
  have h := FlatControlledShiftArray.output_source (radix := 2) 1 low high (width G L) ws a
    (fun _ => blank) (fun _ => blank) 0 0 bs qs ns
  change (stageOutput G L ws a bs qs ns).tape (20 : Fin 27)=_ at h
  change (stageOutput G L ws a bs qs ns).tape (20 : Fin 27)=_
  exact h

theorem output_origin (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool) :
    (output G L ws a bs qs ns).head (20 : Fin 54)=0 := by
  have h := FlatControlledShiftPayload.output_payload (radix := 2) 1 low high (width G L) ws a
    (fun _ => blank) (fun _ => blank) 0 0 bs qs ns
  have hh := congrFun (congrArg Tapes.head h) (0 : Fin 2)
  change (stageOutput G L ws a bs qs ns).head (20 : Fin 27)=0 at hh
  exact hh

end
end IntegerMultBounds.Machine.ActiveTargetHighestRun
