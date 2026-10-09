import IntegerMultBounds.Machine.ActiveTargetHighestLaterBank

/-! The later-source highest target bit is toggled by three actual machines:
physical interchange, controlled one-bit rotation, physical interchange. The
entire original array is retained as spectators, with no target-capacity bound.
All ten supplied canonical stage descriptors survive and all work tapes return
blank. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLaterRun
noncomputable section
open Networks.Shared50ModularControl (prime)
open ActiveTargetHighestLaterValue (nativeArray earlier later conjugation)
open RadixRangePadding (volume transpose)
open SharedPlacementAlphabet (setTape)

abbrev Array (G L B : ℕ) := Fin (volume (2^L) 2 (2^G) B) → Bool

def headers (hs : Fin 4 → List Bool) : Tapes 4 prime :=
  ⟨fun _ => 1,fun i => RadixZeroFill.encodedBinary (hs i)⟩
def focus (i : Fin 4) : Fin 58 := Fin.natAdd 54 i
def payload : Fin 58 := Fin.castAdd 4 (20 : Fin 54)
def caller (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (x : Array G L B)
    (bs qs ns : List Bool) (hs : Fin 4 → List Bool) : Tapes 58 prime :=
  (ActiveTargetHighestLaterAlphabet.input G L ws (nativeArray G L B x) bs qs ns).append (headers hs)
def input (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (x : Array G L B)
    (bs qs ns : List Bool) (hs : Fin 4 → List Bool) :=
  BinaryRadixEqualShared.input (caller G L ws x bs qs ns hs)

def swap := BinaryPackedFieldSwap.program focus payload
def middle := extend (extend ActiveTargetHighestLaterAlphabet.program 4) BinaryRadixEqualShared.count
def program := seq swap (seq middle swap)
def cost (G L B : ℕ) (hs : Fin 4 → List Bool) :=
  2*BinaryRadixEqualShared.cost (2^L) (2^G) B 1 hs+
    ActiveTargetHighestRun.constant*ActiveTargetHighestRun.volume G L B+2

theorem focus_ne : ∀ i, focus i≠payload := by
  intro i h
  have hv := congrArg Fin.val h
  change 54+i.val=20 at hv
  omega

theorem sources (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool) (x : Array G L B)
    (bs qs ns : List Bool) (hs : Fin 4 → List Bool) :
    BinaryAdjacentWidthHeadersShared.Sources (caller G L ws x bs qs ns hs) focus hs := by
  constructor <;> intro i <;> simp only [caller,focus,Tapes.append,Fin.addCases_right,headers]

theorem store_caller (G L B : ℕ) (ws : Fin 3 → List Bool) (bs qs ns : List Bool)
    (hs : Fin 4 → List Bool) (x y : Array G L B) :
    BinaryPackedFieldSwap.store (caller G L ws y bs qs ns hs) payload x=caller G L ws x bs qs ns hs := by
  unfold BinaryPackedFieldSwap.store caller payload
  rw [SharedPlacementAlphabet.setTape_append_left]
  exact congrArg (fun v => v.append (headers hs)) (ActiveTargetHighestLaterBank.store_input G L B ws bs qs ns x y)

theorem swaps (G L B : ℕ) (hB : 0<B) (ws : Fin 3 → List Bool) (bs qs ns : List Bool)
    (hs : Fin 4 → List Bool) (x : Array G L B)
    (hv : ∀ i, Counter.value (hs i)=BinaryRadixRangePrepare.values (2^L) (2^G) B 1 i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime swap (fun v => v=input G L ws x bs qs ns hs)
      (fun v => v=input G L ws (transpose x) bs qs ns hs)
      (BinaryRadixEqualShared.cost (2^L) (2^G) B 1 hs) := by
  have h := BinaryPackedFieldSwap.swaps (caller G L ws x bs qs ns hs) focus payload
    (2^L) (2^G) B 1 hs hv hc (by positivity) (by positivity) hB focus_ne
    (sources G L ws x bs qs ns hs) x
  rw [store_caller,store_caller] at h
  exact h

theorem middle_runs (G L B : ℕ) (hB : 0<B) (ws : Fin 3 → List Bool) (x : Array G L B)
    (bs qs ns : List Bool) (hs : Fin 4 → List Bool)
    (hw : ∀ i, Counter.value (ws i)=ActiveTargetHighestRun.width G L i)
    (cw : ∀ i, GrowingCounterData.Canonical (ws i))
    (hb : Counter.value bs=B) (hq : Counter.value qs=2)
    (hn : Counter.value ns=ActiveTargetHighestRun.prefixSize G L)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) :
    HoareTime middle (fun v => v=input G L ws x bs qs ns hs)
      (fun v => v=input G L ws (earlier x) bs qs ns hs)
      (ActiveTargetHighestRun.constant*ActiveTargetHighestRun.volume G L B) := by
  have h := ActiveTargetHighestLaterAlphabet.runs G L B hB ws (nativeArray G L B x) bs qs ns
    hw cw hb hq hn cb cq cn
  rw [ActiveTargetHighestLaterValue.native_array_earlier] at h
  have h₁ := h.extend (headers hs)
  have h₂ := h₁.extend (FixedHeaderBankCopy.empty BinaryRadixEqualShared.count)
  apply h₂.consequence ?_ ?_ le_rfl
  · rintro v rfl
    exact ⟨_,⟨_,rfl,rfl⟩,rfl⟩
  · rintro v ⟨a,⟨b,rfl,rfl⟩,rfl⟩
    rfl

/-- Complete later-source physical XOR with descriptor retention and paid
workspace restoration included in the literal endpoint equality. -/
theorem runs (G L B : ℕ) (hB : 0<B) (ws : Fin 3 → List Bool) (x : Array G L B)
    (bs qs ns : List Bool) (hs : Fin 4 → List Bool)
    (hw : ∀ i, Counter.value (ws i)=ActiveTargetHighestRun.width G L i)
    (cw : ∀ i, GrowingCounterData.Canonical (ws i))
    (hb : Counter.value bs=B) (hq : Counter.value qs=2)
    (hn : Counter.value ns=ActiveTargetHighestRun.prefixSize G L)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns)
    (hv : ∀ i, Counter.value (hs i)=BinaryRadixRangePrepare.values (2^L) (2^G) B 1 i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun v => v=input G L ws x bs qs ns hs)
      (fun v => v=input G L ws (later x) bs qs ns hs) (cost G L B hs) := by
  have h₁ := swaps G L B hB ws bs qs ns hs x hv hc
  have h₂ := middle_runs G L B hB ws (transpose x) bs qs ns hs hw cw hb hq hn cb cq cn
  have h₃ := swaps G L B hB ws bs qs ns hs (earlier (transpose x)) hv hc
  rw [conjugation] at h₃
  apply (h₁.seq (h₂.seq h₃)).consequence (fun _ h => h) (fun _ h => h)
  unfold cost
  omega

/-- Since both exchanged fields have width one, the real binary-interchange
bound reduces to a single uniform linear bound on the original full volume. -/
theorem uniform_bound : ∃ C : ℝ, 0<C ∧ ∀ (G L B : ℕ) (hs : Fin 4 → List Bool),
    0<B →
    (∀ i, Counter.value (hs i)=BinaryRadixRangePrepare.values (2^L) (2^G) B 1 i) →
    (∀ i, GrowingCounterData.Canonical (hs i)) →
    (cost G L B hs : ℝ) ≤ C*(volume (2^L) 2 (2^G) B : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := BinaryRadixEqualShared.uniform_bound
  refine ⟨2*C+137577,by linarith,?_⟩
  intro G L B hs hB hv hc
  have hb := hbound (2^L) (2^G) B 1 hs (by positivity) (by positivity) hB hv hc
  simp only [max_self,pow_one,Nat.cast_one,Real.one_rpow,mul_one] at hb
  have hV : (1 : ℝ) ≤ (volume (2^L) 2 (2^G) B : ℝ) := by
    have hn : 0<volume (2^L) 2 (2^G) B := by unfold volume; positivity
    exact_mod_cast hn
  simp only [cost,ActiveTargetHighestLaterValue.size_eq,ActiveTargetHighestRun.constant,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith only [hb,hV]

theorem result_eq_store (G L B : ℕ) (ws : Fin 3 → List Bool) (x : Array G L B)
    (bs qs ns : List Bool) (hs : Fin 4 → List Bool) :
    input G L ws (later x) bs qs ns hs=
      setTape (input G L ws x bs qs ns hs) (Fin.castAdd BinaryRadixEqualShared.count payload)
        (BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (later x i))) 0 := by
  unfold input BinaryRadixEqualShared.input
  rw [SharedPlacementAlphabet.setTape_append_left]
  exact congrArg (fun v => v.append (FixedHeaderBankCopy.empty BinaryRadixEqualShared.count))
    (store_caller G L B ws bs qs ns hs (later x) x).symm

theorem result_frame (G L B : ℕ) (ws : Fin 3 → List Bool) (x : Array G L B)
    (bs qs ns : List Bool) (hs : Fin 4 → List Bool)
    (i : Fin (58+BinaryRadixEqualShared.count))
    (hi : i≠Fin.castAdd BinaryRadixEqualShared.count payload) :
    (input G L ws (later x) bs qs ns hs).head i=(input G L ws x bs qs ns hs).head i ∧
    (input G L ws (later x) bs qs ns hs).tape i=(input G L ws x bs qs ns hs).tape i := by
  rw [result_eq_store]
  simp only [setTape,Function.update_of_ne hi]
  exact ⟨trivial,trivial⟩

theorem result_payload (G L B : ℕ) (ws : Fin 3 → List Bool) (x : Array G L B)
    (bs qs ns : List Bool) (hs : Fin 4 → List Bool) :
    (input G L ws (later x) bs qs ns hs).head (Fin.castAdd BinaryRadixEqualShared.count payload)=0 ∧
    (input G L ws (later x) bs qs ns hs).tape (Fin.castAdd BinaryRadixEqualShared.count payload)=
      BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (later x i)) := by
  rw [result_eq_store]
  simp only [setTape,Function.update_self]
  exact ⟨trivial,trivial⟩

theorem workspace_blank (G L B : ℕ) (ws : Fin 3 → List Bool) (x : Array G L B)
    (bs qs ns : List Bool) (hs : Fin 4 → List Bool) (i : Fin BinaryRadixEqualShared.count) :
    (input G L ws (later x) bs qs ns hs).head (Fin.natAdd 58 i)=0 ∧
    (input G L ws (later x) bs qs ns hs).tape (Fin.natAdd 58 i)=fun _ => blank := by
  simp only [input,BinaryRadixEqualShared.input,Tapes.append,Fin.addCases_right,FixedHeaderBankCopy.empty]
  exact ⟨trivial,trivial⟩

end
end IntegerMultBounds.Machine.ActiveTargetHighestLaterRun
