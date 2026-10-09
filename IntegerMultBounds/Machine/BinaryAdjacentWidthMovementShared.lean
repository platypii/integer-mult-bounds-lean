import IntegerMultBounds.Machine.BinaryAdjacentWidthHeadersShared
import IntegerMultBounds.Machine.RadixDigitMoveBlockExecution
import IntegerMultBounds.Machine.SharedPlacementAlphabet

/-! Binary block-digit movement sharing the caller's payload tape. All three
execution headers are copied physically into a blank private bank and erased
again. The constructed lifecycle supplies them from only P/G/B/u. -/
namespace IntegerMultBounds.Machine.BinaryAdjacentWidthMovementShared
noncomputable section
variable {a t P S E : ℕ}
open BinaryAdjacentWidthHeadersShared (Sources)
open SharedPlacementAlphabet (setTape)

def destination : Fin 3 → Fin 22 := ![6,18,7]
theorem destination_injective : Function.Injective destination := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [destination] at h

def bank (source : ℤ → Fin (a+4)) (hs : Fin 3 → List Bool) : Tapes 22 a :=
  RadixDigitMoveBlockExecution.bank (Q := 2) source (hs 0) (hs 1) (hs 2)

private theorem encoded_binary (bs : List Bool) :
    CountedLoopReuseAlphabet.binary (a := a) bs = RadixZeroFill.encodedBinary bs :=
  (RadixDigitMoveCounts.encoded_binary bs).symm

theorem private_bank (hs : Fin 3 → List Bool) :
    bank (a := a) (fun _ => blank) hs = FixedHeaderSparseBankCopy.headerBank destination hs := by
  apply FixedHeaderSparseBankCopy.headerBank_eq destination destination_injective
  · intro i; fin_cases i <;> exact ⟨rfl,encoded_binary _⟩
  · intro j hj
    fin_cases j <;> first | exact ⟨rfl,rfl⟩ | exact (hj 0 rfl).elim | exact (hj 1 rfl).elim | exact (hj 2 rfl).elim

theorem bank_source (source : ℤ → Fin (a+4)) (hs : Fin 3 → List Bool) :
    (bank source hs).head 0 = 0 ∧ (bank source hs).tape 0 = source := ⟨rfl,rfl⟩

theorem bank_set_source (source spare : ℤ → Fin (a+4)) (hs : Fin 3 → List Bool) :
    setTape (bank source hs) 0 spare 0 = bank spare hs := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

def copyProgram (focus : Fin 3 → Fin t) := FixedHeaderSparseBankCopy.program
  (a := a) (by omega : 0 < t+3) focus destination destination_injective (by decide)
def eraseProgram := FixedHeaderSparseBankCopy.cleanup
  (a := a) (by omega : 0 < t+3) destination destination_injective (by decide)
def moveProgram (payload : Fin t) := Placement.placed (RadixDigitMoveBlockExecution.forwardProgram 2 a)
  (SharedPlacementAlphabet.sharedPlacement payload (0 : Fin 22))
def unmoveProgram (payload : Fin t) := Placement.placed (RadixDigitMoveBlockExecution.backwardProgram 2 a)
  (SharedPlacementAlphabet.sharedPlacement payload (0 : Fin 22))
def forwardProgram (focus : Fin 3 → Fin t) (payload : Fin t) :=
  seq (seq (copyProgram (a := a) focus) (moveProgram payload)) (eraseProgram (a := a) (t := t))
def backwardProgram (focus : Fin 3 → Fin t) (payload : Fin t) :=
  seq (seq (copyProgram (a := a) focus) (unmoveProgram payload)) (eraseProgram (a := a) (t := t))
def coefficient := RadixDigitMoveBlockExecution.bound 2+63

private theorem forward_shared (caller : Tapes t a) (payload : Fin t)
    (source : ℤ → Fin (a+4)) (x : Fin (P*2*(S*E)) → Fin (a+4)) (hs : Fin 3 → List Bool)
    (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hp : Counter.value (hs 0) = P) (hs' : Counter.value (hs 1) = S) (he : Counter.value (hs 2) = E)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (ht : caller.tape payload = putWord source 0 (List.ofFn x)) (hh : caller.head payload = 0) :
    HoareTime (moveProgram payload)
      (fun v => v = caller.append (bank (fun _ => blank) hs))
      (fun v => v = (setTape caller payload
        (putWord source 0 (List.ofFn (RadixDigitMoveBlockRows.move x))) 0).append (bank (fun _ => blank) hs))
      (RadixDigitMoveBlockExecution.bound 2*(P*2*(S*E))) := by
  have h := RadixDigitMoveBlockExecution.forward_hoare source x (hs 0) (hs 1) (hs 2)
    hP (by omega) hS hE hp hs' he (hc 0) (hc 1) (hc 2)
  have hw := SharedPlacementAlphabet.shared_hoare h caller payload (0 : Fin 22) (fun _ => blank) 0 ht hh
  change HoareTime _ (fun v => v = caller.append (setTape (bank _ hs) 0 _ 0))
    (fun v => v = (setTape caller payload (putWord source 0 (List.ofFn (RadixDigitMoveBlockRows.move x))) 0).append (setTape (bank _ hs) 0 _ 0)) _ at hw
  simpa only [bank_set_source,moveProgram,RadixDigitMoveCore.count] using hw

private theorem backward_shared (caller : Tapes t a) (payload : Fin t)
    (source : ℤ → Fin (a+4)) (y : Fin (P*S*2*E) → Fin (a+4)) (hs : Fin 3 → List Bool)
    (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hp : Counter.value (hs 0) = P) (hs' : Counter.value (hs 1) = S) (he : Counter.value (hs 2) = E)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (ht : caller.tape payload = putWord source 0 (List.ofFn y)) (hh : caller.head payload = 0) :
    HoareTime (unmoveProgram payload)
      (fun v => v = caller.append (bank (fun _ => blank) hs))
      (fun v => v = (setTape caller payload
        (putWord source 0 (List.ofFn (RadixDigitMoveBlockRows.unmove y))) 0).append (bank (fun _ => blank) hs))
      (RadixDigitMoveBlockExecution.bound 2*(P*2*(S*E))) := by
  have h := RadixDigitMoveBlockExecution.backward_unmove_hoare source y (hs 0) (hs 1) (hs 2)
    hP (by omega) hS hE hp hs' he (hc 0) (hc 1) (hc 2)
  have hw := SharedPlacementAlphabet.shared_hoare h caller payload (0 : Fin 22) (fun _ => blank) 0 ht hh
  change HoareTime _ (fun v => v = caller.append (setTape (bank _ hs) 0 _ 0))
    (fun v => v = (setTape caller payload (putWord source 0 (List.ofFn (RadixDigitMoveBlockRows.unmove y))) 0).append (setTape (bank _ hs) 0 _ 0)) _ at hw
  simpa only [bank_set_source,unmoveProgram,RadixDigitMoveCore.count] using hw

theorem forward (caller : Tapes t a) (focus : Fin 3 → Fin t) (payload : Fin t)
    (source : ℤ → Fin (a+4)) (x : Fin (P*2*(S*E)) → Fin (a+4)) (hs : Fin 3 → List Bool)
    (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hp : Counter.value (hs 0) = P) (hs' : Counter.value (hs 1) = S) (he : Counter.value (hs 2) = E)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hsrc : Sources caller focus hs)
    (V : ℕ) (hV : 0 < V) (hb : ∀ i, Counter.value (hs i) ≤ V) (hvol : P*2*(S*E) ≤ V)
    (ht : caller.tape payload = putWord source 0 (List.ofFn x)) (hh : caller.head payload = 0) :
    HoareTime (forwardProgram focus payload)
      (fun v => v = caller.append (FixedHeaderBankCopy.empty 22))
      (fun v => v = (setTape caller payload
        (putWord source 0 (List.ofFn (RadixDigitMoveBlockRows.move x))) 0).append (FixedHeaderBankCopy.empty 22))
      (coefficient*V) := by
  have h1 := FixedHeaderSparseBankCopy.constructs_linear (a := a) (by omega : 0 < t+3)
    focus destination destination_injective (by decide) caller hs hsrc.tape hsrc.head V hV hc hb
  rw [← private_bank] at h1
  have h2 := forward_shared caller payload source x hs hP hS hE hp hs' he hc ht hh
  have h3 := FixedHeaderSparseBankCopy.cleans_linear (a := a) (by omega : 0 < t+3)
    destination destination_injective (by decide)
    (setTape caller payload (putWord source 0 (List.ofFn (RadixDigitMoveBlockRows.move x))) 0) hs V hV hc hb
  rw [← private_bank] at h3
  apply ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h)
  have hm := Nat.mul_le_mul_left (RadixDigitMoveBlockExecution.bound 2) hvol
  unfold coefficient
  nlinarith

theorem backward (caller : Tapes t a) (focus : Fin 3 → Fin t) (payload : Fin t)
    (source : ℤ → Fin (a+4)) (y : Fin (P*S*2*E) → Fin (a+4)) (hs : Fin 3 → List Bool)
    (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hp : Counter.value (hs 0) = P) (hs' : Counter.value (hs 1) = S) (he : Counter.value (hs 2) = E)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hsrc : Sources caller focus hs)
    (V : ℕ) (hV : 0 < V) (hb : ∀ i, Counter.value (hs i) ≤ V) (hvol : P*2*(S*E) ≤ V)
    (ht : caller.tape payload = putWord source 0 (List.ofFn y)) (hh : caller.head payload = 0) :
    HoareTime (backwardProgram focus payload)
      (fun v => v = caller.append (FixedHeaderBankCopy.empty 22))
      (fun v => v = (setTape caller payload
        (putWord source 0 (List.ofFn (RadixDigitMoveBlockRows.unmove y))) 0).append (FixedHeaderBankCopy.empty 22))
      (coefficient*V) := by
  have h1 := FixedHeaderSparseBankCopy.constructs_linear (a := a) (by omega : 0 < t+3)
    focus destination destination_injective (by decide) caller hs hsrc.tape hsrc.head V hV hc hb
  rw [← private_bank] at h1
  have h2 := backward_shared caller payload source y hs hP hS hE hp hs' he hc ht hh
  have h3 := FixedHeaderSparseBankCopy.cleans_linear (a := a) (by omega : 0 < t+3)
    destination destination_injective (by decide)
    (setTape caller payload (putWord source 0 (List.ofFn (RadixDigitMoveBlockRows.unmove y))) 0) hs V hV hc hb
  rw [← private_bank] at h3
  apply ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h)
  have hm := Nat.mul_le_mul_left (RadixDigitMoveBlockExecution.bound 2) hvol
  unfold coefficient
  nlinarith

/-- The complete forty-tape private workspace starts and finishes blank. -/
def input (caller : Tapes t a) :=
  (BinaryAdjacentWidthHeadersShared.input caller).append (FixedHeaderBankCopy.empty 22)
def payloadSlot (payload : Fin t) : Fin ((t+1)+17) := Fin.castAdd 17 (Fin.castAdd 1 payload)
def constructedForwardProgram (focus : Fin 4 → Fin t) (payload : Fin t) := seq
  (seq (extend (BinaryAdjacentWidthHeadersShared.program (a := a) focus) 22)
    (forwardProgram (a := a) BinaryAdjacentWidthHeadersShared.movementFocus (payloadSlot payload)))
  (extend (BinaryAdjacentWidthHeadersShared.cleanup (a := a) (t := t)) 22)
def constructedBackwardProgram (focus : Fin 4 → Fin t) (payload : Fin t) := seq
  (seq (extend (BinaryAdjacentWidthHeadersShared.program (a := a) focus) 22)
    (backwardProgram (a := a) BinaryAdjacentWidthHeadersShared.movementFocus (payloadSlot payload)))
  (extend (BinaryAdjacentWidthHeadersShared.cleanup (a := a) (t := t)) 22)
def constructedCoefficient := BinaryAdjacentWidthHeadersShared.constructCoefficient+coefficient+107

theorem movement_volume (P G B u : ℕ) :
    P*2*((2^u*G)*(2^u*B)) = BinaryAdjacentWidthHeadersShared.volume P G B u := by
  unfold BinaryAdjacentWidthHeadersShared.volume
  ring

theorem movement_bounds (P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : ∀ i, Counter.value (hs i) = BinaryAdjacentWidthHeadersShared.values P G B u i) :
    ∀ i, Counter.value (BinaryAdjacentWidthHeadersShared.movementWords P G B u hs i) ≤
      BinaryAdjacentWidthHeadersShared.volume P G B u := by
  obtain ⟨_,hD⟩ := BinaryAdjacentWidthHeadersShared.volume_bounds P G B u hP hG hB
  obtain ⟨_,_,hb⟩ := ArbitraryWidthHighDimensions.data_volume_bounds 2 P G B u 0
    (by omega) (by omega) hP hG hB
  intro i
  rw [BinaryAdjacentWidthHeadersShared.movement_values P G B u hs hv]
  fin_cases i
  · have h := (hb 3).trans hD
    simpa [ArbitraryWidthHighDimensions.values,BinaryAdjacentWidthHeadersShared.movementValues] using h
  · have h := (hb 4).trans hD
    simpa [ArbitraryWidthHighDimensions.values,BinaryAdjacentWidthHeadersShared.movementValues,Nat.mul_comm] using h
  · have h := (hb 5).trans hD
    simpa [ArbitraryWidthHighDimensions.values,BinaryAdjacentWidthHeadersShared.movementValues,Nat.mul_comm] using h

theorem output_setTape (caller : Tapes t a) (P G B u : ℕ) (hs : Fin 4 → List Bool)
    (payload : Fin t) (word : ℤ → Fin (a+4)) :
    setTape (BinaryAdjacentWidthHeadersShared.output caller P G B u hs) (payloadSlot payload) word 0 =
      BinaryAdjacentWidthHeadersShared.output (setTape caller payload word 0) P G B u hs := by
  simp only [BinaryAdjacentWidthHeadersShared.output,payloadSlot,SharedPlacementAlphabet.setTape_append_left]

/-- Fully constructed forward movement, from only the four original headers.
The payload exterior and all other caller tapes are retained, and every private
header, generated descriptor and work tape is restored to blank. -/
theorem constructed_forward (caller : Tapes t a) (focus : Fin 4 → Fin t) (payload : Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool) (source : ℤ → Fin (a+4))
    (x : Fin (P*2*((2^u*G)*(2^u*B))) → Fin (a+4))
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : ∀ i, Counter.value (hs i) = BinaryAdjacentWidthHeadersShared.values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hsrc : Sources caller focus hs)
    (ht : caller.tape payload = putWord source 0 (List.ofFn x)) (hh : caller.head payload = 0) :
    HoareTime (constructedForwardProgram focus payload) (fun v => v = input caller)
      (fun v => v = input (setTape caller payload
        (putWord source 0 (List.ofFn (RadixDigitMoveBlockRows.move x))) 0))
      (constructedCoefficient*BinaryAdjacentWidthHeadersShared.volume P G B u) := by
  have h1 := hoare_extend_eq (BinaryAdjacentWidthHeadersShared.constructs caller focus P G B u hs
    hP hG hB hv hc hsrc) (FixedHeaderBankCopy.empty 22)
  have hm := BinaryAdjacentWidthHeadersShared.movement_values P G B u hs hv
  have hcanon := BinaryAdjacentWidthHeadersShared.movement_canonical P G B u hs hc
  have hcells := BinaryAdjacentWidthHeadersShared.caller_cells caller P G B u hs payload
  have h2 := forward (BinaryAdjacentWidthHeadersShared.output caller P G B u hs)
    BinaryAdjacentWidthHeadersShared.movementFocus (payloadSlot payload) source x
    (BinaryAdjacentWidthHeadersShared.movementWords P G B u hs) hP (by positivity) (by positivity)
    (hm 0) (hm 1) (hm 2) hcanon (BinaryAdjacentWidthHeadersShared.movement_sources caller P G B u hs)
    (BinaryAdjacentWidthHeadersShared.volume P G B u)
    (BinaryAdjacentWidthHeadersShared.volume_bounds P G B u hP hG hB).1
    (movement_bounds P G B u hs hP hG hB hv) (le_of_eq (movement_volume P G B u))
    (hcells.2.trans ht) (hcells.1.trans hh)
  rw [output_setTape] at h2
  have h3 := hoare_extend_eq (BinaryAdjacentWidthHeadersShared.cleans
    (setTape caller payload (putWord source 0 (List.ofFn (RadixDigitMoveBlockRows.move x))) 0)
    focus P G B u hs hP hG hB hv hc) (FixedHeaderBankCopy.empty 22)
  apply ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h)
  have hV := (BinaryAdjacentWidthHeadersShared.volume_bounds P G B u hP hG hB).1
  unfold constructedCoefficient
  nlinarith

/-- Fully constructed inverse movement, from only the four original headers.
The payload exterior and all other caller tapes are retained, and every private
header, generated descriptor and work tape is restored to blank. -/
theorem constructed_backward (caller : Tapes t a) (focus : Fin 4 → Fin t) (payload : Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool) (source : ℤ → Fin (a+4))
    (y : Fin (P*(2^u*G)*2*(2^u*B)) → Fin (a+4))
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : ∀ i, Counter.value (hs i) = BinaryAdjacentWidthHeadersShared.values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hsrc : Sources caller focus hs)
    (ht : caller.tape payload = putWord source 0 (List.ofFn y)) (hh : caller.head payload = 0) :
    HoareTime (constructedBackwardProgram focus payload) (fun v => v = input caller)
      (fun v => v = input (setTape caller payload
        (putWord source 0 (List.ofFn (RadixDigitMoveBlockRows.unmove y))) 0))
      (constructedCoefficient*BinaryAdjacentWidthHeadersShared.volume P G B u) := by
  have h1 := hoare_extend_eq (BinaryAdjacentWidthHeadersShared.constructs caller focus P G B u hs
    hP hG hB hv hc hsrc) (FixedHeaderBankCopy.empty 22)
  have hm := BinaryAdjacentWidthHeadersShared.movement_values P G B u hs hv
  have hcanon := BinaryAdjacentWidthHeadersShared.movement_canonical P G B u hs hc
  have hcells := BinaryAdjacentWidthHeadersShared.caller_cells caller P G B u hs payload
  have h2 := backward (BinaryAdjacentWidthHeadersShared.output caller P G B u hs)
    BinaryAdjacentWidthHeadersShared.movementFocus (payloadSlot payload) source y
    (BinaryAdjacentWidthHeadersShared.movementWords P G B u hs) hP (by positivity) (by positivity)
    (hm 0) (hm 1) (hm 2) hcanon (BinaryAdjacentWidthHeadersShared.movement_sources caller P G B u hs)
    (BinaryAdjacentWidthHeadersShared.volume P G B u)
    (BinaryAdjacentWidthHeadersShared.volume_bounds P G B u hP hG hB).1
    (movement_bounds P G B u hs hP hG hB hv) (le_of_eq (movement_volume P G B u))
    (hcells.2.trans ht) (hcells.1.trans hh)
  rw [output_setTape] at h2
  have h3 := hoare_extend_eq (BinaryAdjacentWidthHeadersShared.cleans
    (setTape caller payload (putWord source 0 (List.ofFn (RadixDigitMoveBlockRows.unmove y))) 0)
    focus P G B u hs hP hG hB hv hc) (FixedHeaderBankCopy.empty 22)
  apply ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h)
  have hV := (BinaryAdjacentWidthHeadersShared.volume_bounds P G B u hP hG hB).1
  unfold constructedCoefficient
  nlinarith

end
end IntegerMultBounds.Machine.BinaryAdjacentWidthMovementShared
