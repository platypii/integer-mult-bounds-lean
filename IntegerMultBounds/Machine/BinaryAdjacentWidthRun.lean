import IntegerMultBounds.Machine.BinaryAdjacentWidthPrefixShared
import IntegerMultBounds.Machine.BinaryAdjacentWidthMovementShared
import IntegerMultBounds.Machine.BinaryAdjacentWidthInterchange
import IntegerMultBounds.Machine.BinaryRadixEqualShared

/-! Actual adjacent binary-width interchange, with physically constructed
prefix and movement headers and blank private workspace at both endpoints. -/
namespace IntegerMultBounds.Machine.BinaryAdjacentWidthRun
noncomputable section
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open BinaryAdjacentWidthHeadersShared (Sources values volume)
variable {t : ℕ}

def prefixSlot (i : Fin t) := Fin.castAdd 17 (Fin.castAdd 1 i)
def equalSlot (i : Fin ((t+1)+17)) := Fin.castAdd BinaryRadixEqualShared.count i

def middle (caller : Tapes t prime) := BinaryRadixEqualShared.input (BinaryAdjacentWidthPrefixShared.input caller)
def input (caller : Tapes t prime) := BinaryAdjacentWidthMovementShared.input (middle caller)
def ready (caller : Tapes t prime) (P G B : ℕ) (hs : Fin 4 → List Bool) :=
  BinaryAdjacentWidthMovementShared.input (BinaryRadixEqualShared.input (BinaryAdjacentWidthPrefixShared.output caller P G B hs))
def setup (focus : Fin 4 → Fin t) := extend (extend (extend (extend
  (BinaryAdjacentWidthPrefixShared.program (a := prime) focus) BinaryRadixEqualShared.count) 1) 17) 22
def cleanup := extend (extend (extend (extend
  (BinaryAdjacentWidthPrefixShared.cleanup (a := prime) (t := t)) BinaryRadixEqualShared.count) 1) 17) 22

def equalProgram (focus : Fin 4 → Fin t) (payload : Fin t) :=
  extend (extend (extend (BinaryRadixEqualShared.program (BinaryAdjacentWidthPrefixShared.equalFocus focus) (prefixSlot payload)) 1) 17) 22
def movementFocus (focus : Fin 4 → Fin t) := fun i => equalSlot (prefixSlot (focus i))
def forwardProgram (focus : Fin 4 → Fin t) (payload : Fin t) :=
  BinaryAdjacentWidthMovementShared.constructedForwardProgram (a := prime) (movementFocus focus) (equalSlot (prefixSlot payload))
def backwardProgram (focus : Fin 4 → Fin t) (payload : Fin t) :=
  BinaryAdjacentWidthMovementShared.constructedBackwardProgram (a := prime) (movementFocus focus) (equalSlot (prefixSlot payload))
def longHProgram (focus : Fin 4 → Fin t) (payload : Fin t) :=
  seq (seq (seq (setup focus) (equalProgram focus payload)) (forwardProgram focus payload)) cleanup
def longDProgram (focus : Fin 4 → Fin t) (payload : Fin t) :=
  seq (seq (seq (setup focus) (backwardProgram focus payload)) (equalProgram focus payload)) cleanup

def cost (P G B u : ℕ) (hs : Fin 4 → List Bool) :=
  BinaryAdjacentWidthPrefixShared.coefficient*volume P G B u + BinaryRadixEqualShared.cost (P*2) G B u (BinaryAdjacentWidthPrefixShared.equalWords P G B hs) +
    BinaryAdjacentWidthMovementShared.constructedCoefficient*volume P G B u + 210*volume P G B u + 3

private theorem equal_values (P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i) :
    ∀ i, Counter.value (BinaryAdjacentWidthPrefixShared.equalWords P G B hs i) = BinaryRadixRangePrepare.values (P*2) G B u i := by
  intro i; fin_cases i
  · exact BinaryAdjacentWidthPrefixShared.bits_value P G B
  · exact hv 1
  · exact hv 2
  · exact hv 3
private theorem equal_canonical (P G B : ℕ) (hs : Fin 4 → List Bool)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    ∀ i, GrowingCounterData.Canonical (BinaryAdjacentWidthPrefixShared.equalWords P G B hs i) := by
  intro i; fin_cases i
  · exact BinaryAdjacentWidthPrefixShared.bits_canonical P G B
  · exact hc 1
  · exact hc 2
  · exact hc 3

private theorem prefix_setTape (caller : Tapes t prime) (P G B : ℕ)
    (hs : Fin 4 → List Bool) (payload : Fin t) (word : ℤ → Fin (prime+4)) :
    setTape (BinaryAdjacentWidthPrefixShared.output caller P G B hs) (prefixSlot payload) word 0 =
      BinaryAdjacentWidthPrefixShared.output (setTape caller payload word 0) P G B hs := by
  simp only [BinaryAdjacentWidthPrefixShared.output,prefixSlot,SharedPlacementAlphabet.setTape_append_left]

private theorem source_changed (caller : Tapes t prime) (focus : Fin 4 → Fin t)
    (payload : Fin t) (hs : Fin 4 → List Bool) (hsrc : Sources caller focus hs)
    (hh : caller.head payload = 0) (word : ℤ → Fin (prime+4)) :
    Sources (setTape caller payload word 0) focus hs := by
  have hn : ∀ i, focus i ≠ payload := by
    intro i h
    have hi := hsrc.head i
    rw [h,hh] at hi
    omega
  constructor
  · intro i; simpa only [setTape,Function.update_of_ne (hn i)] using hsrc.tape i
  · intro i; simpa only [setTape,Function.update_of_ne (hn i)] using hsrc.head i

private theorem prepared_sources (caller : Tapes t prime) (focus : Fin 4 → Fin t)
    (P G B : ℕ) (hs : Fin 4 → List Bool) (hsrc : Sources caller focus hs) :
    Sources (BinaryRadixEqualShared.input (BinaryAdjacentWidthPrefixShared.output caller P G B hs)) (movementFocus focus) hs := by
  constructor
  · intro i
    simpa only [BinaryRadixEqualShared.input,BinaryAdjacentWidthPrefixShared.output,movementFocus,equalSlot,prefixSlot,Tapes.append,Fin.addCases_left] using hsrc.tape i
  · intro i
    simpa only [BinaryRadixEqualShared.input,BinaryAdjacentWidthPrefixShared.output,movementFocus,equalSlot,prefixSlot,Tapes.append,Fin.addCases_left] using hsrc.head i

private theorem setup_runs (caller : Tapes t prime) (focus : Fin 4 → Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hsrc : Sources caller focus hs) :
    HoareTime (setup focus) (fun z => z = input caller) (fun z => z = ready caller P G B hs)
      (BinaryAdjacentWidthPrefixShared.coefficient*volume P G B u) := by
  exact hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (BinaryAdjacentWidthPrefixShared.constructs caller focus P G B u hs hP hG hB hv hc hsrc)
      (FixedHeaderBankCopy.empty BinaryRadixEqualShared.count)) (FixedHeaderBankCopy.empty 1))
      (FixedHeaderBankCopy.empty 17)) (FixedHeaderBankCopy.empty 22)

private theorem cleanup_runs (caller : Tapes t prime) (focus : Fin 4 → Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (cleanup (t := t)) (fun z => z = ready caller P G B hs) (fun z => z = input caller)
      (210*volume P G B u) := by
  exact hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (BinaryAdjacentWidthPrefixShared.cleans caller focus P G B u hs hP hG hB hv hc)
      (FixedHeaderBankCopy.empty BinaryRadixEqualShared.count)) (FixedHeaderBankCopy.empty 1))
      (FixedHeaderBankCopy.empty 17)) (FixedHeaderBankCopy.empty 22)

private theorem equal_runs (caller : Tapes t prime) (focus : Fin 4 → Fin t) (payload : Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hsrc : Sources caller focus hs)
    (x : Fin (RadixRangePadding.volume (P*2) (2^u) G B) → Bool)
    (ht : caller.tape payload = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head payload = 0) :
    HoareTime (equalProgram focus payload) (fun z => z = ready caller P G B hs)
      (fun z => z = ready (setTape caller payload
        (BinaryRadixRangePrepareAlphabet.word (RadixRangePadding.transpose (fun i => bitSymbol (x i)))) 0) P G B hs)
      (BinaryRadixEqualShared.cost (P*2) G B u (BinaryAdjacentWidthPrefixShared.equalWords P G B hs)) := by
  have h := BinaryRadixEqualShared.runs (BinaryAdjacentWidthPrefixShared.output caller P G B hs) (BinaryAdjacentWidthPrefixShared.equalFocus focus) (prefixSlot payload)
    (P*2) G B u (BinaryAdjacentWidthPrefixShared.equalWords P G B hs) (equal_values P G B u hs hv)
    (equal_canonical P G B hs hc) (by omega) hG hB (BinaryAdjacentWidthPrefixShared.equal_sources caller focus P G B hs hsrc) x
    (by simpa only [BinaryAdjacentWidthPrefixShared.output,prefixSlot,Tapes.append,Fin.addCases_left] using ht)
    (by simpa only [BinaryAdjacentWidthPrefixShared.output,prefixSlot,Tapes.append,Fin.addCases_left] using hh)
  rw [prefix_setTape] at h
  exact hoare_extend_eq (hoare_extend_eq (hoare_extend_eq h
    (FixedHeaderBankCopy.empty 1)) (FixedHeaderBankCopy.empty 17)) (FixedHeaderBankCopy.empty 22)

private theorem forward_runs (caller : Tapes t prime) (focus : Fin 4 → Fin t) (payload : Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hsrc : Sources caller focus hs)
    (x : Fin (P*2*((2^u*G)*(2^u*B))) → Fin (prime+4))
    (ht : caller.tape payload = putWord (fun _ => blank) 0 (List.ofFn x)) (hh : caller.head payload = 0) :
    HoareTime (forwardProgram focus payload) (fun z => z = ready caller P G B hs)
      (fun z => z = ready (setTape caller payload
        (putWord (fun _ => blank) 0 (List.ofFn (RadixDigitMoveBlockRows.move x))) 0) P G B hs)
      (BinaryAdjacentWidthMovementShared.constructedCoefficient*volume P G B u) := by
  have h := BinaryAdjacentWidthMovementShared.constructed_forward (BinaryRadixEqualShared.input (BinaryAdjacentWidthPrefixShared.output caller P G B hs)) (movementFocus focus)
    (equalSlot (prefixSlot payload)) P G B u hs (fun _ => blank) x hP hG hB hv hc
    (prepared_sources caller focus P G B hs hsrc)
    (by simpa only [BinaryRadixEqualShared.input,BinaryAdjacentWidthPrefixShared.output,equalSlot,prefixSlot,Tapes.append,Fin.addCases_left] using ht)
    (by simpa only [BinaryRadixEqualShared.input,BinaryAdjacentWidthPrefixShared.output,equalSlot,prefixSlot,Tapes.append,Fin.addCases_left] using hh)
  simp only [BinaryRadixEqualShared.input,equalSlot,SharedPlacementAlphabet.setTape_append_left,prefix_setTape] at h
  exact h
private theorem backward_runs (caller : Tapes t prime) (focus : Fin 4 → Fin t) (payload : Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hsrc : Sources caller focus hs)
    (x : Fin (P*(2^u*G)*2*(2^u*B)) → Fin (prime+4))
    (ht : caller.tape payload = putWord (fun _ => blank) 0 (List.ofFn x)) (hh : caller.head payload = 0) :
    HoareTime (backwardProgram focus payload) (fun z => z = ready caller P G B hs)
      (fun z => z = ready (setTape caller payload
        (putWord (fun _ => blank) 0 (List.ofFn (RadixDigitMoveBlockRows.unmove x))) 0) P G B hs)
      (BinaryAdjacentWidthMovementShared.constructedCoefficient*volume P G B u) := by
  have h := BinaryAdjacentWidthMovementShared.constructed_backward (BinaryRadixEqualShared.input (BinaryAdjacentWidthPrefixShared.output caller P G B hs)) (movementFocus focus)
    (equalSlot (prefixSlot payload)) P G B u hs (fun _ => blank) x hP hG hB hv hc
    (prepared_sources caller focus P G B hs hsrc)
    (by simpa only [BinaryRadixEqualShared.input,BinaryAdjacentWidthPrefixShared.output,equalSlot,prefixSlot,Tapes.append,Fin.addCases_left] using ht)
    (by simpa only [BinaryRadixEqualShared.input,BinaryAdjacentWidthPrefixShared.output,equalSlot,prefixSlot,Tapes.append,Fin.addCases_left] using hh)
  simp only [BinaryRadixEqualShared.input,equalSlot,SharedPlacementAlphabet.setTape_append_left,prefix_setTape] at h
  exact h

/-- Complete longer-H direction from the four original physical headers. -/
theorem longH_runs (caller : Tapes t prime) (focus : Fin 4 → Fin t) (payload : Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hsrc : Sources caller focus hs)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P (2*2^u) G (2^u) B) → Bool)
    (ht : caller.tape payload = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head payload = 0) :
    HoareTime (longHProgram focus payload) (fun z => z = input caller)
      (fun z => z = input (setTape caller payload
        (BinaryRadixRangePrepareAlphabet.word
          (BinaryAdjacentWidthInterchange.transpose (fun i => bitSymbol (x i)))) 0)) (cost P G B u hs) := by
  let wx := fun i => bitSymbol (a := prime) (x i)
  let midword := BinaryRadixRangePrepareAlphabet.word
    (RadixRangePadding.transpose (BinaryAdjacentWidthInterchange.equalInput wx))
  let after := setTape caller payload midword 0
  have h1 := setup_runs caller focus P G B u hs hP hG hB hv hc hsrc
  have heqin : caller.tape payload = BinaryRadixRangePrepareAlphabet.word
      (fun i => bitSymbol (BinaryAdjacentWidthInterchange.equalInput x i)) := by
    change caller.tape payload = putWord (fun _ => blank) 0
      (List.ofFn (BinaryAdjacentWidthInterchange.equalInput wx))
    rw [BinaryAdjacentWidthInterchange.equalInput_word]
    exact ht
  have h2 := equal_runs caller focus payload P G B u hs hP hG hB hv hc hsrc
    (BinaryAdjacentWidthInterchange.equalInput x) heqin hh
  have hsafter := source_changed caller focus payload hs hsrc hh midword
  have h3 := forward_runs after focus payload P G B u hs hP hG hB hv hc hsafter
    (BinaryAdjacentWidthInterchange.afterEqual wx)
    (by
      simp only [after,setTape,Function.update_self]
      change midword = putWord (fun _ => blank) 0
        (List.ofFn (BinaryAdjacentWidthInterchange.afterEqual wx))
      rw [BinaryAdjacentWidthInterchange.afterEqual_word]
      rfl) (by simp [after,setTape])
  rw [BinaryAdjacentWidthInterchange.move_afterEqual_word] at h3
  simp only [after,SharedPlacementAlphabet.setTape_setTape] at h3
  have h4 := cleanup_runs (setTape caller payload
      (BinaryRadixRangePrepareAlphabet.word (BinaryAdjacentWidthInterchange.transpose wx)) 0)
    focus P G B u hs hP hG hB hv hc
  apply (((h1.seq h2).seq h3).seq h4).consequence (fun _ h => h) (fun _ h => h)
  unfold cost
  omega

/-- Boolean reindexing of the physical inverse digit move. -/
def afterUnmoveBits {P N G B : ℕ}
    (y : Fin (BinaryAdjacentWidthInterchange.volume P N G (2*N) B) → Bool) :
    Fin (RadixRangePadding.volume (P*2) N G B) → Bool := fun z =>
  let pqse := finProdFinEquiv.symm (Fin.cast (BinaryAdjacentWidthInterchange.move_input_volume P N G B).symm z)
  let pq := finProdFinEquiv.symm pqse.1
  let se := finProdFinEquiv.symm pqse.2
  y (Fin.cast (BinaryAdjacentWidthInterchange.move_output_volume P N G B)
    (RecursiveInterchangeRows.pack (RecursiveInterchangeRows.pack
      (RecursiveInterchangeRows.pack pq.1 se.1) pq.2) se.2))

theorem afterUnmoveBits_encoded {P N G B : ℕ}
    (y : Fin (BinaryAdjacentWidthInterchange.volume P N G (2*N) B) → Bool) :
    (fun i => bitSymbol (a := prime) (afterUnmoveBits y i)) =
      BinaryAdjacentWidthInterchange.afterUnmove (fun i => bitSymbol (a := prime) (y i)) := rfl

/-- Complete longer-D direction; movement precedes the equal-width call. -/
theorem longD_runs (caller : Tapes t prime) (focus : Fin 4 → Fin t) (payload : Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hsrc : Sources caller focus hs)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P (2^u) G (2*2^u) B) → Bool)
    (ht : caller.tape payload = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head payload = 0) :
    HoareTime (longDProgram focus payload) (fun z => z = input caller)
      (fun z => z = input (setTape caller payload
        (BinaryRadixRangePrepareAlphabet.word
          (BinaryAdjacentWidthInterchange.transpose (fun i => bitSymbol (x i)))) 0)) (cost P G B u hs) := by
  let wx := fun i => bitSymbol (a := prime) (x i)
  let midword := BinaryRadixRangePrepareAlphabet.word
    (BinaryAdjacentWidthInterchange.afterUnmove wx)
  let after := setTape caller payload midword 0
  have h1 := setup_runs caller focus P G B u hs hP hG hB hv hc hsrc
  have h2 := backward_runs caller focus payload P G B u hs hP hG hB hv hc hsrc
    (BinaryAdjacentWidthInterchange.moveInput wx)
    (by rw [BinaryAdjacentWidthInterchange.moveInput_word]; exact ht) hh
  rw [BinaryAdjacentWidthInterchange.unmove_word] at h2
  have hsafter := source_changed caller focus payload hs hsrc hh midword
  have h3 := equal_runs after focus payload P G B u hs hP hG hB hv hc hsafter
    (afterUnmoveBits x)
    (by rw [afterUnmoveBits_encoded]; simp only [after,setTape,Function.update_self]; rfl) (by simp [after,setTape])
  rw [afterUnmoveBits_encoded] at h3
  unfold BinaryRadixRangePrepareAlphabet.word at h3
  rw [BinaryAdjacentWidthInterchange.equal_afterUnmove_word] at h3
  simp only [after,SharedPlacementAlphabet.setTape_setTape] at h3
  have h4 := cleanup_runs (setTape caller payload
      (BinaryRadixRangePrepareAlphabet.word (BinaryAdjacentWidthInterchange.transpose wx)) 0)
    focus P G B u hs hP hG hB hv hc
  apply (((h1.seq h2).seq h3).seq h4).consequence (fun _ h => h) (fun _ h => h)
  unfold cost
  omega

/-- Adjacent-width wrappers retain the certified exponent; descriptor
construction, copying, movement and all inverse cleanup have been charged. -/
theorem uniform_bound : ∃ C : ℝ, 0 < C ∧ ∀ (P G B u : ℕ) (hs : Fin 4 → List Bool),
    0 < P → 0 < G → 0 < B →
    (∀ i, Counter.value (hs i) = values P G B u i) →
    (∀ i, GrowingCounterData.Canonical (hs i)) →
    (cost P G B u hs : ℝ) ≤ C*(volume P G B u : ℝ)*
      ((max 1 u : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := BinaryRadixEqualShared.uniform_bound
  let L := BinaryAdjacentWidthPrefixShared.coefficient +
    BinaryAdjacentWidthMovementShared.constructedCoefficient + 213
  refine ⟨C+(L : ℝ),by have hL := Nat.cast_nonneg (α := ℝ) L; linarith,?_⟩
  intro P G B u hs hP hG hB hv hc
  have hb := hbound (P*2) G B u (BinaryAdjacentWidthPrefixShared.equalWords P G B hs)
    (by omega) hG hB (equal_values P G B u hs hv) (equal_canonical P G B hs hc)
  have he : RadixRangePadding.volume (P*2) (2^u) G B = volume P G B u := by
    unfold RadixRangePadding.volume volume
    ring
  rw [he] at hb
  have hVnat := (BinaryAdjacentWidthHeadersShared.volume_bounds P G B u hP hG hB).1
  have hV : 1 ≤ (volume P G B u : ℝ) := by exact_mod_cast hVnat
  have hp : 1 ≤ ((max 1 u : ℕ) : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 u) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hlin := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α := ℝ) (volume P G B u))
  have hL := Nat.cast_nonneg (α := ℝ) L
  have hh := mul_le_mul_of_nonneg_left hlin hL
  have hcost : cost P G B u hs ≤ BinaryRadixEqualShared.cost (P*2) G B u
      (BinaryAdjacentWidthPrefixShared.equalWords P G B hs) + L*volume P G B u := by
    unfold cost L
    simp only [Nat.add_mul]
    omega
  have hcR := (Nat.cast_le (α := ℝ)).mpr hcost
  simp only [Nat.cast_add,Nat.cast_mul] at hcR
  nlinarith only [hb,hcR,hh]

end
end IntegerMultBounds.Machine.BinaryAdjacentWidthRun
