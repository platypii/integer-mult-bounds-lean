import IntegerMultBounds.Machine.ButterflyRecord
import IntegerMultBounds.Machine.CyclicRowCycle

/-! Literal paired coefficient streams and their clean per-record loop states.
The contexts used by the record machine are derived from the actual flattened
input arrays, rather than supplied per-record tape representations. -/
namespace IntegerMultBounds.Machine.ButterflyStreamData
noncomputable section
open DelimitedRadixRecord (Context complex)
open CyclicRowCycle (rowPrefix prefix_succ source_row)
variable {n : ℕ}

abbrev Coefficient := List (Fin 2) × List (Fin 2)
def encoded (x : Coefficient) : List (Fin 6) := complex x.1 x.2

def componentWords (a b : Coefficient) : ℕ → List (Fin 2)
  | 0 => a.1
  | 1 => a.2
  | 2 => b.1
  | _ => b.2

def result (a b : Coefficient) : Fin 2 → Coefficient :=
  ![(ButterflyNumerator.words 0 (componentWords a b),ButterflyNumerator.words 1 (componentWords a b)),
    (ButterflyNumerator.words 2 (componentWords a b),ButterflyNumerator.words 3 (componentWords a b))]

def full (f : ℤ → Fin 6) (p : ℤ) (xs : Fin n → Coefficient) :=
  putWord f p (List.ofFn (fun i => encoded (xs i))).flatten

def position (p : ℤ) (xs : Fin n → Coefficient) (k : ℕ) : ℤ :=
  p+(rowPrefix (fun i => encoded (xs i)) k).length

def prefixTape (f : ℤ → Fin 6) (p : ℤ) (xs : Fin n → Coefficient) (k : ℕ) :=
  putWord f p (rowPrefix (fun i => encoded (xs i)) k)

def context (f : ℤ → Fin 6) (p : ℤ) (xs : Fin n → Coefficient) (i : Fin n) : Context 2 where
  background := full f p xs
  origin := position p xs i.val
  front := []
  back := []
  re := (xs i).1
  im := (xs i).2

theorem context_tape (f : ℤ → Fin 6) (p : ℤ) (xs : Fin n → Coefficient) (i : Fin n) :
    (context f p xs i).tape=full f p xs := by
  simp only [Context.tape,context,List.nil_append,List.append_nil]
  exact source_row f p (fun i => encoded (xs i)) i

theorem context_start (f : ℤ → Fin 6) (p : ℤ) (xs : Fin n → Coefficient) (i : Fin n) :
    (context f p xs i).start=position p xs i.val := by simp [Context.start,context]

theorem context_components (f g : ℤ → Fin 6) (p r : ℤ) (a b : Fin n → Coefficient) (i : Fin n) :
    ButterflyRecordRead.components (context f p a i) (context g r b i)=componentWords (a i) (b i) := by
  funext k
  rcases k with _|k
  · rfl
  rcases k with _|k
  · rfl
  rcases k with _|k <;> rfl

def streams (f g : Fin 2 → ℤ → Fin 6) (p r : Fin 2 → ℤ)
    (a b : Fin n → Coefficient) (k : ℕ) : Tapes 4 2 :=
  ⟨![position (p 0) a k,position (p 1) b k,
      position (r 0) (fun i => result (a i) (b i) 0) k,
      position (r 1) (fun i => result (a i) (b i) 1) k],
    ![full (f 0) (p 0) a,full (f 1) (p 1) b,
      prefixTape (g 0) (r 0) (fun i => result (a i) (b i) 0) k,
      prefixTape (g 1) (r 1) (fun i => result (a i) (b i) 1) k]⟩

def state (f g : Fin 2 → ℤ → Fin 6) (p r : Fin 2 → ℤ)
    (a b : Fin n → Coefficient) (k : ℕ) : Tapes 52 2 :=
  (streams f g p r a b k).append (RadixLinearCombinationBootstrap.empty 48)

def outs (g : Fin 2 → ℤ → Fin 6) (r : Fin 2 → ℤ) (a b : Fin n → Coefficient) (k : ℕ) :
    Fin 2 → ℤ → Fin 6 := fun j => prefixTape (g j) (r j) (fun i => result (a i) (b i) j) k

def outputPositions (r : Fin 2 → ℤ) (a b : Fin n → Coefficient) (k : ℕ) : Fin 2 → ℤ :=
  fun j => position (r j) (fun i => result (a i) (b i) j) k

theorem record_input (f g : Fin 2 → ℤ → Fin 6) (p r : Fin 2 → ℤ)
    (a b : Fin n → Coefficient) (i : Fin n) :
    ButterflyRecordRead.input (context (f 0) (p 0) a i) (context (f 1) (p 1) b i)
      (outs g r a b i.val) (outputPositions r a b i.val)=state f g p r a b i.val := by
  simp only [ButterflyRecordRead.input,ButterflyRecordRead.streams,context_tape,context_start,
    state,streams,outs,outputPositions]

/-- Consecutive source positions differ by the actual serialized record size. -/
theorem position_succ (p : ℤ) (xs : Fin n → Coefficient) (i : Fin n) :
    position p xs (i.val+1)=position p xs i.val+(xs i).1.length+(xs i).2.length+2 := by
  simp only [position,prefix_succ,List.length_append,encoded,complex,
    DelimitedRadixRecord.field_length,Nat.cast_add,Nat.cast_one]
  omega

/-- Emission appends precisely the next result record to the accumulated prefix. -/
theorem prefixTape_succ (f : ℤ → Fin 6) (p : ℤ) (xs : Fin n → Coefficient) (i : Fin n) :
    putWord (prefixTape f p xs i.val) (position p xs i.val) (encoded (xs i))=
      prefixTape f p xs (i.val+1) := by
  simp only [prefixTape,position,prefix_succ,putWord_append_forward]

/-- The record machine's four stream endpoints are exactly the next loop state. -/
theorem record_output (f g : Fin 2 → ℤ → Fin 6) (p r : Fin 2 → ℤ)
    (a b : Fin n → Coefficient) (i : Fin n) :
    ButterflyRecord.output (context (f 0) (p 0) a i) (context (f 1) (p 1) b i)
      (outs g r a b i.val) (outputPositions r a b i.val)=state f g p r a b (i.val+1) := by
  unfold ButterflyRecord.output ButterflyRecordEmit.output state
  rw [context_components]
  apply congrArg (fun v : Tapes 4 2 => v.append (RadixLinearCombinationBootstrap.empty 48))
  apply Placement.Tapes.ext'
  · intro k
    fin_cases k <;> simp [ButterflyRecordEmit.nextStreams,SharedPlacementAlphabet.setTape,
      ButterflyRecordRead.afterStreams,Context.start,streams,outs,outputPositions,position_succ,
      context,result]
  · intro k
    fin_cases k <;> simp [ButterflyRecordEmit.nextStreams,SharedPlacementAlphabet.setTape,
      ButterflyRecordRead.afterStreams,context_tape,streams,outs,outputPositions]
    · exact prefixTape_succ _ _ (fun i => result (a i) (b i) 0) i
    · exact prefixTape_succ _ _ (fun i => result (a i) (b i) 1) i

end
end IntegerMultBounds.Machine.ButterflyStreamData
