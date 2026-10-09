import IntegerMultBounds.Machine.SymbolTripleEncode

/-! Actual stream execution of the fixed three-bit symbol representation. The
source is retained, arbitrary destination backgrounds are framed, and every
head movement and output write is included in the linear runtime. -/
namespace IntegerMultBounds.Machine.SymbolTripleStream
noncomputable section
open SymbolTripleEncode (encoded body)

def word (xs : List (Fin 6)) := (xs.map encoded).flatten

theorem word_length (xs : List (Fin 6)) : (word xs).length=3*xs.length := by
  induction xs with
  | nil => simp [word]
  | cons s xs ih =>
    simp only [word,List.map_cons,List.flatten_cons,List.length_append,encoded,
      List.length_map,SymbolTripleEncode.code_length,List.length_cons] at *
    omega

def state (f g : ℤ → Fin 6) (p r : ℤ) (xs : List (Fin 6)) (i : ℕ) :=
  Copy.tapes (putWord f p xs) (putWord g r (word (xs.take i))) (p+i) (r+3*i)

def test (sy : Fin 2 → Fin 6) : Bool := sy 0 != blank
def program := whileLoop body test

private theorem one_record (f g : ℤ → Fin 6) (p r : ℤ) (xs : List (Fin 6))
    (i : ℕ) (hi : i<xs.length) :
    HoareTime body (fun v => v=state f g p r xs i)
      (fun v => v=state f g p r xs (i+1)) 5 := by
  have h := SymbolTripleEncode.body_runs (putWord f p xs)
    (putWord g r (word (xs.take i))) (p+i) (r+3*i)
  rw [WordSegments.get f p xs i hi] at h
  have hp : (word (xs.take i)).length=3*i := by
    rw [word_length,List.length_take,Nat.min_eq_left (by omega)]
  have hw : word (xs.take (i+1))=word (xs.take i)++encoded xs[i] := by
    rw [List.take_succ_eq_append_getElem hi]
    unfold word
    rw [List.map_append,List.flatten_append]
    simp only [List.map_singleton,List.flatten_singleton]
  have ht : putWord (putWord g r (word (xs.take i))) (r+3*i) (encoded xs[i]) =
      putWord g r (word (xs.take (i+1))) := by
    rw [hw,←putWord_append_forward,hp]
    push_cast
    rfl
  rw [ht] at h
  have h1 : p+((i+1:ℕ):ℤ)=p+i+1 := by push_cast; ring
  have h2 : r+3*((i+1:ℕ):ℤ)=r+3*i+3 := by push_cast; ring
  simpa only [state,h1,h2] using h

/-- Actual delimiter-free coefficient source words have no blank interior.
Only the blank immediately after the supplied word terminates the scan. -/
theorem runs (f g : ℤ → Fin 6) (p r : ℤ) (xs : List (Fin 6))
    (hblank : f (p+xs.length)=blank) (hn : ∀ s∈xs,s≠blank) :
    HoareTime program (fun v => v=Copy.tapes (putWord f p xs) g p r)
      (fun v => v=Copy.tapes (putWord f p xs) (putWord g r (word xs))
        (p+xs.length) (r+3*xs.length)) (7*xs.length) := by
  have h := while_chain_hoare body test (state f g p r xs) (fun _ => 5) xs.length
    (fun i hi => one_record f g p r xs i hi)
    (by
      intro i hi
      change (putWord f p xs (p+i) != blank)=true
      rw [WordSegments.get f p xs i hi]
      exact bne_iff_ne.mpr (hn xs[i] (List.getElem_mem hi)))
    (by
      change (putWord f p xs (p+xs.length) != blank)=false
      rw [putWord_outside f p (p+xs.length) xs (Or.inr le_rfl),hblank]
      simp)
  simpa [state,program,word,putWord,Nat.mul_comm] using h

end
end IntegerMultBounds.Machine.SymbolTripleStream
