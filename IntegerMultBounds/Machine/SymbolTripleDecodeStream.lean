import IntegerMultBounds.Machine.SymbolTripleDecode
import IntegerMultBounds.Machine.SymbolTripleStream
import IntegerMultBounds.Machine.CyclicRowCycle

/-! A fixed physical inverse of the Boolean triple representation. Every
coefficient symbol is reconstructed from its three actual tape cells, with
linear cost and exact whole-word output rather than a supplied decode oracle. -/
namespace IntegerMultBounds.Machine.SymbolTripleDecodeStream
noncomputable section
open SymbolTripleEncode (encoded)
open SymbolTripleStream (word)
variable {n : ℕ}

def source (f : ℤ → Fin 6) (p : ℤ) (xs : Fin n → Fin 6) := putWord f p (word (List.ofFn xs))
def state (f g : ℤ → Fin 6) (p r : ℤ) (xs : Fin n → Fin 6) (i : ℕ) :=
  Copy.tapes (source f p xs) (putWord g r ((List.ofFn xs).take i)) (p+3*i) (r+i)
def test (sy : Fin 2 → Fin 6) : Bool := sy 0 != blank
def program := whileLoop SymbolTripleDecode.body test

private theorem prefix_word (xs : Fin n → Fin 6) (i : ℕ) :
    CyclicRowCycle.rowPrefix (fun j => encoded (xs j)) i=word ((List.ofFn xs).take i) := by
  simp [CyclicRowCycle.rowPrefix,word,List.map_ofFn,Function.comp_def]

private theorem read_code (f : ℤ → Fin 6) (p : ℤ) (xs : Fin n → Fin 6) (j : Fin n) (i : Fin 3) :
    source f p xs (p+3*j.val+i.val)=bitSymbol (SymbolTripleEncode.bit (xs j) i) := by
  have hlen : (CyclicRowCycle.rowPrefix (fun j => encoded (xs j)) j.val).length=3*j.val := by
    rw [prefix_word,SymbolTripleStream.word_length,List.length_take,List.length_ofFn,Nat.min_eq_left j.isLt.le]
  have hs := CyclicRowCycle.source_row f p (fun j => encoded (xs j)) j
  have hw : word (List.ofFn xs)=(List.ofFn (fun j => encoded (xs j))).flatten := by
    simp [word,List.map_ofFn,Function.comp_def]
  rw [←hw] at hs
  change putWord (source f p xs) (p+(CyclicRowCycle.rowPrefix (fun j => encoded (xs j)) j.val).length)
    (encoded (xs j)) = source f p xs at hs
  rw [hlen] at hs
  push_cast at hs
  have hi : i.val < (encoded (xs j)).length := by simp [encoded,SymbolTripleEncode.code]
  have hg := WordSegments.get (source f p xs) (p+3*j.val) (encoded (xs j)) i.val hi
  rw [hs] at hg
  fin_cases i <;> simpa [encoded,SymbolTripleEncode.code] using hg

private theorem one_record (f g : ℤ → Fin 6) (p r : ℤ) (xs : Fin n → Fin 6) (j : Fin n) :
    HoareTime SymbolTripleDecode.body (fun v => v=state f g p r xs j.val)
      (fun v => v=state f g p r xs (j.val+1)) 7 := by
  have h := SymbolTripleDecode.body_runs (xs j) (source f p xs)
    (putWord g r ((List.ofFn xs).take j.val)) (p+3*j.val) (r+j.val)
    (read_code f p xs j)
  have hl : ((List.ofFn xs).take j.val).length=j.val := by simp
  have ht : Function.update (putWord g r ((List.ofFn xs).take j.val)) (r+j.val) (xs j)=
      putWord g r ((List.ofFn xs).take (j.val+1)) := by
    rw [List.take_succ_eq_append_getElem (by simp),List.getElem_ofFn,←putWord_append_forward,hl]
    rfl
  rw [ht] at h
  have hp : p+3*((j.val+1:ℕ):ℤ)=p+3*j.val+3 := by push_cast; ring
  have hr : r+((j.val+1:ℕ):ℤ)=r+j.val+1 := by push_cast; ring
  simpa only [state,hp,hr] using h

/-- The decoder also handles the native blank symbol inside an encoded word:
its Boolean triple consists of three nonblank false-bit cells. -/
theorem runs (f g : ℤ → Fin 6) (p r : ℤ) (xs : Fin n → Fin 6)
    (hblank : f (p+3*n)=blank) :
    HoareTime program (fun v => v=Copy.tapes (source f p xs) g p r)
      (fun v => v=Copy.tapes (source f p xs) (putWord g r (List.ofFn xs)) (p+3*n) (r+n)) (9*n) := by
  have h := while_chain_hoare SymbolTripleDecode.body test (state f g p r xs) (fun _ => 7) n
    (fun j hj => one_record f g p r xs ⟨j,hj⟩)
    (by
      intro j hj
      change (source f p xs (p+3*j) != blank)=true
      have hr := read_code f p xs ⟨j,hj⟩ 0
      simp only [Fin.val_zero,Nat.cast_zero,add_zero] at hr
      rw [hr]
      cases SymbolTripleEncode.bit (xs ⟨j,hj⟩) 0 <;> simp [bitSymbol,blank])
    (by
      change (source f p xs (p+3*n) != blank)=false
      have hl : (word (List.ofFn xs)).length=3*n := by simp [SymbolTripleStream.word_length]
      rw [source,putWord_outside f p (p+3*n) _ (Or.inr (by rw [hl]; push_cast; rfl)),hblank]
      simp)
  dsimp only [state] at h
  rw [List.take_of_length_le (by simp : (List.ofFn xs).length ≤ n)] at h
  simpa [program,putWord,Nat.mul_comm] using h

end
end IntegerMultBounds.Machine.SymbolTripleDecodeStream
