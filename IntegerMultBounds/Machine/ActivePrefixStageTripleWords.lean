import IntegerMultBounds.Machine.ActivePrefixStageTripleEndpoint
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsShape
import IntegerMultBounds.Machine.SymbolTriplePlaced

/-! Full physical word representation when payload capacity is a multiple of
three. Native records are flattened in original row-major address order; their
Boolean codes are exactly the raw input/output words of the actual stage. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageTripleWords
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageFullSelected (geometry Address)
open ActivePrefixDirtyControlGlobalSwap (index)
open ActivePrefixStageTripleTransport
open ActiveRepairLayoutRecordsShape
variable {s : Shape} {B : ℕ}

def count (d : Inputs s) := d.rows*(addressShape s).recordWidth
abbrev Record (d : Inputs s) := RecordAddress s ((geometry d).n*(geometry d).b)
  ((geometry d).n*(geometry d).q) (geometry d).before (geometry d).after d.rows

def recordEquiv (d : Inputs s) : Record d ≃ Fin (count d) :=
  CompactActiveTargetLayout.indexEquiv (addressShape s) ((geometry d).n*(geometry d).b)
    ((geometry d).n*(geometry d).q) (geometry d).before (geometry d).after d.rows
    (geometry d).compactFits (geometry d).activeSize

def cellAt (d : Inputs s) (r : Record d) (p : Fin s.payload) : Address d :=
  cell s ((geometry d).n*(geometry d).b) ((geometry d).n*(geometry d).q)
    (geometry d).before (geometry d).after d.rows r p

def rows (d : Inputs s) (xs : Address d → Fin B → Fin 6) (r : Fin (count d)) : Fin B → Fin 6 :=
  xs (base d (cellAt d ((recordEquiv d).symm r) ⟨0,by have := d.hrecord; omega⟩))

def nativeArray (d : Inputs s) (xs : Address d → Fin B → Fin 6)
    (k : Fin (count d*B)) : Fin 6 :=
  let rj := finProdFinEquiv.symm k
  rows d xs rj.1 rj.2

theorem volume_eq (d : Inputs s) (h : s.payload=B*3+0) :
    count d*(B*3)=d.rows*s.recordWidth := by
  have he := record_count s d.rows
  simpa only [count,h,Nat.add_zero] using he

private theorem word_append (xs ys : List (Fin 6)) :
    SymbolTripleStream.word (xs++ys)=SymbolTripleStream.word xs++SymbolTripleStream.word ys := by
  simp [SymbolTripleStream.word,List.map_append,List.flatten_append]

private theorem word_flatten (rs : List (List (Fin 6))) :
    SymbolTripleStream.word rs.flatten=(rs.map SymbolTripleStream.word).flatten := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [List.flatten_cons,word_append,ih,List.map_cons]

private theorem native_word (d : Inputs s) (xs : Address d → Fin B → Fin 6) :
    SymbolTripleStream.word (List.ofFn (nativeArray d xs))=
      (List.ofFn (fun r => SymbolTripleStream.word (List.ofFn (rows d xs r)))).flatten := by
  have he : List.ofFn (nativeArray d xs)=(List.ofFn (fun r => List.ofFn (rows d xs r))).flatten := by
    rw [List.ofFn_mul]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext r
    apply congrArg List.ofFn
    funext j
    have hj : (⟨r.val*B+j.val,by
      have hm := Nat.mul_le_mul_right B (Nat.succ_le_of_lt r.isLt)
      nlinarith [j.isLt]⟩ : Fin (count d*B))=finProdFinEquiv (r,j) := by
      apply Fin.ext; simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
    rw [hj]
    simp [nativeArray]
  rw [he,word_flatten,List.map_ofFn]
  rfl

/-- Exact full raw Boolean word, with the native input supplied in canonical
record order rather than through an existential serialization assumption. -/
theorem encoded_word (d : Inputs s) (h : s.payload=B*3+0)
    (xs : Address d → Fin B → Fin 6) :
    (List.ofFn (encodedArray d h xs (fun _ j => Fin.elim0 j))).map (bitSymbol (a:=2))=
      SymbolTripleStream.word (List.ofFn (nativeArray d xs)) := by
  rw [native_word]
  have hv := volume_eq d h
  rw [List.ofFn_congr hv.symm,List.map_ofFn,List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext r
  rw [←SymbolTripleArray.triple_word,List.map_ofFn]
  apply congrArg List.ofFn
  funext p
  change bitSymbol (encodedArray d h xs (fun _ j => Fin.elim0 j)
    (Fin.cast hv ⟨r.val*(B*3)+p.val,_⟩))=
    bitSymbol (SymbolTripleArray.triple (rows d xs r) p)
  apply congrArg (bitSymbol (a:=2))
  let z : Fin s.payload := Fin.cast h.symm (Fin.castAdd 0 p)
  have hk : Fin.cast hv ⟨r.val*(B*3)+p.val,by
      have hm := Nat.mul_le_mul_right (B*3) (Nat.succ_le_of_lt r.isLt)
      nlinarith [p.isLt]⟩=
      index s (geometry d) (cellAt d ((recordEquiv d).symm r) z) := by
    apply Fin.ext
    have hi := cell_index s ((geometry d).n*(geometry d).b) ((geometry d).n*(geometry d).q)
      (geometry d).before (geometry d).after d.rows (geometry d).compactFits
      (geometry d).activeSize ((recordEquiv d).symm r) z
    change _=(recordEquiv d ((recordEquiv d).symm r)).val*s.payload+z.val at hi
    rw [Equiv.apply_symm_apply] at hi
    simpa only [Fin.val_cast,h,Nat.add_zero,z,Fin.val_castAdd,cellAt,index] using hi.symm
  rw [hk,encoded_entry]
  simp only [z,cellAt,cell,Fin.cast_cast,Fin.cast_eq_self,SymbolTripleArray.record_symbol]
  rfl

/-- The converter output and the stage's actual raw Boolean tape are identical,
including all cells outside the word and the original row-major ordering. -/
theorem raw_word {a : ℕ} (d : Inputs s) (h : s.payload=B*3+0)
    (xs : Address d → Fin B → Fin 6) :
    ActiveTargetRotation.word (a:=a) (encodedArray d h xs (fun _ j => Fin.elim0 j))=
      SymbolTriplePlaced.boolean (a:=a) (nativeArray d xs) := by
  have hi : Function.Injective (bitSymbol (a:=2)) := by
    intro b c he
    cases b <;> cases c <;> simp_all [bitSymbol]
  have he := encoded_word d h xs
  rw [←SymbolTripleArray.triple_word] at he
  have hb := List.map_injective_iff.mpr hi he
  have ht := congrArg (fun bs : List Bool =>
    putWord (fun _ => (blank : Fin (a+4))) 0 (bs.map bitSymbol)) hb
  simpa only [List.map_ofFn,Function.comp_def,ActiveTargetRotation.word,SymbolTriplePlaced.boolean] using ht

/-- The complete physical stage's output is the encoded word of explicitly
computed native output coefficients, so the decoder has a real source word. -/
theorem result_word {a : ℕ} (d : Inputs s) (h : s.payload=B*3+0)
    (xs : Address d → Fin B → Fin 6) :
    ActiveTargetRotation.word (a:=a)
      (ActivePrefixStageRuntimeData.result d (encodedArray d h xs (fun _ j => Fin.elim0 j)))=
      SymbolTriplePlaced.boolean (a:=a)
        (nativeArray d (xs ∘ ActivePrefixStageRuntimeSelected.destination d)) := by
  rw [ActivePrefixStageTripleEndpoint.result_encoded]
  exact raw_word d h _

theorem native_nonblank (d : Inputs s) (xs : Address d → Fin B → Fin 6)
    (hn : ∀ i j,xs i j≠blank) : ∀ k,nativeArray d xs k≠blank := by
  intro k
  exact hn _ _

end
end IntegerMultBounds.Machine.ActivePrefixStageTripleWords
