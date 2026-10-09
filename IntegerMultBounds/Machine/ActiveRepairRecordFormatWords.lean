import IntegerMultBounds.Machine.ActiveRepairRecordFormatRecord

namespace IntegerMultBounds.Machine.ActiveRepairRecordFormatWords

def raw (chunks : List (List Bool)) : List (Fin 4) := chunks.flatten.map bitSymbol
def records (chunks : List (List Bool)) : List Partition.Record := chunks.map (fun bits => ⟨false,bits⟩)
def encoded (chunks : List (List Bool)) := Partition.encode (records chunks)

 theorem raw_append (xs ys : List (List Bool)) : raw (xs++ys)=raw xs++raw ys := by
  simp [raw]
 theorem encoded_append (xs ys : List (List Bool)) : encoded (xs++ys)=encoded xs++encoded ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [encoded,records,Partition.encode,List.append_assoc] using congrArg (fun z => Partition.recordWord false x ++ z) ih
 theorem encoded_singleton (xs : List Bool) : encoded [xs]=Partition.recordWord false xs := by
  simp [encoded,records,Partition.encode]
 theorem raw_singleton (xs : List Bool) : raw [xs]=xs.map bitSymbol := by simp [raw]

 theorem putWord_idem {a : ℕ} (f : ℤ → Fin (a+4)) (p : ℤ) (xs : List (Fin (a+4))) :
    putWord (putWord f p xs) p xs=putWord f p xs := by
  induction xs generalizing f p with
  | nil => rfl
  | cons x xs ih =>
    simp only [putWord]
    rw [putWord_update_before _ (p+1) p x xs (by omega),ih]
    exact Function.update_idem _ _ _

 theorem segment_self {a : ℕ} (f : ℤ → Fin (a+4)) (p : ℤ) (pre xs post : List (Fin (a+4))) :
    putWord (putWord f p (pre++xs++post)) (p+pre.length) xs=putWord f p (pre++xs++post) := by
  have ht : putWord f p (pre++xs++post)=
      putWord (putWord (putWord f p pre) (p+pre.length+xs.length) post) (p+pre.length) xs := by
    rw [List.append_assoc,←putWord_append_forward,putWord_append]
  rw [ht]
  exact putWord_idem _ _ _

 theorem raw_decompose (chunks : List (List Bool)) (i : ℕ) (hi : i<chunks.length) :
    raw chunks=raw (chunks.take i)++chunks[i].map bitSymbol++raw (chunks.drop (i+1)) := by
  calc
    _=raw (chunks.take i)++raw (chunks.drop i) := by
      rw [←raw_append]
      exact congrArg raw (List.take_append_drop i chunks).symm
    _=_ := by rw [List.drop_eq_getElem_cons hi]; simp only [raw,List.flatten_cons,List.map_append,List.append_assoc]

 theorem raw_take_succ (chunks : List (List Bool)) (i : ℕ) (hi : i<chunks.length) :
    raw (chunks.take (i+1))=raw (chunks.take i)++chunks[i].map bitSymbol := by
  rw [List.take_succ_eq_append_getElem hi,raw_append,raw_singleton]

 theorem encoded_take_succ (chunks : List (List Bool)) (i : ℕ) (hi : i<chunks.length) :
    encoded (chunks.take (i+1))=encoded (chunks.take i)++Partition.recordWord false chunks[i] := by
  rw [List.take_succ_eq_append_getElem hi,encoded_append,encoded_singleton]

end IntegerMultBounds.Machine.ActiveRepairRecordFormatWords
