import IntegerMultBounds.Machine.SymbolTripleClean
import IntegerMultBounds.Machine.Alphabet
import IntegerMultBounds.Machine.TwoTapeAt
import IntegerMultBounds.Machine.ActiveTargetRotation

/-! Clean physical conversion at arbitrary distinct caller slots and in the
stage alphabet. Only the two selected tapes are active, so arbitrary original
headers, controller registers and all other tapes are retained literally. -/
namespace IntegerMultBounds.Machine.SymbolTriplePlaced
noncomputable section
variable {a t B : ℕ}

def encoding (ha : 2≤a) : Alphabet.Encoding 2 a where
  encode := fun x => ⟨x.val,by have := x.isLt; omega⟩
  decode := fun x => if h : x.val<6 then ⟨x.val,h⟩ else blank
  decode_encode := by intro x; simp [x.isLt]

def mapTape (ha : 2≤a) (f : ℤ → Fin 6) : ℤ → Fin (a+4) :=
  fun z => (encoding ha).encode (f z)
def native (ha : 2≤a) (xs : Fin B → Fin 6) := mapTape ha (SymbolTripleClean.word (List.ofFn xs))
def boolean (xs : Fin B → Fin 6) : ℤ → Fin (a+4) := ActiveTargetRotation.word (SymbolTripleArray.triple xs)

theorem map_word (ha : 2≤a) (xs : List (Fin 6)) :
    mapTape ha (SymbolTripleClean.word xs)=putWord (fun _ => blank) 0 (xs.map (encoding ha).encode) := by
  have hm (f : ℤ → Fin 6) (p : ℤ) (ys : List (Fin 6)) :
      mapTape ha (putWord f p ys)=putWord (mapTape ha f) p (ys.map (encoding ha).encode) := by
    induction ys generalizing p with
    | nil => rfl
    | cons y ys ih =>
      funext z
      by_cases hz : z=p
      · subst z; simp [mapTape,putWord]
      · simp only [putWord,List.map_cons,Function.update_of_ne hz,mapTape]
        exact congrFun (ih (p+1)) z
  exact hm (fun _ => blank) 0 xs

theorem map_boolean (ha : 2≤a) (xs : Fin B → Fin 6) :
    mapTape ha (SymbolTripleClean.word (SymbolTripleStream.word (List.ofFn xs)))=boolean xs := by
  rw [map_word,←SymbolTripleArray.triple_word,List.map_map]
  unfold boolean ActiveTargetRotation.word
  rw [List.map_ofFn]
  rfl

private theorem mapped {states cost : ℕ} {M : Program 2 states 2} {v w : Tapes 2 2}
    (ha : 2≤a) (h : HoareTime M (fun x => x=v) (fun x => x=w) cost) :
    HoareTime (Alphabet.program (encoding ha) M)
      (fun x => x=Alphabet.mapTapes (encoding ha) v)
      (fun x => x=Alphabet.mapTapes (encoding ha) w) cost := by
  apply (Alphabet.map_hoare (encoding ha) h).consequence _ _ le_rfl
  · rintro x rfl; exact ⟨_,rfl,rfl⟩
  · rintro x ⟨v,rfl,rfl⟩; rfl

private theorem map_copy (ha : 2≤a) (f g : ℤ → Fin 6) :
    Alphabet.mapTapes (encoding ha) (Copy.tapes f g 0 0)=
      Copy.tapes (mapTape ha f) (mapTape ha g) 0 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def encodeProgram (ha : 2≤a) (src dst : Fin t) (hne : src≠dst) :=
  TwoTapeAt.program (Alphabet.program (encoding ha) SymbolTripleClean.encodeProgram) src dst hne
def decodeProgram (ha : 2≤a) (src dst : Fin t) (hne : src≠dst) :=
  TwoTapeAt.program (Alphabet.program (encoding ha) SymbolTripleClean.decodeProgram) src dst hne

theorem encode_runs (ha : 2≤a) (v : Tapes t a) (src dst : Fin t) (hne : src≠dst)
    (xs : Fin B → Fin 6) (hn : ∀ j,xs j≠blank)
    (hs : v.tape src=native ha xs ∧ v.head src=0)
    (hd : v.tape dst=(fun _ => blank) ∧ v.head dst=0) :
    HoareTime (encodeProgram ha src dst hne) (fun w => w=v)
      (fun w => w=TwoTapeAt.result v src dst (fun _ => blank) (boolean xs) 0 0) (13*B+10) := by
  have h := mapped ha (SymbolTripleClean.encode_runs xs hn)
  rw [map_copy,map_copy,map_boolean] at h
  exact TwoTapeAt.runs _ src dst hne v _ _ _ _ 0 0 0 0 hs hd h

theorem decode_runs (ha : 2≤a) (v : Tapes t a) (src dst : Fin t) (hne : src≠dst)
    (xs : Fin B → Fin 6) (hn : ∀ j,xs j≠blank)
    (hs : v.tape src=boolean xs ∧ v.head src=0)
    (hd : v.tape dst=(fun _ => blank) ∧ v.head dst=0) :
    HoareTime (decodeProgram ha src dst hne) (fun w => w=v)
      (fun w => w=TwoTapeAt.result v src dst (fun _ => blank) (native ha xs) 0 0) (19*B+10) := by
  have h := mapped ha (SymbolTripleClean.decode_runs xs hn)
  rw [map_copy,map_copy,map_boolean] at h
  exact TwoTapeAt.runs _ src dst hne v _ _ _ _ 0 0 0 0 hs hd h

end
end IntegerMultBounds.Machine.SymbolTriplePlaced
