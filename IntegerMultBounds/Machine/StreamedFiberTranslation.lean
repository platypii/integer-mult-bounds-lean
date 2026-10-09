import IntegerMultBounds.Machine.BinaryOffsetStreamRead
import IntegerMultBounds.Machine.TranslationPreparedFamily

/-! Varying-offset payload rotations driven by a literal binary control stream.
One fixed reader installs each offset, then the actual translation constructs
its split lengths, rotates the fiber and clears derived metadata. -/
namespace IntegerMultBounds.Machine.StreamedFiberTranslation
open CountedCopyReuse (binary empty)
open MarkedWordCleanup (one)

def encoded (ws : List (List Bool)) : List (Fin 4) :=
  (ws.map (fun xs => xs.map bitSymbol ++ [blank])).flatten

theorem encoded_append (xs ys : List (List Bool)) : encoded (xs++ys) = encoded xs++encoded ys := by
  simp [encoded]

def cursor (ws : List (List Bool)) (r : ℤ) (i : ℕ) : ℤ := r+(encoded (ws.take i)).length
def offset (ws : List (List Bool)) (i : ℕ) : ℕ := Counter.value (ws[i]?.getD [])
def old (ws : List (List Bool)) : ℕ → List Bool
  | 0 => []
  | i+1 => ws[i]?.getD []

theorem old_succ (ws : List (List Bool)) (i : ℕ) (hi : i < ws.length) : old ws (i+1) = ws[i] := by
  simp [old,List.getElem?_eq_getElem hi]

theorem encoded_split (ws : List (List Bool)) (i : ℕ) (hi : i < ws.length) :
    encoded ws = encoded (ws.take i) ++ ws[i].map bitSymbol ++ ([blank]++encoded (ws.drop (i+1))) := by
  have h : ws.take i ++ [ws[i]] ++ ws.drop (i+1) = ws := by
    rw [← List.take_succ_eq_append_getElem hi,List.take_append_drop]
  conv_lhs => rw [← h,encoded_append,encoded_append]
  simp only [encoded,List.map_singleton,List.flatten_singleton,List.append_assoc]

theorem cursor_succ (ws : List (List Bool)) (r : ℤ) (i : ℕ) (hi : i < ws.length) :
    cursor ws r (i+1) = cursor ws r i+ws[i].length+1 := by
  rw [cursor,List.take_succ_eq_append_getElem hi,encoded_append]
  simp [encoded,cursor]
  omega

theorem stream_word (ws : List (List Bool)) (f : ℤ → Fin 4) (r : ℤ) (i : ℕ) (hi : i < ws.length) :
    putWord (putWord f r (encoded ws)) (cursor ws r i) (ws[i].map bitSymbol) = putWord f r (encoded ws) := by
  rw [encoded_split ws i hi]
  exact WordSegments.middle _ _ _ _ _

theorem stream_delimiter (ws : List (List Bool)) (f : ℤ → Fin 4) (r : ℤ)
    (i : ℕ) (hi : i < ws.length) :
    putWord f r (encoded ws) (cursor ws r i+ws[i].length) = blank := by
  rw [encoded_split ws i hi]
  have hh := WordSegments.get f r
    (encoded (ws.take i) ++ ws[i].map bitSymbol ++ ([blank]++encoded (ws.drop (i+1))))
    ((encoded (ws.take i)).length+ws[i].length) (by simp)
  simpa [cursor,Nat.cast_add,add_assoc,List.getElem_append] using hh

def placement : Fin (2+11) ≃ Fin 13 where
  toFun := ![12,8,0,1,2,3,4,5,6,7,9,10,11]
  invFun := ![2,3,4,5,6,7,8,9,1,10,11,12,0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def readProgram : Program 13 10 0 := Placement.placed BinaryOffsetStreamRead.program placement
def program : Program 15 243 0 := TranslationPreparedFamily.program (s := 1) readProgram

def frame (ws : List (List Bool)) (f : ℤ → Fin 4) (r : ℤ) (i : ℕ) : Tapes 1 0 :=
  one (putWord f r (encoded ws)) (cursor ws r i)

def state (ws : List (List Bool)) (Q B : ℕ) (source dest control : ℤ → Fin 4)
    (p q r : ℤ) (bs qs : List Bool) (payload : ℕ → ℕ → List (Fin 4)) (i : ℕ) : Tapes 13 0 :=
  TranslationPreparedFamily.state (offset ws) Q B ws.length source dest p q bs qs (old ws)
    (frame ws control r) payload i

private theorem reader (source dest control : ℤ → Fin 4) (p q r : ℤ)
    (bs qs old xs : List Bool) (hend : control (r+xs.length) = blank) :
    HoareTime readProgram
      (fun v => v = (TranslationExecutionReuse.bank source dest p q bs qs old).append
        (one (putWord control r (xs.map bitSymbol)) r))
      (fun v => v = (TranslationExecutionReuse.bank source dest p q bs qs xs).append
        (one (putWord control r (xs.map bitSymbol)) (r+xs.length+1)))
      (2*old.length+2*xs.length+11) := by
  have ha : Placement.active placement ((TranslationExecutionReuse.bank source dest p q bs qs old).append
      (one (putWord control r (xs.map bitSymbol)) r)) =
      Copy.tapes (putWord control r (xs.map bitSymbol)) (binary old) r 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hh := Placement.hoare_at (BinaryOffsetStreamRead.reads control r old xs hend) placement _ ha
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem read_hoare (ws : List (List Bool)) (Q B : ℕ) (source dest control : ℤ → Fin 4)
    (p q r : ℤ) (bs qs : List Bool) (payload : ℕ → ℕ → List (Fin 4))
    (i : ℕ) (hi : i < ws.length) :
    HoareTime readProgram
      (fun v => v = state ws Q B source dest control p q r bs qs payload i)
      (fun v => v = TranslationPreparedFamily.prepared (offset ws) Q B ws.length source dest p q bs qs
        (old ws) (frame ws control r) payload i)
      (2*(old ws i).length+2*ws[i].length+11) := by
  have hh := reader
    (putWord source p (TranslationStream.fibers Q ws.length payload).flatten)
    (putWord dest q (TranslationPreparedFamily.outputPrefix (offset ws) Q i payload))
    (putWord control r (encoded ws)) (p+((i*(Q*B) : ℕ) : ℤ))
    (q+((i*(Q*B) : ℕ) : ℤ)) (cursor ws r i) bs qs (old ws i) ws[i]
    (stream_delimiter ws control r i hi)
  rw [stream_word ws control r i hi] at hh
  simpa only [state,TranslationPreparedFamily.state,TranslationPreparedFamily.prepared,frame,
    cursor_succ ws r i hi,old_succ ws i hi] using hh

private theorem canonical_length (xs : List Bool) (hx : GrowingCounterData.Canonical xs)
    (Q : ℕ) (hv : Counter.value xs ≤ Q) : xs.length ≤ Q+1 := by
  have hw := GrowingCounterData.canonical_width xs hx
  have hl := Nat.log2_le_self (Counter.value xs)
  omega

theorem old_length (ws : List (List Bool)) (Q i : ℕ) (hi : i ≤ ws.length)
    (hc : ∀ xs ∈ ws, GrowingCounterData.Canonical xs) (hv : ∀ xs ∈ ws, Counter.value xs ≤ Q) :
    (old ws i).length ≤ Q+1 := by
  cases i with
  | zero => simp [old]
  | succ i =>
    have hi' : i < ws.length := by omega
    rw [old_succ ws i hi']
    exact canonical_length _ (hc _ (List.getElem_mem hi')) Q (hv _ (List.getElem_mem hi'))

/-- Actual fixed-state execution for every offset in the physical stream.
The full control tape is preserved. Its head consumes every delimiter; all
translation scratch is reset and the final offset remains explicitly present.
No synthesized offset or payload-permutation callback occurs in the contract. -/
theorem runs (ws : List (List Bool)) (Q B : ℕ) (hQ : 0 < Q) (hB : 0 < B)
    (source dest control : ℤ → Fin 4) (p q r : ℤ) (bs qs ns : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (hn : Counter.value ns = ws.length)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns)
    (hc : ∀ xs ∈ ws, GrowingCounterData.Canonical xs) (hv : ∀ xs ∈ ws, Counter.value xs ≤ Q)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B) :
    HoareTime program
      (fun v => v = CountedLoopReuse.bank (state ws Q B source dest control p q r bs qs payload 0)
        empty (binary ns) 1 1)
      (fun v => v = CountedLoopReuse.bank (state ws Q B source dest control p q r bs qs payload ws.length)
        empty (binary ns) 1 1)
      (481*(ws.length*(Q*B))+23) := by
  let cost := fun i => 2*(old ws i).length+2*(ws[i]?.getD []).length+11
  have hcost (i : ℕ) (hi : i < ws.length) : cost i ≤ 4*Q+15 := by
    have ho := old_length ws Q i hi.le hc hv
    have hw := canonical_length ws[i] (hc _ (List.getElem_mem hi)) Q (hv _ (List.getElem_mem hi))
    simp only [cost,List.getElem?_eq_getElem hi,Option.getD_some]
    omega
  have hh := TranslationPreparedFamily.family_hoare_linear readProgram (offset ws) hQ
    (by intro i hi; simpa [offset,List.getElem?_eq_getElem hi] using hv _ (List.getElem_mem hi)) hB
    source dest p q bs qs ns (old ws) (frame ws control r) hb hq hn
    (by intro i hi; rfl) cb cq cn
    (by intro i hi; rw [old_succ ws i hi]; exact hc _ (List.getElem_mem hi)) payload hwidth cost
    (by intro i hi; simpa only [cost,state,List.getElem?_eq_getElem hi,Option.getD_some] using
          read_hoare ws Q B source dest control p q r bs qs payload i hi)
  have hs := TranslationPreparedFamily.preparation_sum_bound ws.length (4*Q+15) cost hcost
  rw [TranslationStream.source_length Q B ws.length payload hwidth] at hh
  unfold program state
  apply hh.consequence (fun _ h => h) (fun _ h => h)
  have hQB : Q ≤ Q*B := Nat.le_mul_of_pos_right _ hB
  have hpos : 1 ≤ Q*B := Nat.mul_pos hQ hB
  have hm := Nat.mul_le_mul_left ws.length (show 4*Q+15 ≤ 19*(Q*B) by omega)
  nlinarith

end IntegerMultBounds.Machine.StreamedFiberTranslation
