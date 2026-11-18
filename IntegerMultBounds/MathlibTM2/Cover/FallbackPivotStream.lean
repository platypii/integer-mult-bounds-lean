module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackClassMachine

/-! Stream pivot choices in physical label order and dispatch each column from the tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q A d m : ℕ} {P U : Type}

def pivotCode (i : ℕ) : List (Fin (A+4)) :=
  List.replicate i (bitSymbol true) ++ [bitSymbol false]

def orderedScheduleCode (order : List (Fin d)) (rows : Fin d → Fin d) : List (Fin (A+4)) :=
  order.flatMap fun k => pivotCode (rows k).val

def scheduleCode (rows : Fin d → Fin d) : List (Fin (A+4)) :=
  orderedScheduleCode (List.finRange d) rows

/-- Compile the residue table once; the generated program writes one entire schedule per label. -/
theorem orderedPivotStream_writes (order : List (Fin d)) (body : P → Pr P T Q A U)
    (table : Matrix (Fin m) (Fin m) (ZMod prime) → Matrix (Fin d) (Fin d) (ZMod prime))
    (rs : List (Pair T)) (hk : rs.length = m*m) (out count saved : Fin T)
    (hr : (count :: saved :: (slots rs ++ [out])).Nodup) :
    ∃ p : Pr P T Q A U, ∀ (v : RecursiveInterchangeLayout.Descriptor) (w B : ℕ),
      0 < w → v.beforeH = B*prime^(m*(w*m)) →
      Writes body (fun R => ready (prime^(w-1)) R rs ∧ R saved = [] ∧
        (R count).length = v.beforeRows*v.rows*B) out p
        ((List.range (LabelMask.records v)).flatMap fun j =>
          orderedScheduleCode order (classPivots (table (LabelStock.residue m w 1 j))))
        ((v.beforeRows*v.rows*B)*(time (prime^(w-1)) (m*m) 1+5)+4) := by
  simpa only [LabelSelectors.recordMap,LabelSelectors.residue_eq,List.flatMap_def] using
    recordWords_writes (body := body) m (fun a => orderedScheduleCode order (classPivots (table (LabelSelectors.matrix m a))))
      rs hk out count saved hr

theorem pivotStream_writes (body : P → Pr P T Q A U)
    (table : Matrix (Fin m) (Fin m) (ZMod prime) → Matrix (Fin d) (Fin d) (ZMod prime))
    (rs : List (Pair T)) (hk : rs.length = m*m) (out count saved : Fin T)
    (hr : (count :: saved :: (slots rs ++ [out])).Nodup) :
    ∃ p : Pr P T Q A U, ∀ (v : RecursiveInterchangeLayout.Descriptor) (w B : ℕ),
      0 < w → v.beforeH = B*prime^(m*(w*m)) →
      Writes body (fun R => ready (prime^(w-1)) R rs ∧ R saved = [] ∧
        (R count).length = v.beforeRows*v.rows*B) out p
        ((List.range (LabelMask.records v)).flatMap fun j =>
          scheduleCode (classPivots (table (LabelStock.residue m w 1 j))))
        ((v.beforeRows*v.rows*B)*(time (prime^(w-1)) (m*m) 1+5)+4) :=
  orderedPivotStream_writes (List.finRange d) body table rs hk out count saved hr

/-- Place the return pivots immediately after the forward record, in rewind order. -/
theorem pivotRoundTrip_writes (body : P → Pr P T Q A U)
    (table : Matrix (Fin m) (Fin m) (ZMod prime) → Matrix (Fin d) (Fin d) (ZMod prime))
    (rs : List (Pair T)) (hk : rs.length = m*m) (out count saved : Fin T)
    (hr : (count :: saved :: (slots rs ++ [out])).Nodup) :
    ∃ p : Pr P T Q A U, ∀ (v : RecursiveInterchangeLayout.Descriptor) (w B : ℕ),
      0 < w → v.beforeH = B*prime^(m*(w*m)) →
      Writes body (fun R => ready (prime^(w-1)) R rs ∧ R saved = [] ∧
        (R count).length = v.beforeRows*v.rows*B) out p
        ((List.range (LabelMask.records v)).flatMap fun j =>
          let rows := classPivots (table (LabelStock.residue m w 1 j))
          scheduleCode rows ++ orderedScheduleCode (List.finRange d).reverse rows)
        ((v.beforeRows*v.rows*B)*(time (prime^(w-1)) (m*m) 1+5)+4) := by
  simpa only [scheduleCode, orderedScheduleCode, List.flatMap_append] using
    orderedPivotStream_writes (List.finRange d ++ (List.finRange d).reverse) body table rs hk out count saved hr

def nextPivotBit (src : Fin T) : Act T Q A U :=
  .pop (.rt src) (fun v o => {v with flag := symBit (o.getD blank)}) .done

def selectPivot {ι : Type} (src : Fin T) (f : ι → Pr P T Q A U) : List ι → Pr P T Q A U
  | [] => .act .done
  | i :: is => .seq (.act (nextPivotBit src)) (.cond (·.flag) (selectPivot src f is) (f i))

theorem selectPivot_exec {ι : Type} (body : P → Pr P T Q A U) (src : Fin T)
    (f : ι → Pr P T Q A U) (pre : List ι) (i : ι) (post : List ι)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (word : S.R src = pivotCode pre.length ++ tail) {z l}
    (branch : Exec body (f i) (mk {v with flag := false} {S with R := Function.update S.R src tail}) l z) :
    Exec body (selectPivot src f (pre ++ i :: post)) (mk v S) (2*(pre.length+1)+l) z := by
  induction pre generalizing v S with
  | nil =>
    have rd := Exec.act (body := body) (nextPivotBit src) (mk v S)
    simp [nextPivotBit,Action.run,word,pivotCode,update_rt] at rd
    exact (Exec.seq rd (Exec.cond_false (by rfl) branch)).cast (by simp; omega) rfl
  | cons j pre ih =>
    let rest := pivotCode (A := A) pre.length ++ tail
    let D : Stacks T A := {S with R := Function.update S.R src rest}
    have head : S.R src = bitSymbol true :: rest := by simpa [rest,pivotCode,List.replicate_succ] using word
    have rd := Exec.act (body := body) (nextPivotBit src) (mk v S)
    simp [nextPivotBit,Action.run,head,update_rt] at rd
    have run := ih {v with flag := true} D (by simp [D,rest]) (by simpa [D,Function.update_idem] using branch)
    exact (Exec.seq rd (Exec.cond_true (by rfl) run)).cast (by simp; omega) rfl

theorem selectPivot_fin_exec (body : P → Pr P T Q A U) (src : Fin T)
    (f : Fin d → Pr P T Q A U) (pivot : Fin d)
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4)))
    (code : S.R src = pivotCode pivot.val ++ rest) {z l}
    (branch : Exec body (f pivot) (mk {v with flag := false} {S with R := Function.update S.R src rest}) l z) :
    Exec body (selectPivot src f (List.finRange d)) (mk v S) (2*(pivot.val+1)+l) z := by
  let xs := List.finRange d
  have lt : pivot.val < xs.length := by simp [xs]
  have len : (xs.take pivot.val).length = pivot.val := by simp [List.length_take,Nat.min_eq_left lt.le]
  have split : xs.take pivot.val ++ pivot :: xs.drop (pivot.val+1) = xs := by
    have h := List.getElem_cons_drop lt
    rw [show pivot :: xs.drop (pivot.val+1) = xs.drop pivot.val by simpa [xs] using h]
    exact List.take_append_drop ..
  obtain select := selectPivot_exec body src f (xs.take pivot.val)
    pivot (xs.drop (pivot.val+1)) v S rest (by rw [len]; exact code) branch
  rw [split,len] at select
  exact select

/-- Dispatch a rewind callback from the unconsumed reverse prefix of the record. -/
theorem reversePivot_exec (body : P → Pr P T Q A U) (src : Fin T)
    (f : Fin d → Pr P T Q A U) (rows : Fin d → Fin d) (k : Fin d)
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4)))
    (code : S.R src = orderedScheduleCode (((List.finRange d).take (k.val+1)).reverse) rows ++ rest)
    {z l} (branch : Exec body (f (rows k)) (mk {v with flag := false} {S with R := Function.update S.R src (orderedScheduleCode (((List.finRange d).take k.val).reverse) rows ++ rest)}) l z) :
    Exec body (selectPivot src f (List.finRange d)) (mk v S) (2*((rows k).val+1)+l) z := by
  apply selectPivot_fin_exec body src f (rows k) v S _ _ branch
  have lt : k.val < (List.finRange d).length := by simp
  simpa [List.take_succ_eq_append_getElem lt, orderedScheduleCode, List.append_assoc] using code

/-- The column number is fixed by the loop; its pivot row comes from the record. -/
def liveColumn (p : ℕ) (k : Fin d) (r : Fin 23 ↪ Fin T) (src : Fin T) : Pr P T Q A U :=
  selectPivot src (fun i => itineraryColumn p k i r) (List.finRange d)

theorem liveColumn_exec (body : P → Pr P T Q A U) (r : Fin 23 ↪ Fin T) (src : Fin T)
    (apart : ∀ i, r i ≠ src) (p w H : ℕ) (hp : p.Prime) [NeZero (p^(w+1))]
    (m : Matrix (Fin d) (Fin d) (ZMod (p^(w+1)))) (k pivot : Fin d) (unit : IsUnit (m pivot k))
    (hm : p^(w+1) < 2^H) (v : HS T Q A U) (S : Stacks T A) (tail rest : List (Fin (A+4)))
    (code : S.R src = pivotCode pivot.val ++ rest) (matrix : S.R (r 15) = matrixWords A H m ++ tail)
    (modulus : S.R (r 2) = binSyms H (p^(w+1))) (one : S.R (r 20) = binSyms H (1 : ZMod (p^(w+1))).val)
    (ticks : (S.R (r 22)).length = w)
    (free : ∀ i : Fin 23, (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) ∨ i = 21 → S.R (r i) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ 2*d+(4*w+4+columnTime d p w H) ∧ Exec body (liveColumn p k r src) (mk v S) n
      (mk z {S with R := Function.update (Function.update S.R src rest) (r 16) (matrixWords A H (clearColumn p w k pivot m) ++ S.R (r 16))}) := by
  let D : Stacks T A := {S with R := Function.update S.R src rest}
  have keep (i) : D.R (r i) = S.R (r i) := Function.update_of_ne (apart i) _ _
  obtain ⟨z,n,hz,hn,run⟩ := itineraryColumn_exec body r p w H hp m k pivot unit hm {v with flag := false} D tail
    ((keep 15).trans matrix) ((keep 2).trans modulus) ((keep 20).trans one)
    (by rw [keep,ticks]) (fun i h => (keep i).trans (free i h))
  rw [keep 16] at run
  have select := selectPivot_fin_exec body src (fun i => itineraryColumn p k i r) pivot v S rest code run
  exact ⟨z,_,hz,by have := pivot.isLt; omega,select⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
