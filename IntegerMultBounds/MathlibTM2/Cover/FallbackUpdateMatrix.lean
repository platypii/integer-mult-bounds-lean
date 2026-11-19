module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackEliminateRow
public import IntegerMultBounds.MathlibTM2.Cover.FallbackItineraryEntries

/-! One complete elimination column on a packed matrix, using a shared pivot reciprocal. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T Q A d : ℕ} {P U : Type}

def pivotCopyPorts : Fin 7 ↪ Fin 19 := ⟨![3,2,15,16,4,5,6],by decide⟩

def updateMatrix (k pivot : Fin d) (r : Fin 19 ↪ Fin T) : Pr P T Q A U :=
  emitBlocks (fun i => if i = k then copyMatrixRow pivot (pivotCopyPorts.trans r)
    else eliminateRow k (Equiv.swap k pivot i) pivot r) (List.ofFn (id : Fin d → Fin d))

theorem updateMatrix_exec (body : P → Pr P T Q A U) (r : Fin 19 ↪ Fin T) (p w : ℕ)
    [NeZero (p^(w+1))] (m : Matrix (Fin d) (Fin d) (ZMod (p^(w+1)))) (k pivot : Fin d) (H : ℕ)
    (hm : p^(w+1) < 2^H) (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (matrix : S.R (r 15) = matrixWords A H m ++ tail) (modulus : S.R (r 2) = binSyms H (p^(w+1)))
    (inverse : S.R (r 17) = binSyms H (pivotReciprocal p (m pivot k) w).val)
    (free : ∀ i : Fin 19, (i < 15 ∧ i ≠ 2) ∨ i = 18 → S.R (r i) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ d*((d+1)*entryTime d H)+1 ∧ Exec body (updateMatrix k pivot r) (mk v S) n
      (mk z {S with R := Function.update S.R (r 16) (matrixWords A H (clearColumn p w k pivot m) ++ S.R (r 16))}) := by
  let emit := fun i : Fin d => if i = k then copyMatrixRow (P := P) (Q := Q) (A := A) (U := U) pivot (pivotCopyPorts.trans r)
    else eliminateRow k (Equiv.swap k pivot i) pivot r
  let words := fun i => (List.ofFn fun j => binSyms (A := A) H (clearColumn p w k pivot m i j).val).flatten
  have step (i : Fin d) (u : HS T Q A U) (suffix : List (Fin (A+4))) : ∃ z n, z.user = u.user ∧
      n ≤ (d+1)*entryTime d H ∧ Exec body (emit i) (mk u {S with R := Function.update S.R (r 16) suffix}) n
        (mk z {S with R := Function.update S.R (r 16) (words i ++ suffix)}) := by
    let D : Stacks T A := {S with R := Function.update S.R (r 16) suffix}
    have keep (i : Fin 19) (h : i ≠ 16) : D.R (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne h) _ _
    have fresh (j : Fin 19) (h : (j < 15 ∧ j ≠ 2) ∨ j = 18) := (keep j (by omega)).trans (free j h)
    by_cases hi : i = k
    · subst i
      have ports : ∀ j : Fin 7, j = 0 ∨ 4 ≤ j → pivotCopyPorts j < 15 ∧ pivotCopyPorts j ≠ 2 := by decide
      obtain ⟨z,n,hz,hn,run⟩ := copyMatrixRow_exec body (pivotCopyPorts.trans r) m pivot H u D tail
        ((keep 15 (by decide)).trans matrix) (by change (D.R (r 2)).length = H; simp [keep 2 (by decide),modulus,length_binSyms])
        (fun j h => fresh _ (Or.inl (ports j h)))
      have le : 8*(d*d*H)+14*H+22 ≤ entryTime d H := by unfold entryTime; omega
      refine ⟨z,n,hz,?_,?_⟩
      · have := Nat.mul_le_mul_left d le
        rw [Nat.succ_mul]; unfold entryTime at *; omega
      · change Exec _ _ _ _ (mk z {D with R := Function.update D.R (r 16) (_ ++ D.R (r 16))}) at run
        simpa [emit,words,clearColumn,D,Function.update_idem] using run
    · let row := Equiv.swap k pivot i
      obtain ⟨z,n,hz,hn,run⟩ := eliminateRow_exec body r m k row pivot _ H hm u D tail
        ((keep 15 (by decide)).trans matrix) ((keep 2 (by decide)).trans modulus) ((keep 17 (by decide)).trans inverse) fresh
      refine ⟨z,n,hz,?_,?_⟩
      · have hb := matrixOffset_le H row k
        rw [Nat.succ_mul]
        unfold entryTime at *
        omega
      · simpa [emit,hi,words,clearColumn,row,D,Function.update_idem] using run
  simpa [updateMatrix,emit,words,matrixWords,List.flatMap_def,List.map_ofFn] using
    emitBlocks_exec body (r 16) emit words _ v S step (List.ofFn (id : Fin d → Fin d))

/-- The pivot row reads a constant one instead of the scratch multiplier. -/
def goodPivotPorts : Fin 17 ↪ Fin 20 :=
  ⟨![19,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16], by decide⟩

def goodMatrix (k : Fin d) (r : Fin 20 ↪ Fin T) : Pr P T Q A U :=
  emitBlocks (fun i => if i = k then goodPivotRow k (goodPivotPorts.trans r)
    else eliminateRow k i k ((Fin.castLEEmb (by decide)).trans r)) (List.ofFn (id : Fin d → Fin d))

theorem goodMatrix_exec {M : ℕ} [NeZero M] (body : P → Pr P T Q A U) (r : Fin 20 ↪ Fin T)
    (m : Matrix (Fin d) (Fin d) (ZMod M)) (k : Fin d) (unit : IsUnit (m k k)) (H : ℕ)
    (hm : M < 2^H) (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (matrix : S.R (r 15) = matrixWords A H m ++ tail) (modulus : S.R (r 2) = binSyms H M)
    (inverse : S.R (r 17) = binSyms H (Ring.inverse (m k k)).val)
    (one : S.R (r 19) = binSyms H (1 : ZMod M).val)
    (free : ∀ i : Fin 20, (i < 15 ∧ i ≠ 2) ∨ i = 18 → S.R (r i) = []) :
    let next := GoodForm.elimM k m (Ring.inverse (m k k))
    ∃ z n, z.user = v.user ∧ n ≤ d*((d+1)*entryTime d H)+1 ∧ Exec body (goodMatrix k r) (mk v S) n
      (mk z {S with R := Function.update S.R (r 16) (matrixWords A H next ++ S.R (r 16))}) := by
  intro next
  have fits : 19 ≤ 20 := by decide
  let emit := fun i : Fin d => if i = k then goodPivotRow (P := P) (Q := Q) (A := A) (U := U) k (goodPivotPorts.trans r)
    else eliminateRow k i k ((Fin.castLEEmb (by decide)).trans r)
  let words := fun i => (List.ofFn fun j => binSyms (A := A) H (next i j).val).flatten
  have step (i : Fin d) (u : HS T Q A U) (suffix : List (Fin (A+4))) : ∃ z n, z.user = u.user ∧
      n ≤ (d+1)*entryTime d H ∧ Exec body (emit i) (mk u {S with R := Function.update S.R (r 16) suffix}) n
        (mk z {S with R := Function.update S.R (r 16) (words i ++ suffix)}) := by
    let D : Stacks T A := {S with R := Function.update S.R (r 16) suffix}
    have keep (j : Fin 20) (h : j ≠ 16) : D.R (r j) = S.R (r j) := Function.update_of_ne (r.injective.ne h) _ _
    have fresh (j : Fin 20) (h : (j < 15 ∧ j ≠ 2) ∨ j = 18) := (keep j (by omega)).trans (free j h)
    by_cases hi : i = k
    · subst i
      have ports : ∀ i : Fin 17, 0 < i → i ≠ 2 → i < 15 → goodPivotPorts i < 15 ∧ goodPivotPorts i ≠ 2 := by decide
      obtain ⟨z,n,hz,hn,run⟩ := goodPivotRow_exec body (goodPivotPorts.trans r) m k H hm u D tail
        ((keep 15 (by decide)).trans matrix) ((keep 2 (by decide)).trans modulus) ((keep 19 (by decide)).trans one)
        (fun i h h' hi => fresh _ (.inl (ports i h h' hi)))
      exact ⟨z,n,hz,by rw [Nat.succ_mul]; unfold entryTime at *; omega,
        by simpa [emit,words,next,goodPivotPorts,D,Function.update_idem] using run⟩
    · obtain ⟨z,n,hz,hn,run⟩ := eliminateRow_exec body ((Fin.castLEEmb (by decide : 19 ≤ 20)).trans r)
        m k i k _ H hm u D tail ((keep 15 (by decide)).trans matrix) ((keep 2 (by decide)).trans modulus)
        ((keep 17 (by decide)).trans inverse) (fun j hj => fresh _ ((by decide +revert : ∀ i : Fin 19, (i < 15 ∧ i ≠ 2) ∨ i = 18 →
          (i.castLE fits < 15 ∧ i.castLE fits ≠ 2) ∨ i.castLE fits = (18 : Fin 20)) j hj))
      have entry (j : Fin d) : next i j = m i j - m i k * Ring.inverse (m k k) * m k j := by
        by_cases hj : j = k
        · subst j; simp [next,GoodForm.elimM,hi,mul_assoc,Ring.inverse_mul_cancel _ unit]
        · simp [next,GoodForm.elimM,hi,hj]
      exact ⟨z,n,hz,by have := matrixOffset_le H i k; rw [Nat.succ_mul]; unfold entryTime at *; omega,
        by simpa [emit,hi,words,entry,D,Function.update_idem] using run⟩
  simpa [goodMatrix,emit,words,matrixWords,List.flatMap_def,List.map_ofFn] using
    emitBlocks_exec body (r 16) emit words _ v S step (List.ofFn (id : Fin d → Fin d))

end IntegerMultBounds.MathlibTM2.Cover.Fallback
