module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackUpdateEntry

/-! Emit an elimination row into the output stack in row-major order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T Q A : ℕ} {P U : Type}

/-- Emit the suffix first, so prepending each block leaves the list in its original order. -/
def emitBlocks {ι : Type} (emit : ι → Pr P T Q A U) : List ι → Pr P T Q A U
  | [] => .act .done
  | i :: is => .seq (emitBlocks emit is) (emit i)

theorem emitBlocks_exec {ι : Type} (body : P → Pr P T Q A U) (dst : Fin T)
    (emit : ι → Pr P T Q A U) (word : ι → List (Fin (A+4))) (cost : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (step : ∀ i (u : HS T Q A U) (suffix : List (Fin (A+4))), ∃ z n, z.user = u.user ∧ n ≤ cost ∧
      Exec body (emit i) (mk u {S with R := Function.update S.R dst suffix}) n
        (mk z {S with R := Function.update S.R dst (word i ++ suffix)})) (is : List ι) :
    ∃ z n, z.user = v.user ∧ n ≤ is.length*cost+1 ∧ Exec body (emitBlocks emit is) (mk v S) n
      (mk z {S with R := Function.update S.R dst (is.flatMap word ++ S.R dst)}) := by
  induction is with
  | nil =>
    exact ⟨v,1,rfl,by simp,by simpa [emitBlocks] using Exec.act (body := body) .done (mk v S)⟩
  | cons i is ih =>
    obtain ⟨u,l,hu,hl,tail⟩ := ih
    obtain ⟨z,n,hz,hn,head⟩ := step i u _
    refine ⟨z,l+n,hz.trans hu,?_,?_⟩
    · simp only [List.length_cons,Nat.succ_mul]; omega
    · simpa [emitBlocks,List.append_assoc] using Exec.seq tail head

def updateRow {d : ℕ} (row pivot : Fin d) (r : Fin 17 ↪ Fin T) : Pr P T Q A U :=
  emitBlocks (fun j => updateEntry j row pivot r) (List.ofFn (id : Fin d → Fin d))

def entryTime (d H : ℕ) := 16*(d*d*H)+48*H*H+208*H+140

theorem matrixOffset_le {d : ℕ} (H : ℕ) (i j : Fin d) :
    (i.val*d+j.val)*H ≤ d*d*H := by
  apply Nat.mul_le_mul_right
  have h := Nat.mul_le_mul_right d (show i.val+1 ≤ d from i.isLt)
  rw [Nat.succ_mul] at h
  omega

theorem updateRow_exec {M d : ℕ} [NeZero M] (body : P → Pr P T Q A U) (r : Fin 17 ↪ Fin T)
    (m : Matrix (Fin d) (Fin d) (ZMod M)) (row pivot : Fin d) (c : ZMod M) (H : ℕ)
    (hm : M < 2^H) (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (matrix : S.R (r 15) = matrixWords A H m ++ tail) (modulus : S.R (r 2) = binSyms H M)
    (coeff : S.R (r 0) = binSyms H c.val) (free : ∀ i : Fin 17, 0 < i → i ≠ 2 → i < 15 → S.R (r i) = []) :
    let words := List.ofFn fun j => binSyms (A := A) H (m row j-c*m pivot j).val
    ∃ z n, z.user = v.user ∧ n ≤ d*entryTime d H+1 ∧ Exec body (updateRow row pivot r) (mk v S) n
      (mk z {S with R := Function.update S.R (r 16) (words.flatten ++ S.R (r 16))}) := by
  let word := fun j => binSyms (A := A) H (m row j-c*m pivot j).val
  suffices step : ∀ j (u : HS T Q A U) (suffix : List (Fin (A+4))), ∃ z n,
      z.user = u.user ∧ n ≤ entryTime d H ∧
      Exec body (updateEntry j row pivot r) (mk u {S with R := Function.update S.R (r 16) suffix}) n
        (mk z {S with R := Function.update S.R (r 16) (word j ++ suffix)}) by
    simpa [updateRow,word,List.flatMap_def,List.map_ofFn] using
      emitBlocks_exec body (r 16) (fun j => updateEntry j row pivot r) word (entryTime d H) v S step (List.ofFn (id : Fin d → Fin d))
  intro j u suffix
  let D : Stacks T A := {S with R := Function.update S.R (r 16) suffix}
  have keep (i : Fin 17) (h : i ≠ 16) : D.R (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne h) _ _
  obtain ⟨z,n,hz,hn,run⟩ := updateEntry_exec body r m j row pivot c H hm u D tail
    ((keep 15 (by decide)).trans matrix) ((keep 2 (by decide)).trans modulus) ((keep 0 (by decide)).trans coeff)
    (fun i lo h hi => (keep i (by omega)).trans (free i lo h hi))
  refine ⟨z,n,hz,?_,by simpa [D,word,Function.update_idem] using run⟩
  dsimp [entryTime]
  have := matrixOffset_le H pivot j
  have := matrixOffset_le H row j
  omega

/-- Gather selected fixed-width entries into one contiguous word stream. -/
def gatherMatrix {d n : ℕ} (row col : Fin n → Fin d) (r : Fin 7 ↪ Fin T) : Pr P T Q A U :=
  emitBlocks (fun j : Fin n => readMatrixWord ((row j).val*d+(col j).val) r) (List.ofFn (id : Fin n → Fin n))

theorem gatherMatrix_exec {M d n : ℕ} [NeZero M] (body : P → Pr P T Q A U) (r : Fin 7 ↪ Fin T)
    (m : Matrix (Fin d) (Fin d) (ZMod M)) (row col : Fin n → Fin d) (H : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (matrix : S.R (r 2) = matrixWords A H m ++ tail) (width : (S.R (r 1)).length = H)
    (free : ∀ i : Fin 7, i = 0 ∨ 4 ≤ i → S.R (r i) = []) :
    let words := List.ofFn fun j => binSyms (A := A) H (m (row j) (col j)).val
    ∃ z t, z.user = v.user ∧ t ≤ n*(8*(d*d*H)+14*H+22)+1 ∧ Exec body (gatherMatrix row col r) (mk v S) t
      (mk z {S with R := Function.update S.R (r 3) (words.flatten ++ S.R (r 3))}) := by
  let word := fun j => binSyms (A := A) H (m (row j) (col j)).val
  let emit := fun j : Fin n => readMatrixWord (P := P) (Q := Q) (A := A) (U := U) ((row j).val*d+(col j).val) r
  have step (j : Fin n) (u : HS T Q A U) (suffix : List (Fin (A+4))) : ∃ z n,
      z.user = u.user ∧ n ≤ 8*(d*d*H)+14*H+22 ∧ Exec body (emit j)
        (mk u {S with R := Function.update S.R (r 3) suffix}) n
        (mk z {S with R := Function.update S.R (r 3) (word j ++ suffix)}) := by
    let D : Stacks T A := {S with R := Function.update S.R (r 3) suffix}
    have keep (i : Fin 7) (h : i ≠ 3) : D.R (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne h) _ _
    obtain ⟨z,hz,run⟩ := readMatrixWord_exec body r m (row j) (col j) H u D tail
      ((keep 2 (by decide)).trans matrix) (by rw [keep 1 (by decide),width])
      (fun i h => (keep i (by omega)).trans (free i h))
    exact ⟨z,8*(((row j).val*d+(col j).val)*H)+14*H+22,hz,by have := matrixOffset_le H (row j) (col j); omega,by simpa [D,emit,word,Function.update_idem] using run⟩
  simpa [gatherMatrix,emit,word,List.flatMap_def,List.map_ofFn] using
    emitBlocks_exec body (r 3) emit word _ v S step (List.ofFn (id : Fin n → Fin n))

/-- The pivot row is copied unchanged from its original position. -/
def copyMatrixRow {d : ℕ} (row : Fin d) (r : Fin 7 ↪ Fin T) : Pr P T Q A U :=
  gatherMatrix (fun _ : Fin d => row) id r

theorem copyMatrixRow_exec {M d : ℕ} [NeZero M] (body : P → Pr P T Q A U) (r : Fin 7 ↪ Fin T)
    (m : Matrix (Fin d) (Fin d) (ZMod M)) (row : Fin d) (H : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (matrix : S.R (r 2) = matrixWords A H m ++ tail) (width : (S.R (r 1)).length = H)
    (free : ∀ i : Fin 7, i = 0 ∨ 4 ≤ i → S.R (r i) = []) :
    let words := List.ofFn fun j => binSyms (A := A) H (m row j).val
    ∃ z n, z.user = v.user ∧ n ≤ d*(8*(d*d*H)+14*H+22)+1 ∧ Exec body (copyMatrixRow row r) (mk v S) n
      (mk z {S with R := Function.update S.R (r 3) (words.flatten ++ S.R (r 3))}) := by
  exact gatherMatrix_exec body r m (fun _ : Fin d => row) id H v S tail matrix width free

end IntegerMultBounds.MathlibTM2.Cover.Fallback
