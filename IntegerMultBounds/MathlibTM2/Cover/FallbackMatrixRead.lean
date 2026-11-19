module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyAfterPrefix
public import IntegerMultBounds.MathlibTM2.Host.Index

/-! Restoring access to a row-major matrix of fixed-width binary residues. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open Mult.PhaseCellToeplitz

private theorem splitBlocks {α : Type} {d H : ℕ} (f : Fin d → List α)
    (width : ∀ i, (f i).length = H) (i : Fin d) :
    ∃ pre post, (List.ofFn f).flatten = pre ++ f i ++ post ∧ pre.length = i.val*H := by
  induction d with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    cases i using Fin.cases with
    | zero => exact ⟨[],_,rfl,by simp⟩
    | succ j =>
      obtain ⟨pre,post,h,len⟩ := ih (fun k => f k.succ) (fun k => width k.succ) j
      exact ⟨f 0 ++ pre,post,by simp [h,List.append_assoc],
        by simp [width,len,Nat.succ_mul,Nat.add_comm]⟩

def matrixWords {d e M : ℕ} [NeZero M] (A H : ℕ) (m : Matrix (Fin d) (Fin e) (ZMod M)) :=
  (List.ofFn fun i => (List.ofFn fun j => binSyms (A := A) H (m i j).val).flatten).flatten

theorem matrixRead_exec {T Q A d e M : ℕ} [NeZero M] {P U : Type} (body : P → Pr P T Q A U)
    {skip width src dst savedPrefix savedWord tmp : Fin T}
    (regs : [skip,width,src,dst,savedPrefix,savedWord,tmp].Nodup)
    (m : Matrix (Fin d) (Fin e) (ZMod M)) (i : Fin d) (j : Fin e) (H : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (matrix : S.R src = matrixWords A H m ++ tail)
    (offset : (S.R skip).length = (i.val*e+j.val)*H) (hw : (S.R width).length = H)
    (hp : S.R savedPrefix = []) (hs : S.R savedWord = []) (ht : S.R tmp = []) :
    ∃ z, z.user = v.user ∧
      Exec body (copyAfterPrefix skip width src dst savedPrefix savedWord tmp) (mk v S)
        (6*((i.val*e+j.val)*H)+10*H+16)
        (mk z {S with R := Function.update S.R dst (binSyms H (m i j).val ++ S.R dst)}) := by
  let word := fun a b => binSyms (A := A) H (m a b).val
  let row := fun a => (List.ofFn (word a)).flatten
  have rowLen (a) : (row a).length = e*H := by simp [row,word,List.length_flatten,List.map_ofFn,Function.comp_def,length_binSyms,List.ofFn_const]
  obtain ⟨rows,rest,hr,lr⟩ := splitBlocks row rowLen i
  obtain ⟨cols,last,hc,lc⟩ := splitBlocks (word i) (fun _ => length_binSyms ..) j
  have len : (rows ++ cols).length = (i.val*e+j.val)*H := by
    simp [lr,lc,Nat.add_mul,Nat.mul_assoc]
  change S.R src = (List.ofFn row).flatten ++ tail at matrix
  change row i = _ at hc
  obtain ⟨z,hz,run⟩ := copyAfterPrefix_exec (body := body) regs v S (rows ++ cols) (word i j)
    (last ++ rest ++ tail) (by simp [matrix,hr,hc,List.append_assoc]) (offset.trans len.symm)
    (by simpa [word,length_binSyms] using hw) hp hs ht
  exact ⟨z,hz,by simpa [len,word,length_binSyms] using run⟩

open Node
variable {T Q A : ℕ} {P U : Type}

def readMatrixWord (index : ℕ) (r : Fin 7 ↪ Fin T) : Pr P T Q A U :=
  .seq (umul index (r 1) (r 0) (r 6))
    (.seq (copyAfterPrefix (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6)) (uclear (r 0)))

theorem readMatrixWord_exec {d e M : ℕ} [NeZero M] (body : P → Pr P T Q A U)
    (r : Fin 7 ↪ Fin T) (m : Matrix (Fin d) (Fin e) (ZMod M)) (i : Fin d) (j : Fin e) (H : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (matrix : S.R (r 2) = matrixWords A H m ++ tail) (hw : (S.R (r 1)).length = H)
    (fresh : ∀ k : Fin 7, k = 0 ∨ 4 ≤ k → S.R (r k) = []) :
    ∃ z, z.user = v.user ∧
      Exec body (readMatrixWord (i.val*e+j.val) r) (mk v S)
        (8*((i.val*e+j.val)*H)+14*H+22)
        (mk z {S with R := Function.update S.R (r 3) (binSyms H (m i j).val ++ S.R (r 3))}) := by
  let n := (i.val*e+j.val)*H
  let D : Stacks T A := {S with R := Function.update S.R (r 0) (List.replicate n tick)}
  have keep (k : Fin 7) (h : k ≠ 0) : D.R (r k) = S.R (r k) :=
    Function.update_of_ne (r.injective.ne h) _ _
  obtain ⟨u,hu,setup⟩ := umul_exec body (i.val*e+j.val) (a := r 1) (b := r 0) (t := r 6)
    (r.injective.ne (by decide)) (r.injective.ne (by decide)) (r.injective.ne (by decide))
    v S (fresh 6 (by decide))
  rw [hw,fresh 0 (by decide),List.append_nil] at setup
  obtain ⟨y,hy,read⟩ := matrixRead_exec body (skip := r 0) (width := r 1) (src := r 2)
    (dst := r 3) (savedPrefix := r 4) (savedWord := r 5) (tmp := r 6)
    (by simp [List.nodup_cons,r.injective.eq_iff]) m i j H u D tail
    ((keep 2 (by decide)).trans matrix) (by simp [D,n]) (by rw [keep 1 (by decide),hw])
    ((keep 4 (by decide)).trans (fresh 4 (by decide))) ((keep 5 (by decide)).trans (fresh 5 (by decide)))
    ((keep 6 (by decide)).trans (fresh 6 (by decide)))
  let E : Stacks T A := {D with R := Function.update D.R (r 3) (binSyms H (m i j).val ++ D.R (r 3))}
  obtain ⟨z,hz,clear⟩ := uclear_exec body (r 0) y E
  have len : (E.R (r 0)).length = n := by simp [E,D,r.injective.eq_iff]
  rw [len] at clear
  refine ⟨z,hz.trans (hy.trans hu),(Exec.seq setup (Exec.seq read clear)).cast (by dsimp [n]; omega) ?_⟩
  congr 1
  refine Stacks.ext ?_ ?_ ?_ ?_ <;> try rfl
  funext k
  by_cases h : k = r 0
  · subst k; simp [E,D,r.injective.eq_iff,fresh 0 (by decide)]
  · by_cases h' : k = r 3
    · subst k; simp [E,D,r.injective.eq_iff]
    · simp [E,D,h,h']

def pivotReadPorts : Fin 7 ↪ Fin 8 := Fin.castLEEmb (by decide)
def entryReadPorts : Fin 7 ↪ Fin 8 := ⟨![0,1,2,7,4,5,6],by decide⟩

def readColumnPair {d : ℕ} (j row pivot : Fin d) (r : Fin 8 ↪ Fin T) : Pr P T Q A U :=
  .seq (readMatrixWord (pivot.val*d+j.val) (pivotReadPorts.trans r))
    (readMatrixWord (row.val*d+j.val) (entryReadPorts.trans r))

theorem readColumnPair_exec {d M : ℕ} [NeZero M] (body : P → Pr P T Q A U)
    (r : Fin 8 ↪ Fin T) (m : Matrix (Fin d) (Fin d) (ZMod M)) (j row pivot : Fin d) (H : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (matrix : S.R (r 2) = matrixWords A H m ++ tail) (hw : (S.R (r 1)).length = H)
    (fresh : ∀ i : Fin 8, i ≠ 1 → i ≠ 2 → S.R (r i) = []) :
    ∃ z, z.user = v.user ∧ Exec body (readColumnPair j row pivot r) (mk v S)
      (8*((pivot.val*d+j.val)*H)+14*H+22 + (8*((row.val*d+j.val)*H)+14*H+22))
      (mk z {S with R := Function.update (Function.update S.R (r 3) (binSyms H (m pivot j).val)) (r 7) (binSyms H (m row j).val)}) := by
  have hp : ∀ i : Fin 7, i = 0 ∨ 4 ≤ i → pivotReadPorts i ≠ 1 ∧ pivotReadPorts i ≠ 2 := by decide
  have he : ∀ i : Fin 7, i = 0 ∨ 4 ≤ i →
      entryReadPorts i ≠ 1 ∧ entryReadPorts i ≠ 2 ∧ entryReadPorts i ≠ 3 := by decide
  obtain ⟨u,hu,p⟩ := readMatrixWord_exec body (pivotReadPorts.trans r) m pivot j H v S tail matrix hw
    (fun i h => fresh _ (hp i h).1 (hp i h).2)
  change Exec _ _ _ _ (mk u {S with R := Function.update S.R (r 3) (_ ++ S.R (r 3))}) at p
  rw [fresh 3 (by decide) (by decide),List.append_nil] at p
  let D : Stacks T A := {S with R := Function.update S.R (r 3) (binSyms H (m pivot j).val)}
  have keep (i : Fin 8) (h : i ≠ 3) : D.R (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne h) _ _
  obtain ⟨z,hz,e⟩ := readMatrixWord_exec body (entryReadPorts.trans r) m row j H u D tail
    ((keep 2 (by decide)).trans matrix) (by change (D.R (r 1)).length = H; rw [keep 1 (by decide),hw])
    (fun i h => (keep _ (he i h).2.2).trans (fresh _ (he i h).1 (he i h).2.1))
  change Exec _ _ _ _ (mk z {D with R := Function.update D.R (r 7) (_ ++ D.R (r 7))}) at e
  rw [keep 7 (by decide),fresh 7 (by decide) (by decide),List.append_nil] at e
  exact ⟨z,hz.trans hu,Exec.seq p e⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
