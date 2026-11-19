module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackItineraryMachine

/-! Read a pivot stage in either direction without consuming the two-stack archive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Node
open Mult.PhaseCellToeplitz
variable {P U α : Type} {T Q A : ℕ}

/-- At distance g from the newest stage, the desired snapshot is behind
g / 2 snapshots on the stack selected by parity. -/
theorem archiveStage_split (stage : ℕ → List α) (tail dest : List α) (j size : ℕ)
    (gap : ℕ) (width : ∀ k, j ≤ k → k ≤ j+gap → (stage k).length = size) :
    let pair := matrixArchive stage (stage 0 ++ tail) dest (j+gap)
    ∃ pre post, (if gap % 2 = 0 then pair.1 else pair.2) = pre ++ stage j ++ post ∧
      pre.length = gap/2*size := by
  cases gap with
  | zero =>
    cases j <;> exact ⟨[],_,rfl,by simp⟩
  | succ g =>
    cases g with
    | zero =>
      cases j <;> exact ⟨[],_,rfl,by simp⟩
    | succ g =>
      obtain ⟨pre,post,split,len⟩ := archiveStage_split stage tail dest j size g
        (fun k lo hi => width k lo (by omega))
      have parity : (g+2)%2 = g%2 := by omega
      have half : (g+2)/2 = g/2+1 := by omega
      by_cases even : g%2 = 0
      · refine ⟨stage (j+g+2) ++ pre,post,?_,?_⟩
        · simp only [parity,even,ite_true,matrixArchive,List.append_assoc] at split ⊢
          exact congrArg (stage (j+g+2) ++ ·) split
        · rw [List.length_append,width (j+g+2) (by omega) (by omega),len,half,Nat.succ_mul]
          omega
      · refine ⟨stage (j+g+1) ++ pre,post,?_,?_⟩
        · simpa [parity,even,matrixArchive,List.append_assoc] using congrArg (stage (j+g+1) ++ ·) split
        · rw [List.length_append,width (j+g+1) (by omega) (by omega),len,half,Nat.succ_mul]
          omega

/-- Copy a whole selected stage to the column reader's input tape, preserving
both archive stacks. The counters measure the skip and snapshot in symbols. -/
theorem copyArchiveStage_exec (body : P → Pr P T Q A U) (r : Fin 7 ↪ Fin T)
    (stage : ℕ → List (Fin (A+4))) (tail dest : List (Fin (A+4))) (j gap size : ℕ)
    (width : ∀ k, j ≤ k → k ≤ j+gap → (stage k).length = size)
    (v : HS T Q A U) (S : Stacks T A)
    (packed : let pair := matrixArchive stage (stage 0 ++ tail) dest (j+gap)
              S.R (r 2) = if gap%2 = 0 then pair.1 else pair.2)
    (count : (S.R (r 1)).length = size)
    (free : ∀ k : Fin 7, k = 0 ∨ 4 ≤ k → S.R (r k) = []) :
    ∃ z, z.user = v.user ∧ Exec body (readMatrixWord (gap/2) r) (mk v S)
      (8*(gap/2*size)+14*size+22)
      (mk z {S with R := Function.update S.R (r 3) (stage j ++ S.R (r 3))}) := by
  obtain ⟨pre,post,split,len⟩ := archiveStage_split stage tail dest j size gap width
  let n := gap/2*size
  let D : Stacks T A := {S with R := Function.update S.R (r 0) (List.replicate n tick)}
  have keep (k : Fin 7) (ne : k ≠ 0) : D.R (r k) = S.R (r k) :=
    Function.update_of_ne (r.injective.ne ne) _ _
  obtain ⟨u,hu,setup⟩ := umul_exec body (gap/2) (a := r 1) (b := r 0) (t := r 6)
    (r.injective.ne (by decide)) (r.injective.ne (by decide)) (r.injective.ne (by decide)) v S (free 6 (by decide))
  rw [count,free 0 (by decide),List.append_nil] at setup
  obtain ⟨y,hy,copy⟩ := copyAfterPrefix_exec (body := body) (skip := r 0) (width := r 1)
    (src := r 2) (dst := r 3) (savedPrefix := r 4) (savedWord := r 5) (tmp := r 6)
    (by simp [List.nodup_cons,r.injective.eq_iff]) u D pre (stage j) post
    (by simpa only [List.append_assoc] using (keep 2 (by decide)).trans (packed.trans split))
    (by simp [D,n,len]) (by rw [keep 1 (by decide),count,width j (by omega) (by omega)])
    ((keep 4 (by decide)).trans (free 4 (by decide))) ((keep 5 (by decide)).trans (free 5 (by decide)))
    ((keep 6 (by decide)).trans (free 6 (by decide)))
  let E : Stacks T A := {D with R := Function.update D.R (r 3) (stage j ++ D.R (r 3))}
  obtain ⟨z,hz,clear⟩ := uclear_exec body (r 0) y E
  have used : (E.R (r 0)).length = n := by simp [E,D,r.injective.eq_iff]
  rw [used] at clear
  refine ⟨z,hz.trans (hy.trans hu),(Exec.seq setup (Exec.seq copy clear)).cast ?_ ?_⟩
  · rw [len,width j (by omega) (by omega)]
    dsimp [n]
    omega
  · congr 1
    refine Stacks.ext ?_ ?_ ?_ ?_ <;> try rfl
    funext k
    by_cases h : k = r 0
    · subst k; simp [E,D,r.injective.eq_iff,free 0 (by decide)]
    · by_cases h' : k = r 3
      · subst k; simp [E,D,r.injective.eq_iff]
      · simp [E,D,h,h']

open GoodForm in
/-- The archive produced by good-record elimination supplies the original
stage matrix for pivot a, even after all later pivots have been processed. -/
theorem copyGoodPivotStage_exec {d M : ℕ} [NeZero M] (body : P → Pr P T Q A U)
    (r : Fin 7 ↪ Fin T) (G : Matrix (Fin d) (Fin d) (ZMod M)) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ k (hk : k < rank), IsUnit (lead (k+1) (lt_of_lt_of_le hk hr) G).det)
    (a : Fin rank) (H : ℕ) (tail dest : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A) :
    let words := fun k => if hk : k ≤ rank then matrixWords A H (stageAt G rank hr minor k hk).M else []
    let pair := matrixArchive words (words 0 ++ tail) dest rank
    let gap := rank-a.val
    S.R (r 2) = (if gap%2 = 0 then pair.1 else pair.2) →
    (S.R (r 1)).length = d*d*H →
    (∀ k : Fin 7, k = 0 ∨ 4 ≤ k → S.R (r k) = []) →
    ∃ z, z.user = v.user ∧ Exec body (readMatrixWord (gap/2) r) (mk v S)
      (8*(gap/2*(d*d*H))+14*(d*d*H)+22)
      (mk z {S with R := Function.update S.R (r 3) (matrixWords A H (stageAt G rank hr minor a.val a.isLt.le).M ++ S.R (r 3))}) := by
  intro words pair gap packed count free
  have total : a.val + gap = rank := Nat.add_sub_of_le a.isLt.le
  have width (k : ℕ) (_ : a.val ≤ k) (hi : k ≤ a.val+gap) : (words k).length = d*d*H := by
    rw [total] at hi
    simp [words,hi,matrixWords,List.length_flatten,List.map_ofFn,Function.comp_def,length_binSyms,
      List.ofFn_const,Nat.mul_assoc]
  simpa only [words,dite_eq_left a.isLt.le] using
    copyArchiveStage_exec body r words tail dest a.val gap (d*d*H) width v S
      (by simpa only [total] using packed) count free

end IntegerMultBounds.MathlibTM2.Cover.Fallback
