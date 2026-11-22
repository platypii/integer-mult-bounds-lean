module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepRankAdvance
public import IntegerMultBounds.MathlibTM2.Routing.DescriptorTableCompile

/-! Count destination ranks onto a reverse buffer for the selector compiler. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Node RadixDigits RadixCounterData Routing
variable {T Q q M : ℕ} {P U : Type}

private theorem frames_snoc (H : ℕ) (xs : List (Fin M)) (x : Fin M) :
    descriptorSelectorFrames (A := q) H (xs ++ [x]) =
      descriptorSelectorFrames H xs ++ (binSyms H x.val ++ [separator]) := by
  induction xs with
  | nil => simp [descriptorSelectorFrames]
  | cons y ys ih => simp [descriptorSelectorFrames,ih,List.append_assoc]

private theorem advance_succ (hq : 2 ≤ q) (j : ℕ) (xs : List (Fin q)) :
    advance hq (j+1) xs = increment hq (advance hq j xs) := by
  induction j generalizing xs with
  | zero => rfl
  | succ j ih => exact ih (increment hq xs)

theorem sweepSelectorLoop_exec (body : P → Pr P T Q q U) (hq : 2 ≤ q) (r : Fin 7 ↪ Fin T)
    (matrix count saved : Fin T) (apart : ∀ i, r i ≠ matrix)
    (ports : [matrix,count,saved].Nodup) (outside : ∀ i, r i ≠ count ∧ r i ≠ saved)
    (ds : List (Fin q)) (pos : 0 < ds.length) (H cost : ℕ) (rank : ℕ → Fin M)
    (mat : ℕ → List (Fin (q+4))) (evaluate : Pr P T Q q U) (v : HS T Q q U) (S : Stacks T q)
    (counter : S.R (r 0) = ds.map digitSymbol) (width : (S.R (r 5)).length = ds.length)
    (initial : S.R matrix = mat 0) (free : ∀ i : Fin 7, i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 6 → S.R (r i) = []) :
    let stream := fun j => (descriptorSelectorFrames (A := q) H ((List.range j).map rank)).reverse ++ S.R (r 2)
    let state := fun j => Function.update (Function.update (Function.update S.R matrix (mat j))
      (r 0) ((advance hq j ds).map digitSymbol)) (r 2) (stream j)
    (∀ j < (S.R count).length, ∀ u (B : Stacks T q), (∀ k, k ≠ count → k ≠ saved → B.R k = state j k) →
      ∃ y k, y.user = u.user ∧ k ≤ cost ∧ Exec body evaluate (mk u B) k (mk y {B with
        R := Function.update (Function.update B.R matrix (mat (j+1))) (r 1) (binSyms H (rank j).val)})) →
    let N := (S.R count).length
    ∃ z R n, z.user = v.user ∧ n ≤ N*(cost+(2*H+9*ds.length+15)+3)+2 ∧
      Exec body (eachSym count saved (.seq evaluate (advanceSweepRank hq r))) (mk v S) n (mk z {S with R := R}) ∧
      R count = [] ∧ R saved = (S.R count).reverse ++ S.R saved ∧
      ∀ k, k ≠ count → k ≠ saved → R k = state N k := by
  intro stream state run N
  regs_ne ports
  apply eachSym_exec body ‹count ≠ saved› v S
  · intro j hj u B _ agree
    obtain ⟨y,k,hy,hk,eval⟩ := run j hj u B agree
    have slot (i) := agree (r i) (outside i).1 (outside i).2
    obtain ⟨z,n,hz,hn,step⟩ := sweepSelectorStep_exec body hq r matrix apart (mat (j+1)) evaluate
      (advance hq j ds) (by simpa using pos) H (rank j).val u y B k hy (by simp [slot,state,apart])
      (by simpa [slot,state,apart] using width)
      (fun i hi => by rcases hi with rfl|rfl|rfl|rfl <;> simp [slot,state,apart,free]) eval
    refine ⟨z,_,n,hz,by simpa using hn.trans (Nat.add_le_add_right hk _),step,?_,?_,?_⟩
    · simp [Ne.symm (outside _).1,Ne.symm ‹matrix ≠ count›]
    · simp [Ne.symm (outside _).2,Ne.symm ‹matrix ≠ saved›]
    · intro i hc hs
      have next : stream (j+1) = separator :: (binSyms H (rank j).val).reverse ++ stream j := by
        simp [stream,List.range_succ,frames_snoc,List.append_assoc]
      have buffer : B.R (r 2) = stream j := by simp [slot,state]
      by_cases h₀ : i = r 0
      · subst i; simp [state,advance_succ]
      by_cases h₂ : i = r 2
      · subst i; simp [state,buffer,next]
      by_cases hm : i = matrix
      · subst i; simp [state,h₀,h₂]
      · simpa [state,h₀,h₂,hm] using agree i hc hs
  · intro i _ _
    simp [state,stream,advance,descriptorSelectorFrames,← counter,← initial]

/-- One reversal restores both destination order and the bit order within
each frame, giving the table compiler its exact input. -/
theorem finishSweepSelectors_exec (body : P → Pr P T Q q U) (buf out : Fin T) (apart : buf ≠ out)
    (H : ℕ) (rank : ℕ → Fin M) (source : Fin M → Fin M) (correct : ∀ i : Fin M, rank i.val = source i)
    (v : HS T Q q U) (S : Stacks T q)
    (stream : S.R buf = (descriptorSelectorFrames H ((List.range M).map rank)).reverse) :
    ∃ z, z.user = v.user ∧ Exec body (moveR buf out id) (mk v S) (2*(M*(H+1))+2)
      (mk z {S with
       R := Function.update (Function.update S.R buf []) out
        (descriptorSelectorFrames H (List.ofFn source) ++ S.R out)}) := by
  have order : (List.range M).map rank = List.ofFn source := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simpa using correct ⟨i,by simpa using hj⟩
  obtain ⟨z,hz,move⟩ := moveR_exec body buf out apart id v S
  refine ⟨z,hz,?_⟩
  simpa [stream,order,movedR,descriptorSelectorFrames_length,Nat.mul_comm] using move

end IntegerMultBounds.MathlibTM2.M6.BitNode
