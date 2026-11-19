module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodHeadArchive
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPairWeights

/-! Prepare one archived pivot for an entire column of weighted head shears. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host GoodForm
variable {P U : Type} {T Q A d b w : ℕ} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

def prepareHeadPivot (b rank a : ℕ) (reader : Fin 7 ↪ Fin T) (child : Fin 20 ↪ Fin T) : Pr P T Q A U :=
  .seq (readMatrixWord ((rank-a)/2) reader) (signedChildPair b a a child)

def headPivotPrepareTime (b d w H a gap : ℕ) : ℕ :=
  let C := 48*H*H+152*H+66
  (8*(gap/2*(d*d*H))+14*(d*d*H)+22) +
      ((8*(a*H)+14*H+22)+((8*(a*H)+48*H*H+166*H+88)+
        (6*w+6+(14*H+16+(b-2)*C+C+w*(12*H+15+b*C))))+(2*H+2)+(8*H+8))

/-- Load the stage once per pivot. Both reciprocal signs are available on the
same final configuration, and only the stage and three arithmetic outputs change. -/
theorem prepareHeadPivot_exec (body : P → Pr P T Q A U) (reader : Fin 7 ↪ Fin T)
    (child : Fin 20 ↪ Fin T) (apart : ∀ j, child j ≠ reader 3)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ k (hk : k < rank), IsUnit (lead (k+1) (lt_of_lt_of_le hk hr) G).det)
    (a : Fin rank) (parent inv : Fin d → ZMod M) (inverse : ∀ i, parent i * inv i = 1)
    (hb : b.Prime) (H : ℕ) (hm : M < 2^H) (v : HS T Q A U) (S : Stacks T A)
    (tail dest rest pivotTail : List (Fin (A+4))) :
    let words := fun k => if hk : k ≤ rank then matrixWords A H (stageAt G rank hr minor k hk).M else []
    let pair := matrixArchive words (words 0 ++ tail) dest rank
    let gap := rank-a.val
    let pivot := fun i : Fin rank => (stageAt G rank hr minor rank le_rfl).M (i.castLE hr) (i.castLE hr)
    S.R (reader 2) = (if gap%2 = 0 then pair.1 else pair.2) →
    (S.R (reader 1)).length = d*d*H →
    (∀ k : Fin 7, k = 0 ∨ 4 ≤ k → S.R (reader k) = []) →
    S.R (child 19) = (List.ofFn fun k => binSyms H (parent k).val).flatten ++ rest →
    S.R (child 18) = (List.ofFn fun k => binSyms H (pivot k).val).flatten ++ pivotTail →
    S.R (child 4) = binSyms H M → S.R (child 15) = binSyms H (1 : ZMod M).val →
    (S.R (child 16)).length = w →
    (∀ k : Fin 20, (k ≤ 14 ∧ k ≠ 4) ∨ k = 17 → S.R (child k) = []) →
    let k := a.castLE hr
    let reciprocal := inv k * Ring.inverse (pivot a)
    ∃ z F n, z.user = v.user ∧ n ≤ headPivotPrepareTime b d w H a.val gap ∧
      Exec body (prepareHeadPivot b rank a.val reader child) (mk v S) n (mk z F) ∧
      F.R (reader 3) = words a.val ++ S.R (reader 3) ∧
      F.R (child 0) = binSyms H reciprocal.val ∧ F.R (child 12) = binSyms H (-reciprocal).val ∧
      F.R (child 14) = binSyms H (parent k * pivot a).val ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      ∀ j, j ≠ reader 3 → j ≠ child 0 → j ≠ child 14 → j ≠ child 12 → F.R j = S.R j := by
  intro words pair gap pivot packed count free parentWord pivots modulus one clock scratch k reciprocal
  obtain ⟨u,hu,read⟩ := copyGoodPivotStage_exec body reader G rank hr minor a H tail dest v S packed count free
  let D : Stacks T A := {S with R := Function.update S.R (reader 3) (words a.val ++ S.R (reader 3))}
  have eq : words a.val = matrixWords A H (stageAt G rank hr minor a.val a.isLt.le).M := dite_eq_left a.isLt.le
  have keep (j : Fin 20) : D.R (child j) = S.R (child j) := Function.update_of_ne (apart j) _ _
  obtain ⟨z,F,n,hz,time,run,prod,pos,neg,left,inp,out,frame⟩ := signedChildPair_exec body child
    parent k (inv k) (inverse k) pivot a ((stageAt G rank hr minor rank le_rfl).unit _ a.isLt)
    hb H hm u D pivotTail rest ((keep 19).trans parentWord) ((keep 18).trans pivots)
    ((keep 4).trans modulus) ((keep 15).trans one) (by rw [keep,clock]) (fun j hj => (keep j).trans (scratch j hj))
  rw [← eq] at read
  refine ⟨z,F,_,hz.trans hu,Nat.add_le_add_left time _,Exec.seq read run,?_,pos,neg,prod,left,inp,out,?_⟩
  · exact (frame _ (apart 0).symm (apart 14).symm (apart 12).symm).trans (Function.update_self ..)
  · intro j ne h0 h14 h12
    exact (frame j h0 h14 h12).trans (Function.update_of_ne ne _ _)

/-- With an empty stage destination on entry, the four temporary outputs
can be recycled for the next pivot at a cost independent of the payload. -/
theorem clearHeadPivot_exec (body : P → Pr P T Q A U) (stage : Fin T) (child : Fin 20 ↪ Fin T)
    (apart : ∀ j, child j ≠ stage) (H size : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (matrix : (S.R stage).length = size)
    (weights : ∀ j : Fin 20, j = 0 ∨ j = 12 ∨ j = 14 → (S.R (child j)).length = H) :
    let outputs := [stage,child 0,child 12,child 14]
    ∃ z, z.user = v.user ∧ Exec body (Mult.ShortConv.clearWords outputs) (mk v S)
      (2*(size+3*H)+9) (mk z {S with R := fun j => if j ∈ outputs then [] else S.R j}) := by
  intro outputs
  have distinct : outputs.Nodup := by
    simp [outputs,List.nodup_cons,child.injective.eq_iff,Ne.symm (apart 0),Ne.symm (apart 12),Ne.symm (apart 14)]
  obtain ⟨z,hz,run⟩ := Mult.ShortConv.clearWords_exec (body := body) outputs distinct v S
  refine ⟨z,hz,run.cast ?_ rfl⟩
  simp [outputs,matrix,weights 0 (by decide),weights 12 (by decide),weights 14 (by decide)]
  ring

end IntegerMultBounds.MathlibTM2.Cover.Fallback
