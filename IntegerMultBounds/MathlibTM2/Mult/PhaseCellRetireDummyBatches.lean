module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireDummyRows

/-! Generate the replica-batch width before retiring padded dummy cores. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def retireDummyBatches (rows capacity replicas width batchWidth count missing saved tmp src : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct replicas width batchWidth saved tmp)
    (.seq (retireDummyRows rows capacity batchWidth count missing saved tmp src) (uclear batchWidth))

def retireDummyBatchesCost (rows capacity replicas width : ℕ) : ℕ :=
  replicas*(4*width+9)+4 + retireDummyRowsCost rows capacity (replicas*width) + (2*(replicas*width)+2)

theorem retireDummyBatches_native (rows capacity replicas width batchWidth count missing saved tmp src : Fin T) :
    mnNativePushBound 2 (retireDummyBatches (P := P) (Q := Q) (A := A) (U := U)
      rows capacity replicas width batchWidth count missing saved tmp src) := by
  refine ⟨?_,retireDummyRows_native _ _ _ _ _ _ _ _,?_⟩
  all_goals simp [unaryProduct,ucopy,umulSym,scanP,scanR,uclear,drainR,popDo,keepIn,pushN,
    moveR,moveStep,whileR,peekR,popPush,mnNativePushBound,mnActPush]

theorem retireDummyBatches_exec (rows capacity replicas width batchWidth count missing saved tmp src : Fin T)
    (hreg : [rows,capacity,replicas,width,batchWidth,count,missing,saved,tmp,src].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (hbatch : S.R batchWidth = [])
    (hcount : S.R count = []) (hmissing : S.R missing = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ retireDummyBatchesCost (S.R rows).length (S.R capacity).length (S.R replicas).length (S.R width).length ∧
      Exec body (retireDummyBatches rows capacity replicas width batchWidth count missing saved tmp src) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R src
          ((S.R src).drop (((S.R capacity).length-(S.R rows).length)*((S.R replicas).length*(S.R width).length))))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := replicas) (b := width) (dst := batchWidth) (t₁ := saved) (t₂ := tmp)
    (by regs_nodup) v S hsaved htmp
  let B := (S.R replicas).length*(S.R width).length
  let F : Stacks T A := {S with R := Function.update S.R batchWidth (List.replicate B tick)}
  simp only [hbatch,List.append_nil] at he₁
  change Exec _ _ _ _ (Host.mk v₁ F) at he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := retireDummyRows_exec rows capacity batchWidth count missing saved tmp src
    (by regs_nodup) v₁ F
    (by simp [F,hcount,‹batchWidth ≠ count›.symm])
    (by simp [F,hmissing,‹batchWidth ≠ missing›.symm])
    (by simp [F,hsaved,‹batchWidth ≠ saved›.symm])
    (by simp [F,htmp,‹batchWidth ≠ tmp›.symm])
  have hn₂' : n₂ ≤ retireDummyRowsCost (S.R rows).length (S.R capacity).length B := by
    simpa [F,‹rows ≠ batchWidth›,‹capacity ≠ batchWidth›] using hn₂
  let G : Stacks T A := {F with R := (Function.update F.R src
    ((S.R src).drop (((S.R capacity).length-(S.R rows).length)*B)))}
  have he₂' : Exec body (retireDummyRows rows capacity batchWidth count missing saved tmp src) (Host.mk v₁ F) n₂
      (Host.mk v₂ G) := by
    simpa [G,F,‹rows ≠ batchWidth›,‹capacity ≠ batchWidth›,‹batchWidth ≠ src›.symm] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body batchWidth v₂ G
  have hlen : (G.R batchWidth).length = B := by simp [G,F,‹batchWidth ≠ src›]
  rw [hlen] at he₃
  have hend : {G with R := Function.update G.R batchWidth []} =
      {S with R := Function.update S.R src ((S.R src).drop (((S.R capacity).length-(S.R rows).length)*B))} := by
    congr 1
    funext k
    by_cases hb : k = batchWidth
    · subst k; simp [G,F,‹batchWidth ≠ src›,hbatch]
    · by_cases hx : k = src
      · subst k; simp [G,F,‹batchWidth ≠ src›.symm]
      · simp [G,F,hb,hx]
  rw [hend] at he₃
  refine ⟨v₃,n₁+(n₂+(2*B+2)),hu₃.trans (hu₂.trans hu₁),?_,Exec.seq he₁ (Exec.seq he₂' he₃)⟩
  change _ ≤ (S.R replicas).length*(4*(S.R width).length+9)+4 +
    retireDummyRowsCost (S.R rows).length (S.R capacity).length B + (2*B+2)
  omega

theorem retireDummyBatches_exec_within (rows capacity replicas width batchWidth count missing saved tmp src : Fin T)
    (hreg : [rows,capacity,replicas,width,batchWidth,count,missing,saved,tmp,src].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (hbatch : S.R batchWidth = [])
    (hcount : S.R count = []) (hmissing : S.R missing = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ retireDummyBatchesCost (S.R rows).length (S.R capacity).length (S.R replicas).length (S.R width).length ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        2*retireDummyBatchesCost (S.R rows).length (S.R capacity).length (S.R replicas).length (S.R width).length) depth
        (retireDummyBatches rows capacity replicas width batchWidth count missing saved tmp src) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R src
          ((S.R src).drop (((S.R capacity).length-(S.R rows).length)*((S.R replicas).length*(S.R width).length))))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := retireDummyBatches_exec rows capacity replicas width batchWidth count missing saved tmp src
    hreg v S hbatch hcount hmissing hsaved htmp
  exact ⟨v',n,hu,hn,mn_native_exec_within he 2 (retireDummyBatches_native _ _ _ _ _ _ _ _ _ _) depth _ (by omega)⟩
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
