module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryPayloadCount
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefixStock

/-! Move one selected payload using retained replica, row and word rulers.
Generate and retire the byte counter without scanning the borrowed suffix or
absolute source endpoints. Local selection retains its row ruler on tape 116. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def generatedTakePrefix (replicas rows wide symbols count src dst saved tmp : Fin T) : Pr P T Q A U :=
  .seq (recoveryPayloadCount replicas rows wide symbols count saved tmp)
    (.seq (takePrefix count src dst saved tmp) (uclear count))

def generatedTakePrefixCost (N H W : ℕ) : ℕ :=
  recoveryPayloadCountCost N H W+(6*(N*(H*W))+6)+(2*(N*(H*W))+2)

theorem generatedTakePrefixCost_linear (N H W : ℕ) (hW : 1 ≤ W) :
    generatedTakePrefixCost N H W ≤ 36*((N+1)*(H*W+1)) := by
  have h := recoveryPayloadCountCost_linear N H W hW
  unfold generatedTakePrefixCost
  nlinarith

theorem generatedTakePrefix_native (replicas rows wide symbols count src dst saved tmp : Fin T) :
    mnNativePushBound 2 (generatedTakePrefix (P := P) (Q := Q) (A := A) (U := U)
      replicas rows wide symbols count src dst saved tmp) := by
  simp only [generatedTakePrefix,mnNativePushBound]
  exact ⟨recoveryPayloadCount_native ..,takePrefix_native ..,by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]⟩

theorem generatedTakePrefix_exec (replicas rows wide symbols count src dst saved tmp : Fin T)
    (hreg : [replicas,rows,wide,symbols,count,src,dst,saved,tmp].Nodup)
    (N H W : ℕ) (xs tail : List (Fin (A+4))) (hlen : xs.length = N*(H*W))
    (v : HS T Q A U) (S : Stacks T A)
    (hN : (S.R replicas).length = N) (hH : (S.R rows).length = H) (hW : (S.R wide).length = W)
    (hsrc : S.R src = xs++tail) (hblank : ∀ k ∈ [symbols,count,saved,tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generatedTakePrefixCost N H W ∧
      Exec body (generatedTakePrefix replicas rows wide symbols count src dst saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R src tail) dst (xs++S.R dst))}) ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        2*generatedTakePrefixCost N H W) depth
        (generatedTakePrefix replicas rows wide symbols count src dst saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R src tail) dst (xs++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,_⟩ := recoveryPayloadCount_exec (body := body)
    replicas rows wide symbols count saved tmp (by regs_nodup) N H W v S hN hH hW hblank
  let F : Stacks T A := {S with R := Function.update S.R count (List.replicate (N*(H*W)) tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := takePrefix_exec (body := body) (by regs_nodup : [count,src,dst,saved,tmp].Nodup)
    v₁ F xs tail (by simpa [F,‹count ≠ src›.symm] using hsrc)
    (by simp [F,hlen])
    (by simpa [F,‹count ≠ saved›.symm] using hblank saved (by simp))
    (by simpa [F,‹count ≠ tmp›.symm] using hblank tmp (by simp))
  let G : Stacks T A := {F with R := (Function.update (Function.update F.R src tail) dst (xs++F.R dst))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) count v₂ G
  have hcount : (G.R count).length = N*(H*W) := by simp [G,F,‹count ≠ dst›,‹count ≠ src›]
  have hfinal : {G with R := Function.update G.R count []} =
      {S with R := (Function.update (Function.update S.R src tail) dst (xs++S.R dst))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hc : k = count
    · subst k; simp [G,F,‹count ≠ dst›,‹count ≠ src›,hblank count (by simp)]
    · by_cases hd : k = dst
      · subst k; simp [G,F,‹count ≠ dst›.symm]
      · by_cases hs : k = src
        · subst k; simp [G,F,‹src ≠ dst›,‹count ≠ src›.symm]
        · simp [G,F,hc,hd,hs,‹count ≠ dst›.symm]
  rw [hcount,hfinal] at he₃
  have hex := Exec.seq he₁ (Exec.seq he₂ he₃)
  have hn : n₁+((6*xs.length+6)+(2*(N*(H*W))+2)) ≤ generatedTakePrefixCost N H W := by
    unfold generatedTakePrefixCost
    omega
  refine ⟨v₃,_,hu₃.trans (hu₂.trans hu₁),hn,hex,fun depth => ?_⟩
  exact mn_native_exec_within hex 2 (generatedTakePrefix_native ..) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
