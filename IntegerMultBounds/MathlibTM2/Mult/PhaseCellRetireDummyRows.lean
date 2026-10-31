module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddingCounterSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoutedGatherSuffix

/-! Retire the dummy core prefix using a generated physical symbol count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def retireDummyRows (rows capacity batchWidth count missing saved tmp src : Fin T) : Pr P T Q A U :=
  .seq (paddingCounterSetup rows capacity batchWidth count missing saved tmp)
    (.seq (usub count src saved) (uclear count))

def retireDummyRowsCost (rows capacity width : ℕ) : ℕ :=
  paddingCounterSetupCost rows capacity width+6*((capacity-rows)*width)+6

theorem retireDummyRows_native (rows capacity batchWidth count missing saved tmp src : Fin T) :
    mnNativePushBound 2 (retireDummyRows (P := P) (Q := Q) (A := A) (U := U)
      rows capacity batchWidth count missing saved tmp src) := by
  refine ⟨paddingCounterSetup_native _ _ _ _ _ _ _,?_,?_⟩
  all_goals simp [usub,uclear,scanR,drainR,popDo,keepIn,dropTop,moveR,moveStep,whileR,peekR,
    mnNativePushBound,mnActPush]

theorem retireDummyRows_exec (rows capacity batchWidth count missing saved tmp src : Fin T)
    (hreg : [rows,capacity,batchWidth,count,missing,saved,tmp,src].Nodup)
    (v : HS T Q A U) (S : Stacks T A)
    (hcount : S.R count = []) (hmissing : S.R missing = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ retireDummyRowsCost (S.R rows).length (S.R capacity).length (S.R batchWidth).length ∧
      Exec body (retireDummyRows rows capacity batchWidth count missing saved tmp src) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R src
          ((S.R src).drop (((S.R capacity).length-(S.R rows).length)*(S.R batchWidth).length)))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := paddingCounterSetup_exec rows capacity batchWidth count missing saved tmp
    (by regs_nodup) v S hcount hmissing hsaved htmp
  let D := ((S.R capacity).length-(S.R rows).length)*(S.R batchWidth).length
  let F : Stacks T A := {S with R := Function.update S.R count (List.replicate D tick)}
  change Exec _ _ _ _ (Host.mk v₁ F) at he₁
  obtain ⟨v₂,hu₂,he₂⟩ := usub_exec body ‹count ≠ src› ‹count ≠ saved› ‹saved ≠ src›.symm v₁ F
    (by simp [F,‹count ≠ saved›.symm,hsaved])
  let G : Stacks T A := {F with R := Function.update F.R src ((S.R src).drop D)}
  have he₂' : Exec body (usub count src saved) (Host.mk v₁ F) (4*D+4) (Host.mk v₂ G) := by
    simpa [F,G,‹count ≠ src›.symm] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body count v₂ G
  have hlen : (G.R count).length = D := by simp [G,F,‹count ≠ src›]
  rw [hlen] at he₃
  have hend : {G with R := Function.update G.R count []} =
      {S with R := Function.update S.R src ((S.R src).drop D)} := by
    congr 1
    funext k
    by_cases hc : k = count
    · subst k; simp [G,F,‹count ≠ src›,hcount]
    · by_cases hx : k = src
      · subst k; simp [G,F,‹count ≠ src›.symm]
      · simp [G,F,hc,hx]
  rw [hend] at he₃
  refine ⟨v₃,n₁+((4*D+4)+(2*D+2)),hu₃.trans (hu₂.trans hu₁),?_,
    Exec.seq he₁ (Exec.seq he₂' he₃)⟩
  change n₁ ≤ paddingCounterSetupCost _ _ _ at hn₁
  change _ ≤ paddingCounterSetupCost _ _ _+6*D+6
  omega

theorem retireDummyRows_exec_within (rows capacity batchWidth count missing saved tmp src : Fin T)
    (hreg : [rows,capacity,batchWidth,count,missing,saved,tmp,src].Nodup)
    (v : HS T Q A U) (S : Stacks T A)
    (hcount : S.R count = []) (hmissing : S.R missing = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ retireDummyRowsCost (S.R rows).length (S.R capacity).length (S.R batchWidth).length ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        2*retireDummyRowsCost (S.R rows).length (S.R capacity).length (S.R batchWidth).length) depth
        (retireDummyRows rows capacity batchWidth count missing saved tmp src) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R src
          ((S.R src).drop (((S.R capacity).length-(S.R rows).length)*(S.R batchWidth).length)))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := retireDummyRows_exec rows capacity batchWidth count missing saved tmp src hreg v S
    hcount hmissing hsaved htmp
  exact ⟨v',n,hu,hn,mn_native_exec_within he 2 (retireDummyRows_native _ _ _ _ _ _ _ _) depth _ (by omega)⟩
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
