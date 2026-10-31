module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPublicationPlan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringReplicaPublication

/-! Prepare controls once for a whole replica class, publish all replicas,
restore the borrowed clock, then release the controls. Scratch is reused
between stages. Only the archive source and ambient destination change. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PreparedPublicationPlan
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s L : ℕ} {src dst : Fin T} {P U : Type} {body : P → Pr P T Q A U}

def replicaProgram (plan : PreparedPublicationPlan T src dst) (clock lineRows : Fin T) : Pr P T Q A U :=
  .seq (windowPublicationControls plan.count plan.savedControl plan.advances plan.savedAdvances plan.counter
    plan.window plan.zero plan.acc plan.control plan.trash plan.tmp)
    (.seq (restoringReplicaPublication clock plan.zero plan.padRows plan.wordWidth plan.retireCount plan.control
      plan.savedControl plan.gap plan.window src dst plan.acc plan.trash plan.tmp lineRows plan.counter plan.savedAdvances)
      (uclear plan.control))

theorem replica_exec (plan : PreparedPublicationPlan T src dst) (clock lineRows : Fin T)
    (hreg : (plan.support++[src,dst,clock,lineRows]).Nodup)
    (windows : PublicationWindows s L) (w missing : ℕ) (hw1 : 1 ≤ w)
    (replicas : List (PublicationReplica A)) (hvalid : ∀ r ∈ replicas, r.Valid windows w missing)
    (sourceTail outputTail borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hready : plan.Ready windows w missing borrowed S)
    (hsrc : S.R src = replicas.flatMap (PublicationReplica.input w)++sourceTail)
    (hdst : S.R dst = replicas.flatMap PublicationReplica.ambient++outputTail)
    (hclock : (S.R clock).length = replicas.length) (hline : (S.R lineRows).length = s) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ replicaPublicationCost replicas.length s missing L w+37*s*w+6*replicas.length+31 ∧
      Exec body (plan.replicaProgram clock lineRows) (Host.mk v S) n (Host.mk v' F) ∧
      F.R src = sourceTail ∧ F.R dst = replicas.flatMap (PublicationReplica.output windows w)++outputTail ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ src → i ≠ dst → F.R i = S.R i := by
  have hr := hreg
  change [plan.count,plan.savedControl,plan.advances,plan.savedAdvances,plan.counter,plan.window,plan.zero,plan.acc,
    plan.control,plan.trash,plan.tmp,plan.padRows,plan.wordWidth,plan.retireCount,plan.gap,src,dst,clock,lineRows].Nodup at hr
  regs_ne hr
  have hz := hready.fresh
  have hcontrol := hz plan.control (by simp)
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := windowPublicationControls_exec (body := body)
    plan.count plan.savedControl plan.advances plan.savedAdvances plan.counter plan.window plan.zero plan.acc plan.control plan.trash plan.tmp
    (by regs_nodup) windows w hw1 borrowed v S hready.count hready.advances hready.window (by
      intro i hi; apply hz i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  let M : Stacks T A := {S with R := Function.update S.R plan.control (gatherControls A (windows.gaps w))}
  have he₁' : Exec body (windowPublicationControls plan.count plan.savedControl plan.advances plan.savedAdvances plan.counter
      plan.window plan.zero plan.acc plan.control plan.trash plan.tmp) (Host.mk v S) n₁ (Host.mk v₁ M) := by
    simpa only [hcontrol,List.append_nil] using he₁
  have hstable (i : Fin T) (hi : i ≠ plan.control) : M.R i = S.R i := by simp [M,hi]
  obtain ⟨v₂,F,n₂,hu₂,hn₂,he₂,hs,hd,hi,ho,hl,hframe⟩ := restoringReplicaPublication_exec (body := body)
    clock plan.zero plan.padRows plan.wordWidth plan.retireCount plan.control plan.savedControl plan.gap plan.window
    src dst plan.acc plan.trash plan.tmp lineRows plan.counter plan.savedAdvances (by regs_nodup)
    windows w missing hw1 replicas hvalid sourceTail outputTail v₁ M
    (by rw [hstable _ ‹plan.control ≠ src›.symm]; exact hsrc)
    (by rw [hstable _ ‹plan.control ≠ dst›.symm]; exact hdst)
    (by rw [hstable _ ‹plan.control ≠ clock›.symm]; exact hclock)
    (by rw [hstable _ ‹plan.zero ≠ plan.control›]; exact hz _ (by simp))
    (by rw [hstable _ ‹plan.control ≠ plan.padRows›.symm]; exact hready.padRows)
    (by rw [hstable _ ‹plan.control ≠ plan.wordWidth›.symm]; exact hready.wordWidth)
    (by rw [hstable _ ‹plan.control ≠ lineRows›.symm]; exact hline)
    (by simp [M]) (by rw [hstable _ ‹plan.window ≠ plan.control›]; exact hready.window)
    (by
      intro i hi
      have ho : i ≠ plan.control := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [hstable i ho]
      apply hz i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    (by rw [hstable _ ‹plan.counter ≠ plan.control›]; exact hz _ (by simp))
  have hF : F.R plan.control = gatherControls A (windows.gaps w) := by
    rw [hframe _ ‹plan.control ≠ src› ‹plan.control ≠ dst›]; simp [M]
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := releaseWindowPublicationControls_exec (body := body) plan.control windows w hw1 v₂ F hF
  let G : Stacks T A := {F with R := Function.update F.R plan.control []}
  refine ⟨v₃,G,n₁+(n₂+n₃),hu₃.trans (hu₂.trans hu₁),?_,Exec.seq he₁' (Exec.seq he₂ he₃),?_,?_,hi,ho,hl,?_⟩
  · nlinarith only [hn₁,hn₂,hn₃]
  · simpa only [G,Function.update_of_ne ‹plan.control ≠ src›.symm] using hs
  · simpa only [G,Function.update_of_ne ‹plan.control ≠ dst›.symm] using hd
  · intro i his hid
    by_cases hc : i = plan.control
    · subst i; simp [G,hcontrol]
    · simp only [G,Function.update_of_ne hc]
      rw [hframe i his hid,hstable i hc]

theorem replica_native (plan : PreparedPublicationPlan T src dst) (clock lineRows : Fin T) :
    mnNativePushBound 2 (plan.replicaProgram (P := P) (Q := Q) (A := A) (U := U) clock lineRows) := by
  have hp := preparedWindowPublication_native (P := P) (Q := Q) (A := A) (U := U)
    plan.count plan.savedControl plan.advances plan.savedAdvances plan.counter plan.window plan.zero plan.acc plan.control plan.trash plan.tmp
    plan.padRows plan.wordWidth plan.retireCount plan.gap src dst
  refine ⟨hp.1,restoringReplicaPublication_native _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,?_⟩
  simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

theorem replica_within {plan : PreparedPublicationPlan T src dst} {clock lineRows : Fin T}
    {v v' : HS T Q A U} {S F : Stacks T A} {n N missing w : ℕ}
    (he : Exec body (plan.replicaProgram clock lineRows) (Host.mk v S) n (Host.mk v' F))
    (hn : n ≤ replicaPublicationCost N s missing L w+37*s*w+6*N+31) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
      2*(replicaPublicationCost N s missing L w+37*s*w+6*N+31)) depth
      (plan.replicaProgram clock lineRows) (Host.mk v S) n (Host.mk v' F) := by
  exact mn_native_exec_within he 2 (plan.replica_native clock lineRows) depth _ (by omega)

/-- Setup is paid once per class; replica work is linear in padding and ambient
volume. The six clock-save steps per replica are absorbed by one ambient pass. -/
theorem replica_cost_le (N s missing L w : ℕ) (hs : 1 ≤ s) (hw : 1 ≤ w) :
    replicaPublicationCost N s missing L w+37*s*w+6*N+31 ≤
      N*(21*(missing*L*w)+93*(s*w))+37*s*w+35 := by
  have hb := replicaPublicationCost_le N s missing L w hs hw
  have hsw : 1 ≤ s*w := Nat.mul_pos hs hw
  have hm := Nat.mul_le_mul_left N (show 87*(s*w)+6 ≤ 93*(s*w) by omega)
  nlinarith only [hb,hm]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PreparedPublicationPlan
