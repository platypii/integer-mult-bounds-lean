module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationStock

/-! A replica-class sweep borrows its clock. Saving the clock in reverse and
moving it back after the batch restores every tape except source/destination,
so later classes can reuse the same replica dimension. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s L : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def restoringReplicaPublication
    (clock clockSave padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved : Fin T) : Pr P T Q A U :=
  .seq (copyR clock clockSave tmp id)
    (.seq (.seq (countedLoop clock (replicaPublicationStep padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved))
      (moveR outAcc dst id)) (moveR clockSave clock id))

theorem restoringReplicaPublication_exec
    (clock clockSave padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved : Fin T)
    (hreg : [clock,clockSave,padRows,wordWidth,retireCount,control,savedControl,gap,window,src,dst,acc,trash,tmp,lineRows,outAcc,saved].Nodup)
    (windows : PublicationWindows s L) (w missing : ℕ) (hw1 : 1 ≤ w)
    (replicas : List (PublicationReplica A)) (hvalid : ∀ r ∈ replicas, r.Valid windows w missing)
    (sourceTail outputTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = replicas.flatMap (PublicationReplica.input w)++sourceTail)
    (hdst : S.R dst = replicas.flatMap PublicationReplica.ambient++outputTail)
    (hclock : (S.R clock).length = replicas.length) (hclockSave : S.R clockSave = [])
    (hpadRows : (S.R padRows).length = missing*L) (hwidth : (S.R wordWidth).length = w)
    (hlineRows : (S.R lineRows).length = s)
    (hc : S.R control = gatherControls A (windows.gaps w)) (hw : (S.R window).length = L*w)
    (hclean : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,tmp,saved], S.R i = [])
    (houtAcc : S.R outAcc = []) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ replicaPublicationCost replicas.length s missing L w+6*replicas.length+6 ∧
      Exec body (restoringReplicaPublication clock clockSave padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved)
        (mk v S) n (mk v' F) ∧
      F.R src = sourceTail ∧ F.R dst = replicas.flatMap (PublicationReplica.output windows w)++outputTail ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ src → i ≠ dst → F.R i = S.R i := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := copyR_exec (body := body) clock clockSave tmp ‹clock ≠ clockSave› ‹clock ≠ tmp› ‹clockSave ≠ tmp› id v S
    (hclean _ (by simp))
  let M : Stacks T A := {S with R := Function.update S.R clockSave (S.R clock).reverse}
  have he₁' : Exec body (copyR clock clockSave tmp id) (mk v S) (4*replicas.length+4) (mk v₁ M) := by
    simpa only [List.map_id,hclockSave,List.append_nil,hclock] using he₁
  have hstable (i : Fin T) (hi : i ≠ clockSave) : M.R i = S.R i := by simp [M,hi]
  obtain ⟨v₂,F,n₂,hu₂,hn₂,he₂,hs,hd,ha,hcl,hi,ho,hl,hframe⟩ := replicaPublicationBatch_exec (body := body)
    clock padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved (by regs_nodup)
    windows w missing hw1 replicas hvalid sourceTail outputTail v₁ M
    (by rw [hstable _ ‹clockSave ≠ src›.symm]; exact hsrc)
    (by rw [hstable _ ‹clockSave ≠ dst›.symm]; exact hdst)
    (by rw [hstable _ ‹clock ≠ clockSave›]; exact hclock)
    (by rw [hstable _ ‹clockSave ≠ padRows›.symm]; exact hpadRows)
    (by rw [hstable _ ‹clockSave ≠ wordWidth›.symm]; exact hwidth)
    (by rw [hstable _ ‹clockSave ≠ lineRows›.symm]; exact hlineRows)
    (by rw [hstable _ ‹clockSave ≠ control›.symm]; exact hc)
    (by rw [hstable _ ‹clockSave ≠ window›.symm]; exact hw)
    (by
      intro i hi
      have hne : i ≠ clockSave := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [hstable i hne]; exact hclean i hi)
    (by rw [hstable _ ‹clockSave ≠ outAcc›.symm]; exact houtAcc)
  have hsave : F.R clockSave = (S.R clock).reverse := by
    rw [hframe _ ‹clockSave ≠ src› ‹clockSave ≠ dst› ‹clock ≠ clockSave›.symm]
    simp [M]
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body clockSave clock ‹clock ≠ clockSave›.symm id v₂ F
  let G : Stacks T A := {F with R := movedR F.R clockSave clock id (F.R clockSave)}
  have he₃' : Exec body (moveR clockSave clock id) (mk v₂ F) (2*replicas.length+2) (mk v₃ G) := by
    simpa only [G,hsave,List.length_reverse,hclock] using he₃
  refine ⟨v₃,G,(4*replicas.length+4)+(n₂+(2*replicas.length+2)),hu₃.trans (hu₂.trans hu₁),?_,
    Exec.seq he₁' (Exec.seq he₂ he₃'),?_,?_,hi,ho,hl,?_⟩
  · change n₂ ≤ replicaPublicationCost replicas.length s missing L w at hn₂
    omega
  · simpa [G,movedR,‹clockSave ≠ src›.symm,‹clock ≠ src›.symm] using hs
  · simpa [G,movedR,‹clockSave ≠ dst›.symm,‹clock ≠ dst›.symm] using hd
  · intro i his hid
    by_cases hic : i = clock
    · subst i; simp [G,movedR,hsave,hcl]
    · by_cases hiz : i = clockSave
      · subst i; simp [G,movedR,‹clock ≠ clockSave›.symm,hclockSave]
      · simp only [G,movedR,Function.update_of_ne hic,Function.update_of_ne hiz]
        rw [hframe i his hid hic,hstable i hiz]

theorem restoringReplicaPublication_native
    (clock clockSave padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved : Fin T) :
    mnNativePushBound 2 (restoringReplicaPublication (P := P) (Q := Q) (A := A) (U := U)
      clock clockSave padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved) := by
  refine ⟨?_,replicaPublication_pushBound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,?_⟩
  · simp [copyR,copyStep,moveR,moveStep,peekR,whileR,mnNativePushBound,mnActPush]
  · simp [moveR,moveStep,peekR,whileR,mnNativePushBound,mnActPush]

theorem restoringReplicaPublication_within
    {clock clockSave padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved : Fin T}
    {v v' : HS T Q A U} {S F : Stacks T A} {n N missing w : ℕ}
    (he : Exec body (restoringReplicaPublication clock clockSave padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved)
      (mk v S) n (mk v' F))
    (hn : n ≤ replicaPublicationCost N s missing L w+6*N+6) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
      2*(replicaPublicationCost N s missing L w+6*N+6)) depth
      (restoringReplicaPublication clock clockSave padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved)
      (mk v S) n (mk v' F) := by
  exact mn_native_exec_within he 2 (restoringReplicaPublication_native _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
