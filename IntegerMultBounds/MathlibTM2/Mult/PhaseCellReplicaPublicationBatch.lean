module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationLoop

/-! Complete replica publication restores forward line order with one final
move. All borrowed suffixes and private accumulator registers are restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement
variable {T Q A s L : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem replicaPublicationBatch_exec
    (clock padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved : Fin T)
    (hreg : [clock,padRows,wordWidth,retireCount,control,savedControl,gap,window,src,dst,acc,trash,tmp,lineRows,outAcc,saved].Nodup)
    (windows : PublicationWindows s L) (w missing : ℕ) (hw1 : 1 ≤ w)
    (replicas : List (PublicationReplica A))
    (hvalid : ∀ r ∈ replicas, r.Valid windows w missing)
    (sourceTail outputTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = replicas.flatMap (PublicationReplica.input w)++sourceTail)
    (hdst : S.R dst = replicas.flatMap PublicationReplica.ambient++outputTail)
    (hclock : (S.R clock).length = replicas.length)
    (hpadRows : (S.R padRows).length = missing*L) (hwidth : (S.R wordWidth).length = w)
    (hlineRows : (S.R lineRows).length = s)
    (hc : S.R control = gatherControls A (windows.gaps w)) (hw : (S.R window).length = L*w)
    (hclean : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,tmp,saved], S.R i = [])
    (houtAcc : S.R outAcc = []) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ replicas.length*(replicaPublicationStepCost s missing L w+3)+2+
        (2*(replicas.length*(s*w))+2) ∧
      Exec body (.seq (countedLoop clock (replicaPublicationStep padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved))
        (moveR outAcc dst id))
        (mk v S) n (mk v' F) ∧
      F.R src = sourceTail ∧
      F.R dst = replicas.flatMap (PublicationReplica.output windows w)++outputTail ∧
      F.R outAcc = [] ∧
      F.R clock = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ src → i ≠ dst → i ≠ clock → F.R i = S.R i := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,F,n₁,hu₁,hn₁,he₁,hs,hd,ha,hclock',hi,ho,hl,hframe⟩ := replicaPublicationLoop_exec (body := body)
    clock padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved
    hreg windows w missing hw1 replicas hvalid sourceTail outputTail
    v S hsrc hdst hclock hpadRows hwidth hlineRows hc hw hclean
  let output := PublicationReplica.output (A := A) windows w
  have hlen : (replicas.flatMap output).length = replicas.length*(s*w) := by
    simp only [List.length_flatMap]
    have hm : replicas.map (fun r => (output r).length) = replicas.map (fun _ => s*w) :=
      List.map_congr_left (fun r hr => (hvalid r hr).output_length)
    rw [hm]
    simp
  have hacc : F.R outAcc = (replicas.flatMap output).reverse := by
    simpa only [houtAcc,List.append_nil] using ha
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body outAcc dst ‹dst ≠ outAcc›.symm id v₁ F
  let G : Stacks T A := {F with R := movedR F.R outAcc dst id (F.R outAcc)}
  have hlenAcc : (F.R outAcc).length = replicas.length*(s*w) := by rw [hacc,List.length_reverse,hlen]
  have hstep : Exec body (moveR outAcc dst id) (mk v₁ F)
      (2*(replicas.length*(s*w))+2) (mk v₂ G) := by simpa only [hlenAcc] using he₂
  have hblankAcc : G.R outAcc = [] := by simp [G,movedR,‹dst ≠ outAcc›.symm]
  refine ⟨v₂,G,n₁+(2*(replicas.length*(s*w))+2),hu₂.trans hu₁,
    Nat.add_le_add_right hn₁ _,Exec.seq he₁ hstep,?_,?_,hblankAcc,?_,hi,ho,hl,?_⟩
  · simpa [G,movedR,‹src ≠ outAcc›,‹src ≠ dst›] using hs
  · simp [G,movedR,hacc,hd,output]
  · simpa [G,movedR,‹clock ≠ outAcc›,‹clock ≠ dst›] using hclock'
  · intro i his hid hic
    by_cases hia : i = outAcc
    · subst i; exact hblankAcc.trans houtAcc.symm
    · simpa [G,movedR,hia,hid] using hframe i his hid hia hic

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
