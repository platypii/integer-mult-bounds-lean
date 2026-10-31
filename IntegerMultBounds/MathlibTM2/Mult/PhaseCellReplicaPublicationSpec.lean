module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationAccuracy

/-! Complete replica publication restores forward line order with one final
move. All borrowed suffixes and private accumulator registers are restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A s L : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem replicaPublicationBatch_accuracy_exec
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
    (houtAcc : S.R outAcc = [])
    (q : ℕ) (target : ℕ → ZMod s → ℂ) (error : ℝ)
    (hgood : ∀ j (hj : j < replicas.length) n (hn : n < windows.origins.length),
      PhaseCellInterface.ErrorOn (haloVertices s windows.origins[n] (windows.origins[n]+L))
        (packedIntervalRead q w windows.origins[n]
          (cstream A w (replicas[j].rows[n]'(by rw [(hvalid _ (List.getElem_mem hj)).rowCount]; exact hn))))
        (target j) error) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ replicas.length*(replicaPublicationStepCost s missing L w+3)+2+
        (2*(replicas.length*(s*w))+2) ∧
      Exec body (.seq (countedLoop clock (replicaPublicationStep padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved))
        (moveR outAcc dst id))
        (mk v S) n (mk v' F) ∧
      F.R src = sourceTail ∧
      F.R dst = replicas.flatMap (PublicationReplica.output windows w)++outputTail ∧
      F.R outAcc = [] ∧
      F.R clock = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ i, i ≠ src → i ≠ dst → i ≠ clock → F.R i = S.R i) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+
        2*replicaPublicationCost replicas.length s missing L w) 0
        (.seq (countedLoop clock (replicaPublicationStep padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved))
          (moveR outAcc dst id)) (mk v S) n (mk v' F) ∧
      ∀ j (hj : j < replicas.length) n (hn : n < windows.origins.length),
        PhaseCellInterface.ErrorOn (haloVertices s windows.origins[n] (windows.origins[n]+L))
          (pairedCellRead q w ((F.R dst).drop (j*(s*w)))) (target j) error := by
  obtain ⟨v',F,n,hu,hn,he,hs,hd,ha,hclock',hi,ho,hl,hframe⟩ := replicaPublicationBatch_exec
    clock padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved
    hreg windows w missing hw1 replicas hvalid sourceTail outputTail v S hsrc hdst hclock
    hpadRows hwidth hlineRows hc hw hclean houtAcc
  refine ⟨v',F,n,hu,hn,he,hs,hd,ha,hclock',hi,ho,hl,hframe,?_,?_⟩
  · simpa only [Nat.add_zero] using replicaPublication_within_stock he hn 0
  · intro j hj k hk
    exact replicaPublication_errorOn windows q w missing replicas hvalid outputTail (F.R dst) hd
      j hj k hk (target j) error (hgood j hj k hk)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
