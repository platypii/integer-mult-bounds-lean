module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSymbolReplicaPublicationBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationFromEncoded
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Publish actual encoded solver output using the symbol-volume header already
retained by gathering. All per-replica movement is linear native traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s L : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def symbolEncodedPublication
    (clock control savedControl gap window src dst acc trash tmp volume outAcc : Fin T) : Pr P T Q A U :=
  .seq (countedLoop clock (symbolReplicaPublicationStep control savedControl gap window src dst acc trash tmp volume outAcc))
    (moveR outAcc dst id)

def symbolEncodedPublicationCost (N V : ℕ) := N*(41*V+13)+4

theorem symbolEncodedPublication_pushBound
    (clock control savedControl gap window src dst acc trash tmp volume outAcc : Fin T) :
    mnNativePushBound 2 (symbolEncodedPublication (P := P) (Q := Q) (A := A) (U := U)
      clock control savedControl gap window src dst acc trash tmp volume outAcc) := by
  simp [symbolEncodedPublication,symbolReplicaPublicationStep,countedLoop,countedLoopBody,
    scatterBatch,scatterLoopBody,scatterPacket,gatherRead,gatherReadStep,WordCmd.peekRp,
    discardPrefix,transfer,moveR,uclear,keepIn,scanR,transferAct,drainR,popDo,whileR,
    moveStep,peekR,popPush,mnNativePushBound,mnActPush]

theorem symbolEncodedPublication_exec_within
    (clock control savedControl gap window src dst acc trash tmp volume outAcc : Fin T)
    (hreg : [clock,control,savedControl,gap,window,src,dst,acc,trash,tmp,volume,outAcc].Nodup)
    (windows : PublicationWindows s L) {w q e : ℕ} (hw1 : 1 ≤ w)
    (xs : BoundedEncodedStream A w q e) (ambientRows : List (List (Fin (A+4))))
    (hambient : ∀ ys ∈ ambientRows, ys.length = s*w)
    (hlen : xs.val.length = ambientRows.length*(windows.origins.length*L)*w)
    (sourceTail outputTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = xs.val++sourceTail) (hdst : S.R dst = ambientRows.flatten++outputTail)
    (hclock : (S.R clock).length = ambientRows.length) (hvolume : (S.R volume).length = s*w)
    (hc : S.R control = gatherControls A (windows.gaps w)) (hwindow : (S.R window).length = L*w)
    (hclean : ∀ i ∈ [savedControl,gap,acc,trash,tmp], S.R i = []) (houtAcc : S.R outAcc = []) (depth : ℕ) :
    ∃ v' F n, ∃ replicas : List (PublicationReplica A), replicas.map PublicationReplica.ambient = ambientRows ∧
      replicas.flatMap (PublicationReplica.input w) = xs.val ∧
      (∀ r ∈ replicas, r.Valid windows w 0) ∧ v'.user = v.user ∧
      n ≤ symbolEncodedPublicationCost ambientRows.length (s*w) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*symbolEncodedPublicationCost ambientRows.length (s*w)) depth
        (symbolEncodedPublication clock control savedControl gap window src dst acc trash tmp volume outAcc)
        (mk v S) n (mk v' F) ∧
      F.R src = sourceTail ∧ F.R dst = replicas.flatMap (PublicationReplica.output windows w)++outputTail ∧
      F.R outAcc = [] ∧ F.R clock = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ src → i ≠ dst → i ≠ clock → F.R i = S.R i := by
  obtain ⟨replicas,hnrep,hambient',hinput,hvalid⟩ := publicationReplicas_of_encoded windows hw1 xs ambientRows hambient hlen
  have hflat : replicas.flatMap PublicationReplica.ambient = ambientRows.flatten := by rw [List.flatMap_def,hambient']
  obtain ⟨v',F,n,hu,hn,he,hrest⟩ := symbolReplicaPublicationBatch_exec (body := body)
    clock control savedControl gap window src dst acc trash tmp volume outAcc hreg windows w hw1 replicas hvalid
    sourceTail outputTail v S (by rw [hinput]; exact hsrc) (by rw [hflat]; exact hdst)
    (by rw [hnrep]; exact hclock) hvolume hc hwindow hclean houtAcc
  have hn' : n ≤ symbolEncodedPublicationCost ambientRows.length (s*w) := by
    simpa only [symbolEncodedPublicationCost,hnrep] using hn
  exact ⟨v',F,n,replicas,hambient',hinput,hvalid,hu,hn',
    mn_native_exec_within he 2 (symbolEncodedPublication_pushBound _ _ _ _ _ _ _ _ _ _ _ _) depth _ (by omega),hrest⟩

theorem symbolEncodedPublicationCost_le (N V : ℕ) (hV : 1 ≤ V) :
    symbolEncodedPublicationCost N V ≤ 54*N*V+4 := by
  have hh := Nat.mul_le_mul_left N (show 41*V+13 ≤ 54*V by omega)
  dsimp only [symbolEncodedPublicationCost]
  nlinarith only [hh]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
