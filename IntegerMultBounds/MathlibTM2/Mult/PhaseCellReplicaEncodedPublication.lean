module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationFromEncoded
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationStock

/-! Publish actual compact bounded solver output into packed replica lines,
reusing the structural scatter program and its linear native stock bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement
variable {T Q A s L : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def publishEncodedReplicas
    (clock padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved : Fin T) :
    Pr P T Q A U :=
  .seq (countedLoop clock (replicaPublicationStep padRows wordWidth retireCount control savedControl gap window
    src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id)

theorem publishEncodedReplicas_exec_within
    (clock padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved : Fin T)
    (hreg : [clock,padRows,wordWidth,retireCount,control,savedControl,gap,window,src,dst,acc,trash,tmp,lineRows,outAcc,saved].Nodup)
    (windows : PublicationWindows s L) {w q e : ℕ} (hw1 : 1 ≤ w)
    (xs : BoundedEncodedStream A w q e) (ambientRows : List (List (Fin (A+4))))
    (hambient : ∀ ys ∈ ambientRows, ys.length = s*w)
    (hlen : xs.val.length = ambientRows.length*(windows.origins.length*L)*w)
    (sourceTail outputTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = xs.val++sourceTail) (hdst : S.R dst = ambientRows.flatten++outputTail)
    (hclock : (S.R clock).length = ambientRows.length) (hpadRows : S.R padRows = [])
    (hwidth : (S.R wordWidth).length = w) (hlineRows : (S.R lineRows).length = s)
    (hc : S.R control = gatherControls A (windows.gaps w)) (hwindow : (S.R window).length = L*w)
    (hclean : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,tmp,saved], S.R i = [])
    (houtAcc : S.R outAcc = []) (depth : ℕ) :
    ∃ v' F n, ∃ replicas : List (PublicationReplica A), replicas.map PublicationReplica.ambient = ambientRows ∧
      replicas.flatMap (PublicationReplica.input w) = xs.val ∧
      (∀ r ∈ replicas, r.Valid windows w 0) ∧
      v'.user = v.user ∧ n ≤ replicaPublicationCost ambientRows.length s 0 L w ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*replicaPublicationCost ambientRows.length s 0 L w) depth
        (publishEncodedReplicas clock padRows wordWidth retireCount control savedControl gap window
          src dst acc trash tmp lineRows outAcc saved) (mk v S) n (mk v' F) ∧
      F.R src = sourceTail ∧ F.R dst = replicas.flatMap (PublicationReplica.output windows w)++outputTail ∧
      F.R outAcc = [] ∧ F.R clock = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ src → i ≠ dst → i ≠ clock → F.R i = S.R i := by
  obtain ⟨replicas,hnrep,hambient',hinput,hvalid⟩ := publicationReplicas_of_encoded windows hw1 xs ambientRows hambient hlen
  have hflat : replicas.flatMap PublicationReplica.ambient = ambientRows.flatten := by
    rw [List.flatMap_def,hambient']
  obtain ⟨v',F,n,hu,hn,he,hrest⟩ := replicaPublicationBatch_exec
    clock padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved
    hreg windows w 0 hw1 replicas hvalid sourceTail outputTail v S
    (by rw [hinput]; exact hsrc) (by rw [hflat]; exact hdst)
    (by rw [hnrep]; exact hclock) (by simp [hpadRows]) hwidth hlineRows hc hwindow hclean houtAcc
  have hn' : n ≤ replicaPublicationCost ambientRows.length s 0 L w := by
    simpa only [replicaPublicationCost,hnrep] using hn
  exact ⟨v',F,n,replicas,hambient',hinput,hvalid,hu,hn',replicaPublication_within_stock he hn' depth,hrest⟩

/-- Compact output has no discarded padding rows; publication is linear native traffic. -/
theorem replicaEncodedPublicationCost_le (N s L w : ℕ) (hs : 1 ≤ s) (hw : 1 ≤ w) :
    replicaPublicationCost N s 0 L w ≤ 87*N*s*w+4 := by
  have hc := replicaPublicationCost_le N s 0 L w hs hw
  calc
    _ ≤ N*(21*(0*L*w)+87*(s*w))+4 := hc
    _ = _ := by ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
