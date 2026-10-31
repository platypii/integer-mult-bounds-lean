module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSymbolEncodedPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationPreserves

/-! Publish into an independent accumulated ambient bank in solver order.
Borrow and restore the replica counter so successive classes share metadata. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A span L : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def retainedEncodedPublication
    (clock savedCount control savedControl gap window src dst acc trash tmp volume outAcc : Fin T) : Pr P T Q A U :=
  .seq (copyR clock savedCount tmp id)
    (.seq (symbolEncodedPublication clock control savedControl gap window src dst acc trash tmp volume outAcc)
      (moveR savedCount clock id))

def retainedEncodedPublicationCost (N V : ℕ) :=
  (4*N+4)+(symbolEncodedPublicationCost N V+(2*N+2))

theorem retainedEncodedPublication_pushBound
    (clock savedCount control savedControl gap window src dst acc trash tmp volume outAcc : Fin T) :
    mnNativePushBound 2 (retainedEncodedPublication (P := P) (Q := Q) (A := A) (U := U)
      clock savedCount control savedControl gap window src dst acc trash tmp volume outAcc) := by
  change _ ∧ _ ∧ _
  refine ⟨?_,symbolEncodedPublication_pushBound _ _ _ _ _ _ _ _ _ _ _ _,?_⟩
  · simp [copyR,copyStep,moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush]
  · simp [moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush]

theorem retainedEncodedPublication_exec_within
    (clock savedCount control savedControl gap window src dst acc trash tmp volume outAcc : Fin T)
    (hreg : [clock,savedCount,control,savedControl,gap,window,src,dst,acc,trash,tmp,volume,outAcc].Nodup)
    (windows : PublicationWindows span L) {w q e : ℕ} (hw1 : 1 ≤ w)
    (xs : BoundedEncodedStream A w q e) (ambientRows : List (List (Fin (A+4))))
    (hambient : ∀ ys ∈ ambientRows, ys.length = span*w)
    (hlen : xs.val.length = ambientRows.length*(windows.origins.length*L)*w)
    (sourceTail outputTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = xs.val++sourceTail) (hdst : S.R dst = ambientRows.flatten++outputTail)
    (hclock : (S.R clock).length = ambientRows.length) (hvolume : (S.R volume).length = span*w)
    (hc : S.R control = gatherControls A (windows.gaps w)) (hwindow : (S.R window).length = L*w)
    (hclean : ∀ i ∈ [savedCount,savedControl,gap,acc,trash,tmp,outAcc], S.R i = []) (depth : ℕ) :
    ∃ v' F n, ∃ replicas : List (PublicationReplica A), replicas.map PublicationReplica.ambient = ambientRows ∧
      replicas.flatMap (PublicationReplica.input w) = xs.val ∧ (∀ r ∈ replicas, r.Valid windows w 0) ∧
      v'.user = v.user ∧ n ≤ retainedEncodedPublicationCost ambientRows.length (span*w) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*retainedEncodedPublicationCost ambientRows.length (span*w)) depth
        (retainedEncodedPublication clock savedCount control savedControl gap window src dst acc trash tmp volume outAcc)
        (mk v S) n (mk v' F) ∧
      F.R src = sourceTail ∧ F.R dst = replicas.flatMap (PublicationReplica.output windows w)++outputTail ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ i, i ≠ src → i ≠ dst → F.R i = S.R i) ∧
      ∀ {s origin : ℕ} [NeZero s], ∀ r : Fin ambientRows.length,
        ∀ (core : Finset (ZMod s)) (x : ZMod s → ℝ) (error : ℝ),
        (∀ k ∈ core, origin ≤ k.val ∧ k.val < origin+span) →
        (∀ k ∈ core, ∀ n : Fin windows.origins.length,
          k.val-origin+1 ≤ windows.origins[n.val]'n.isLt ∨
            (windows.origins[n.val]'n.isLt)+L ≤ k.val-origin) →
        PhaseCellInterface.ErrorOn core
          (fun k => (packedIntervalRead q w origin ((S.R dst).drop (r.val*span*w)) k).re) x error →
        PhaseCellInterface.ErrorOn core
          (fun k => (packedIntervalRead q w origin ((F.R dst).drop (r.val*span*w)) k).re) x error := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := copyR_exec (body := body) clock savedCount tmp
    ‹clock ≠ savedCount› ‹clock ≠ tmp› ‹savedCount ≠ tmp› id v S (hclean _ (by simp))
  let M : Stacks T A := {S with R := Function.update S.R savedCount (S.R clock).reverse}
  have he₁' : Exec body (copyR clock savedCount tmp id) (mk v S) (4*ambientRows.length+4) (mk v₁ M) := by
    simpa only [List.map_id,hclock,hclean savedCount (by simp),List.append_nil] using he₁
  have hoff (i : Fin T) (hi : i ≠ savedCount) : M.R i = S.R i := by simp [M,hi]
  have hstable : ∀ i ∈ [clock,control,savedControl,gap,window,src,dst,acc,trash,tmp,volume,outAcc], M.R i = S.R i := by
    intro i hi
    apply hoff
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | assumption | (apply Ne.symm; assumption)
  obtain ⟨v₂,F,n₂,replicas,ha,hinput,hvalid,hu₂,hn₂,he₂,hs₂,hd₂,hout₂,hclock₂,hi₂,ho₂,hl₂,hframe₂⟩ :=
    symbolEncodedPublication_exec_within (body := body)
      clock control savedControl gap window src dst acc trash tmp volume outAcc (by regs_nodup)
      windows hw1 xs ambientRows hambient hlen sourceTail outputTail v₁ M
      (by rw [hstable _ (by simp)]; exact hsrc) (by rw [hstable _ (by simp)]; exact hdst)
      (by rw [hstable _ (by simp)]; exact hclock) (by rw [hstable _ (by simp)]; exact hvolume)
      (by rw [hstable _ (by simp)]; exact hc) (by rw [hstable _ (by simp)]; exact hwindow)
      (by
        intro i hi
        have hm : i ∈ [clock,control,savedControl,gap,window,src,dst,acc,trash,tmp,volume,outAcc] := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
          rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp
        rw [hstable i hm]
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact hclean _ (by simp))
      (by rw [hstable _ (by simp)]; exact hclean _ (by simp)) depth
  have hsaved : F.R savedCount = (S.R clock).reverse := by
    rw [hframe₂ savedCount ‹savedCount ≠ src› ‹savedCount ≠ dst› ‹clock ≠ savedCount›.symm]
    simp [M]
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body savedCount clock ‹clock ≠ savedCount›.symm id v₂ F
  let G : Stacks T A := {F with R := movedR F.R savedCount clock id (F.R savedCount)}
  have hn₃ : (F.R savedCount).length = ambientRows.length := by rw [hsaved,List.length_reverse,hclock]
  have he₃' : Exec body (moveR savedCount clock id) (mk v₂ F) (2*ambientRows.length+2) (mk v₃ G) := by
    simpa only [hn₃] using he₃
  have hn : (4*ambientRows.length+4)+(n₂+(2*ambientRows.length+2)) ≤
      retainedEncodedPublicationCost ambientRows.length (span*w) := Nat.add_le_add_left (Nat.add_le_add_right hn₂ _) _
  have hex := Exec.seq he₁' (Exec.seq he₂.toExec he₃')
  refine ⟨v₃,G,_,replicas,ha,hinput,hvalid,hu₃.trans (hu₂.trans hu₁),hn,
    mn_native_exec_within hex 2 (retainedEncodedPublication_pushBound _ _ _ _ _ _ _ _ _ _ _ _ _) depth _ (by omega),
    ?_,?_,hi₂,ho₂,hl₂,?_,?_⟩
  · simpa [G,movedR,‹savedCount ≠ src›.symm,‹clock ≠ src›.symm] using hs₂
  · simpa [G,movedR,‹savedCount ≠ dst›.symm,‹clock ≠ dst›.symm] using hd₂
  · intro i his hid
    by_cases hic : i = clock
    · subst i; simp [G,movedR,hsaved,hclock₂]
    by_cases hisaved : i = savedCount
    · subst i; simp [G,movedR,‹clock ≠ savedCount›.symm,hclean savedCount (by simp)]
    simp only [G,movedR,Function.update_of_ne hic,Function.update_of_ne hisaved]
    exact (hframe₂ i his hid hic).trans (hoff i hisaved)
  · intro s origin _ r core x error hcore hoff hbefore
    have hnrep : replicas.length = ambientRows.length := by
      have hh := congrArg List.length ha
      simpa only [List.length_map] using hh
    let rr : Fin replicas.length := ⟨r.val,by rw [hnrep]; exact r.isLt⟩
    have hflat : replicas.flatMap PublicationReplica.ambient = ambientRows.flatten := by
      rw [List.flatMap_def,ha]
    have hb : PhaseCellInterface.ErrorOn core
        (fun k => (packedIntervalRead q w origin
          (((replicas.flatMap PublicationReplica.ambient)++outputTail).drop (rr.val*span*w)) k).re) x error := by
      simpa only [hflat,←hdst] using hbefore
    have he := publicationReplicas_preserves_errorOn windows q w replicas hvalid outputTail rr
      core x error hcore hoff hb
    have hdG : G.R dst = replicas.flatMap (PublicationReplica.output windows w)++outputTail := by
      simpa [G,movedR,‹savedCount ≠ dst›.symm,‹clock ≠ dst›.symm] using hd₂
    simpa only [hdG] using he

theorem retainedEncodedPublicationCost_le (N V : ℕ) :
    retainedEncodedPublicationCost N V ≤ 60*N*(V+1)+10 := by
  unfold retainedEncodedPublicationCost symbolEncodedPublicationCost
  nlinarith only [Nat.zero_le (N*V)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
