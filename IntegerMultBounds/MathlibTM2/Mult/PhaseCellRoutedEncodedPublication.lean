module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSymbolEncodedPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReversePackedLines

/-! Align a forward ambient bank with reverse-order compact solver output and
publish it in one native execution. Both borrowed source suffixes survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s L : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def routedEncodedPublication
    (clock control savedControl gap window src ambientSrc dst acc trash tmp volume outAcc : Fin T) : Pr P T Q A U :=
  .seq (retainedReversePackedLines clock trash volume ambientSrc dst outAcc tmp)
    (symbolEncodedPublication clock control savedControl gap window src dst acc trash tmp volume outAcc)

def routedEncodedPublicationCost (N V : ℕ) :=
  (N*(6*V+13)+6)+symbolEncodedPublicationCost N V

theorem routedEncodedPublication_exec_within
    (clock control savedControl gap window src ambientSrc dst acc trash tmp volume outAcc : Fin T)
    (hreg : [clock,control,savedControl,gap,window,src,ambientSrc,dst,acc,trash,tmp,volume,outAcc].Nodup)
    (windows : PublicationWindows s L) {w q e : ℕ} (hw1 : 1 ≤ w)
    (xs : BoundedEncodedStream A w q e) (ambientRows : List (List (Fin (A+4))))
    (hambient : ∀ ys ∈ ambientRows, ys.length = s*w)
    (hlen : xs.val.length = ambientRows.length*(windows.origins.length*L)*w)
    (sourceTail ambientTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = xs.val++sourceTail) (hambientSrc : S.R ambientSrc = ambientRows.flatten++ambientTail)
    (hdst : S.R dst = []) (hclock : (S.R clock).length = ambientRows.length)
    (hvolume : (S.R volume).length = s*w)
    (hc : S.R control = gatherControls A (windows.gaps w)) (hwindow : (S.R window).length = L*w)
    (hclean : ∀ i ∈ [savedControl,gap,acc,trash,tmp,outAcc], S.R i = []) (depth : ℕ) :
    ∃ v' F n, ∃ replicas : List (PublicationReplica A),
      replicas.map PublicationReplica.ambient = ambientRows.reverse ∧
      replicas.flatMap (PublicationReplica.input w) = xs.val ∧
      (∀ r ∈ replicas, r.Valid windows w 0) ∧ v'.user = v.user ∧
      n ≤ routedEncodedPublicationCost ambientRows.length (s*w) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*routedEncodedPublicationCost ambientRows.length (s*w)) depth
        (routedEncodedPublication clock control savedControl gap window src ambientSrc dst acc trash tmp volume outAcc)
        (mk v S) n (mk v' F) ∧
      F.R src = sourceTail ∧ F.R ambientSrc = ambientTail ∧
      F.R dst = replicas.flatMap (PublicationReplica.output windows w) ∧ F.R clock = [] ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ src → i ≠ ambientSrc → i ≠ dst → i ≠ clock → F.R i = S.R i := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,M,n₁,hu₁,hn₁,he₁,hs₁,hd₁,hi₁,ho₁,hl₁,hframe₁⟩ :=
    retainedReversePackedLines_exec (body := body) clock trash volume ambientSrc dst outAcc tmp
      (by regs_nodup) ambientRows (s*w) hambient ambientTail v S hclock hvolume hambientSrc
      (hclean _ (by simp)) (hclean _ (by simp)) (hclean _ (by simp))
  have hkeep (i : Fin T) (his : i ≠ ambientSrc) (hid : i ≠ dst) : M.R i = S.R i := hframe₁ i his hid
  have hstable : ∀ i ∈ [clock,control,savedControl,gap,window,src,acc,trash,tmp,volume,outAcc], M.R i = S.R i := by
    intro i hi
    apply hkeep
    all_goals
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | assumption | (apply Ne.symm; assumption)
  obtain ⟨v₂,F,n₂,replicas,ha,hinput,hvalid,hu₂,hn₂,he₂,hs₂,hd₂,hout,hclock',hi₂,ho₂,hl₂,hframe₂⟩ :=
    symbolEncodedPublication_exec_within (body := body)
      clock control savedControl gap window src dst acc trash tmp volume outAcc (by regs_nodup)
      windows hw1 xs ambientRows.reverse (by simpa using hambient) (by simpa using hlen)
      sourceTail [] v₁ M
      (by rw [hstable _ (by simp)]; exact hsrc)
      (by simpa only [hdst,List.append_nil] using hd₁)
      (by rw [hstable _ (by simp)]; simpa using hclock)
      (by rw [hstable _ (by simp)]; exact hvolume)
      (by rw [hstable _ (by simp)]; exact hc)
      (by rw [hstable _ (by simp)]; exact hwindow)
      (by
        intro i hi
        have hm : i ∈ [clock,control,savedControl,gap,window,src,acc,trash,tmp,volume,outAcc] := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
          rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp
        rw [hstable i hm]
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact hclean _ (by simp))
      (by rw [hstable _ (by simp)]; exact hclean _ (by simp)) depth
  have hn : n₁+n₂ ≤ routedEncodedPublicationCost ambientRows.length (s*w) := by
    dsimp only [routedEncodedPublicationCost]
    simpa only [List.length_reverse] using Nat.add_le_add hn₁ hn₂
  have hex := Exec.seq he₁ he₂.toExec
  have hpush : mnNativePushBound 2
      (routedEncodedPublication (P := P) (Q := Q) (A := A) (U := U)
        clock control savedControl gap window src ambientSrc dst acc trash tmp volume outAcc) :=
    ⟨retainedReversePackedLines_pushBound _ _ _ _ _ _ _,symbolEncodedPublication_pushBound _ _ _ _ _ _ _ _ _ _ _ _⟩
  refine ⟨v₂,F,n₁+n₂,replicas,ha,hinput,hvalid,hu₂.trans hu₁,hn,
    mn_native_exec_within hex 2 hpush depth _ (by omega),hs₂,?_,by simpa using hd₂,hclock',
    hi₂.trans hi₁,ho₂.trans ho₁,hl₂.trans hl₁,?_⟩
  · exact (hframe₂ ambientSrc ‹src ≠ ambientSrc›.symm ‹ambientSrc ≠ dst› ‹clock ≠ ambientSrc›.symm).trans hs₁
  · intro i his hia hid hic
    exact (hframe₂ i his hid hic).trans (hkeep i hia hid)

theorem routedEncodedPublicationCost_le (N V : ℕ) (hV : 1 ≤ V) :
    routedEncodedPublicationCost N V ≤ 73*N*V+10 := by
  have hh := Nat.mul_le_mul_left N (show 47*V+26 ≤ 73*V by omega)
  dsimp only [routedEncodedPublicationCost,symbolEncodedPublicationCost]
  nlinarith only [hh]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
