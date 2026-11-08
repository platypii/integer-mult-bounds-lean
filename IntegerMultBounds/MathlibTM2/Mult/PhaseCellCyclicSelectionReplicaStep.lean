module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRowSelection
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalRowControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOrderedGatherStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefixStock

/-! Replay one prepared nearest-row controller on the next retained target
window. Archive the restored window and selected output in reverse so a final
pair of moves restores source order for the whole replica batch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
variable {T Q A s t : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def cyclicSelectionReplicaStep (volume queue archive outAcc dst control savedControl advance window src
    acc current savedSource buf tmp initialControl initialSource rowCount wordR : Fin T) : Pr P T Q A U :=
  .seq (takePrefix volume queue src buf tmp)
    (.seq (naturalGather dst control savedControl advance window src acc current savedSource buf tmp
      initialControl initialSource rowCount wordR)
      (.seq (moveR src archive id) (moveR dst outAcc id)))

def cyclicSelectionReplicaStepCost (n span w : ℕ) : ℕ :=
  (n*(14*w+25)+12*(span*w)+6*w+38)+(8*(span*w)+2*(n*w)+10)

theorem cyclicSelectionReplicaStep_native
    (volume queue archive outAcc dst control savedControl advance window src
      acc current savedSource buf tmp initialControl initialSource rowCount wordR : Fin T) :
    mnNativePushBound 2 (cyclicSelectionReplicaStep (P := P) (Q := Q) (A := A) (U := U)
      volume queue archive outAcc dst control savedControl advance window src acc current savedSource buf tmp
      initialControl initialSource rowCount wordR) := by
  simp only [cyclicSelectionReplicaStep,mnNativePushBound]
  exact ⟨takePrefix_native ..,naturalGather_native ..,by
    simp [moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush],by
    simp [moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush]⟩

private theorem archiveSelection_finish (queue archive outAcc dst src : Fin T)
    (hreg : [queue,archive,outAcc,dst,src].Nodup) (R : Regs T A)
    (input output tail : List (Fin (A+4))) (hsrc : R src = []) (hdst : R dst = []) :
    let H := Function.update (Function.update R queue tail) src input
    let K := Function.update H dst output
    let M := movedR K src archive id input
    movedR M dst outAcc id output = Function.update (Function.update (Function.update R queue tail)
      archive (input.reverse++R archive)) outAcc (output.reverse++R outAcc) := by
  dsimp only
  have hr := hreg
  regs_ne hr
  funext k
  simp only [movedR,Function.update_apply,List.map_id]
  split_ifs <;> simp_all

theorem cyclicSelectionReplicaStep_exec
    (volume queue archive outAcc dst control savedControl advance window src
      acc current savedSource buf tmp initialControl initialSource rowCount wordR : Fin T)
    (hreg : [volume,queue,archive,outAcc,dst,control,savedControl,advance,window,src,
      acc,current,savedSource,buf,tmp,initialControl,initialSource,rowCount,wordR].Nodup)
    (w a n origin span : ℕ) (F : ZMod t → GaussianInt) (hn : 0 < n)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hvolume : (S.R volume).length = span*w)
    (hc : S.R control = localRowControls A s t a n origin w)
    (hqueue : S.R queue = cstream A w (cyclicInterval origin span F)++tail)
    (hrow : (S.R rowCount).length = 1) (hw : (S.R wordR).length = w)
    (hclean : ∀ k ∈ [dst,src,savedControl,advance,window,acc,current,savedSource,buf,tmp,
      initialControl,initialSource], S.R k = []) :
    let input := cstream A w (cyclicInterval origin span F)
    let output := cstream A w (cyclicInterval a n (fun j => F (rowIndex s t j)))
    ∃ v' m, v'.user = v.user ∧ m ≤ cyclicSelectionReplicaStepCost n span w ∧
      Exec body (cyclicSelectionReplicaStep volume queue archive outAcc dst control savedControl advance window src
        acc current savedSource buf tmp initialControl initialSource rowCount wordR) (Host.mk v S) m
        (Host.mk v' {S with R := (Function.update (Function.update (Function.update S.R queue tail)
          archive (input.reverse++S.R archive)) outAcc (output.reverse++S.R outAcc))}) := by
  dsimp only
  have hr := hreg
  regs_ne hr
  let input := cstream A w (cyclicInterval origin span F)
  let output := cstream A w (cyclicInterval a n (fun j => F (rowIndex s t j)))
  have hinputLen : input.length = span*w := by simp [input,length_cstream]
  have houtputLen : output.length = n*w := by simp [output,length_cstream]
  obtain ⟨v₁,hu₁,he₁⟩ := takePrefix_exec (body := body)
    (by regs_nodup : [volume,queue,src,buf,tmp].Nodup) v S input tail hqueue
    (by omega) (hclean buf (by simp)) (hclean tmp (by simp))
  rw [hclean src (by simp),List.append_nil] at he₁
  let H : Stacks T A := {S with R := (Function.update (Function.update S.R queue tail) src input)}
  have hoff (k : Fin T) (hkq : k ≠ queue) (hks : k ≠ src) : H.R k = S.R k := by
    simp [H,hkq,hks]
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := cyclicRowSelection_exec (body := body)
    dst control savedControl advance window src acc current savedSource buf tmp
    initialControl initialSource rowCount wordR hreg.tail.tail.tail.tail w a n origin span F hn hwindow v₁ H
    (by rw [hoff control ‹queue ≠ control›.symm ‹control ≠ src›]; exact hc)
    (by simp [H,input])
    (by rw [hoff rowCount ‹queue ≠ rowCount›.symm ‹src ≠ rowCount›.symm]; exact hrow)
    (by rw [hoff wordR ‹queue ≠ wordR›.symm ‹src ≠ wordR›.symm]; exact hw)
    (by
      intro k hk
      have hne : k ≠ queue ∧ k ≠ src := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          constructor <;> first | assumption | (apply Ne.symm; assumption)
      rw [hoff k hne.1 hne.2]
      exact hclean k (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hk)))
  have hdst : H.R dst = [] := by rw [hoff dst ‹queue ≠ dst›.symm ‹dst ≠ src›]; exact hclean dst (by simp)
  rw [hdst,List.append_nil] at he₂
  let K : Stacks T A := {H with R := Function.update H.R dst output}
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec (body := body) src archive ‹archive ≠ src›.symm id v₂ K
  have hsrcK : K.R src = input := by simp [K,H,‹dst ≠ src›.symm]
  let M : Stacks T A := {K with R := movedR K.R src archive id input}
  have he₃' : Exec body (moveR src archive id) (Host.mk v₂ K) (2*input.length+2) (Host.mk v₃ M) := by
    simpa only [hsrcK,M] using he₃
  have hdstM : M.R dst = output := by simp [M,movedR,K,‹dst ≠ src›,‹archive ≠ dst›.symm]
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec (body := body) dst outAcc ‹outAcc ≠ dst›.symm id v₃ M
  have hfinal : {M with R := movedR M.R dst outAcc id output} =
      {S with R := (Function.update (Function.update (Function.update S.R queue tail)
        archive (input.reverse++S.R archive)) outAcc (output.reverse++S.R outAcc))} := by
    refine Stacks.ext rfl rfl rfl ?_
    exact archiveSelection_finish queue archive outAcc dst src (by regs_nodup) S.R input output tail
      (hclean src (by simp)) (hclean dst (by simp))
  rw [hdstM,hfinal] at he₄
  refine ⟨v₄,_,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃' he₄))⟩
  unfold cyclicSelectionReplicaStepCost
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
