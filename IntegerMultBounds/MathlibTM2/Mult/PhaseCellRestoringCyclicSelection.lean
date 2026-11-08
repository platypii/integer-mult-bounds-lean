module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicSelectionReplicaLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedRecoveryPayload

/-! Restore the retained target bank and publish selected RHS rows in the
original replica order after one controller-reusing sweep. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
variable {T Q A s t : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def restoringCyclicSelection (clock volume queue archive outAcc dst control savedControl advance window src
    acc current savedSource buf tmp initialControl initialSource rowCount wordR : Fin T) : Pr P T Q A U :=
  .seq (countedLoop clock (cyclicSelectionReplicaStep volume queue archive outAcc dst control savedControl
    advance window src acc current savedSource buf tmp initialControl initialSource rowCount wordR))
    (.seq (moveR archive queue id) (moveR outAcc dst id))

def restoringCyclicSelectionCost (N n span w : ℕ) : ℕ :=
  N*(cyclicSelectionReplicaStepCost n span w+2*(span*w)+2*(n*w)+3)+6

theorem restoringCyclicSelection_native
    (clock volume queue archive outAcc dst control savedControl advance window src
      acc current savedSource buf tmp initialControl initialSource rowCount wordR : Fin T) :
    mnNativePushBound 2 (restoringCyclicSelection (P := P) (Q := Q) (A := A) (U := U)
      clock volume queue archive outAcc dst control savedControl advance window src acc current savedSource buf tmp
      initialControl initialSource rowCount wordR) := by
  simp only [restoringCyclicSelection,countedLoop,countedLoopBody,mnNativePushBound]
  refine ⟨⟨?_,?_,cyclicSelectionReplicaStep_native ..,?_⟩,?_,?_⟩
  all_goals simp [moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush]

theorem restoringCyclicSelection_exec
    (clock volume queue archive outAcc dst control savedControl advance window src
      acc current savedSource buf tmp initialControl initialSource rowCount wordR : Fin T)
    (hreg : [clock,volume,queue,archive,outAcc,dst,control,savedControl,advance,window,src,
      acc,current,savedSource,buf,tmp,initialControl,initialSource,rowCount,wordR].Nodup)
    (w a n origin span : ℕ) (Fs : List (ZMod t → GaussianInt)) (hn : 0 < n)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hclock : (S.R clock).length = Fs.length) (hvolume : (S.R volume).length = span*w)
    (hc : S.R control = localRowControls A s t a n origin w)
    (hqueue : S.R queue = (Fs.flatMap fun F => cstream A w (cyclicInterval origin span F))++tail)
    (hrow : (S.R rowCount).length = 1) (hw : (S.R wordR).length = w)
    (hclean : ∀ k ∈ [archive,outAcc,dst,src,savedControl,advance,window,acc,current,savedSource,buf,tmp,
      initialControl,initialSource], S.R k = []) :
    let output := selectedWindowPayload (s := s) A w a n origin span Fs
    ∃ v' m, v'.user = v.user ∧ m ≤ restoringCyclicSelectionCost Fs.length n span w ∧
      Exec body (restoringCyclicSelection clock volume queue archive outAcc dst control savedControl advance window src
        acc current savedSource buf tmp initialControl initialSource rowCount wordR) (Host.mk v S) m
        (Host.mk v' {S with R := Function.update (Function.update S.R clock []) dst output}) ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        2*restoringCyclicSelectionCost Fs.length n span w) depth
        (restoringCyclicSelection clock volume queue archive outAcc dst control savedControl advance window src
          acc current savedSource buf tmp initialControl initialSource rowCount wordR) (Host.mk v S) m
        (Host.mk v' {S with R := Function.update (Function.update S.R clock []) dst output}) := by
  dsimp only
  rw [selectedWindowPayload_cyclic A w a n origin span Fs hwindow]
  have hr := hreg
  regs_ne hr
  let input := Fs.flatMap fun F => cstream A w (cyclicInterval origin span F)
  let output := Fs.flatMap fun F => cstream A w (cyclicInterval a n (fun j => F (rowIndex s t j)))
  have hqueueInput : S.R queue = input++tail := hqueue
  have hinputLen : input.length = Fs.length*(span*w) := by
    simp [input,List.length_flatMap,length_cstream]
  have houtputLen : output.length = Fs.length*(n*w) := by
    simp [output,List.length_flatMap,length_cstream]
  obtain ⟨v₁,B,m₁,hu₁,hm₁,he₁,hq,ha,ho,hclock',hi,hout,hl,hframe⟩ :=
    cyclicSelectionReplicaLoop_exec (body := body) clock volume queue archive outAcc dst control savedControl
      advance window src acc current savedSource buf tmp initialControl initialSource rowCount wordR
      hreg w a n origin span Fs hn hwindow tail v S hclock hvolume hc hqueue hrow hw
      (by intro k hk; exact hclean k (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hk)))
  rw [hclean archive (by simp),List.append_nil] at ha
  rw [hclean outAcc (by simp),List.append_nil] at ho
  have hdst : B.R dst = [] := by
    rw [hframe dst ‹queue ≠ dst›.symm ‹archive ≠ dst›.symm ‹outAcc ≠ dst›.symm ‹clock ≠ dst›.symm]
    exact hclean dst (by simp)
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec (body := body) archive queue ‹queue ≠ archive›.symm id v₁ B
  let H : Stacks T A := {B with R := movedR B.R archive queue id input.reverse}
  have he₂' : Exec body (moveR archive queue id) (Host.mk v₁ B) (2*input.length+2) (Host.mk v₂ H) := by
    simpa only [ha,List.length_reverse,H] using he₂
  have houtAcc : H.R outAcc = output.reverse := by
    simpa only [H,movedR,Function.update_of_ne ‹archive ≠ outAcc›.symm,
      Function.update_of_ne ‹queue ≠ outAcc›.symm] using ho
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec (body := body) outAcc dst ‹outAcc ≠ dst› id v₂ H
  have hfinal : {H with R := movedR H.R outAcc dst id output.reverse} =
      {S with R := Function.update (Function.update S.R clock []) dst output} := by
    refine Stacks.ext hi hout hl ?_
    funext k
    by_cases hkd : k = dst
    · subst k
      simp [H,movedR,hdst,‹queue ≠ dst›.symm,‹archive ≠ dst›.symm]
    by_cases hka : k = archive
    · subst k
      simp [H,movedR,hkd,‹archive ≠ outAcc›,‹queue ≠ archive›.symm,‹clock ≠ archive›.symm,hclean archive (by simp)]
    by_cases hko : k = outAcc
    · subst k
      simp [H,movedR,hkd,‹clock ≠ outAcc›.symm,hclean outAcc (by simp)]
    by_cases hkq : k = queue
    · subst k
      simp [H,movedR,hkd,‹queue ≠ outAcc›,‹clock ≠ queue›.symm,hq,hqueueInput,List.map_id]
    by_cases hkc : k = clock
    · subst k
      simp [H,movedR,hkd,‹clock ≠ outAcc›,‹clock ≠ archive›,‹clock ≠ queue›,hclock']
    simp only [H,movedR,Function.update_of_ne hkd,Function.update_of_ne hko,
      Function.update_of_ne hka,Function.update_of_ne hkq,Function.update_of_ne hkc]
    exact hframe k hkq hka hko hkc
  rw [houtAcc,hfinal] at he₃
  have hm : m₁+((2*input.length+2)+(2*output.reverse.length+2)) ≤
      restoringCyclicSelectionCost Fs.length n span w := by
    simp only [List.length_reverse,hinputLen,houtputLen]
    unfold restoringCyclicSelectionCost
    nlinarith
  have hex := Exec.seq he₁ (Exec.seq he₂' he₃)
  refine ⟨v₃,_,hu₃.trans (hu₂.trans hu₁),hm,hex,fun depth => ?_⟩
  exact mn_native_exec_within hex 2 (restoringCyclicSelection_native ..) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
