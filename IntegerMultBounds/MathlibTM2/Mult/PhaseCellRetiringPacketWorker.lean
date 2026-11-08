module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMovePrefix
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! A restoring packet operation becomes a consuming batch worker by loading
one packet and retiring its restored input after publishing equal-length output. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def retiringPacketWorker (count queue input saved tmp : Fin T) (run : Pr P T Q A U) : Pr P T Q A U :=
  .seq (movePrefix count queue input saved tmp) (.seq run (uclear input))

theorem movePrefix_native (count queue input saved tmp : Fin T) :
    mnNativePushBound 2 (movePrefix (P₀ := P) (Q := Q) (A := A) (U := U) count queue input saved tmp) := by
  simp [movePrefix,transfer,transferAct,moveR,moveStep,scanR,drainR,popDo,
    keepIn,whileR,peekR,mnNativePushBound,mnActPush]

/-- Consuming and publishing the same volume preserves boundary stock even
when the input and output words differ. -/
theorem packet_replace_preserves_size (queue out : Fin T) (hne : out ≠ queue)
    (payload result tail : List (Fin (A+4))) (hlen : result.length = payload.length)
    (v v' : HS T Q A U) (S : Stacks T A) (hqueue : S.R queue = payload++tail) :
    mnSize (Host.mk v' {S with R := (Function.update (Function.update S.R queue tail)
      out (result++S.R out))}) = mnSize (Host.mk v S) := by
  let F : Stacks T A := {S with R := Function.update S.R queue tail}
  have ha := mn_size_update (Host.mk v S) v (.rt queue) tail
  have hb := mn_size_update (Host.mk v F) v' (.rt out) (result++S.R out)
  have ha' : mnSize (Host.mk v F)+(S.R queue).length = mnSize (Host.mk v S)+tail.length := by
    simpa only [F,Host.mk,update_rt,get_rt] using ha
  have hb' : mnSize (Host.mk v' {S with R := (Function.update (Function.update S.R queue tail)
      out (result++S.R out))})+(S.R out).length = mnSize (Host.mk v F)+(result++S.R out).length := by
    simpa only [F,Host.mk,update_rt,get_rt,Function.update_of_ne hne] using hb
  rw [hqueue,List.length_append] at ha'
  rw [List.length_append,hlen] at hb'
  omega

theorem retiringPacketWorker_exec (count queue input out saved tmp : Fin T)
    (hreg : [count,queue,input,out,saved,tmp].Nodup)
    (run : Pr P T Q A U) (payload result tail : List (Fin (A+4)))
    (hlen : result.length = payload.length) (cost reserve : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hqueue : S.R queue = payload++tail) (hcount : (S.R count).length = payload.length)
    (hinput : S.R input = []) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hrun : ∀ v₁ : HS T Q A U,
      let F : Stacks T A := {S with R := (Function.update (Function.update S.R queue tail) input payload)}
      ∃ v₂ n, v₂.user = v₁.user ∧ n ≤ cost ∧
        Exec body run (Host.mk v₁ F) n
          (Host.mk v₂ {F with R := Function.update F.R out (result++S.R out)}) ∧
        ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v₁ F)+depth+reserve)
          depth run (Host.mk v₁ F) n (Host.mk v₂ {F with R := Function.update F.R out (result++S.R out)})) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (6*payload.length+6)+cost+(2*payload.length+2) ∧
      Exec body (retiringPacketWorker count queue input saved tmp run) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R queue tail) out (result++S.R out))}) ∧
      (∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        (2*(6*payload.length+6)+reserve)) depth
        (retiringPacketWorker count queue input saved tmp run) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R queue tail) out (result++S.R out))})) ∧
      mnSize (Host.mk v' {S with R := (Function.update (Function.update S.R queue tail) out (result++S.R out))}) =
        mnSize (Host.mk v S) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := movePrefix_exec (body := body)
    (by regs_nodup : [count,queue,input,saved,tmp].Nodup) payload tail v S hqueue hcount hsaved htmp
  let F : Stacks T A := {S with R := Function.update (Function.update S.R queue tail) input payload}
  have he₁' : Exec body (movePrefix count queue input saved tmp) (Host.mk v S) (6*payload.length+6)
      (Host.mk v₁ F) := by simpa only [hinput,List.append_nil,F] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,htrace₂⟩ := hrun v₁
  let G : Stacks T A := {F with R := Function.update F.R out (result++S.R out)}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) input v₂ G
  have hlenInput : (G.R input).length = payload.length := by simp [G,F,‹input ≠ out›]
  have hfinal : {G with R := Function.update G.R input []} =
      {S with R := Function.update (Function.update S.R queue tail) out (result++S.R out)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = input
    · subst i; simp [‹queue ≠ input›.symm,‹input ≠ out›,hinput]
    · simp [G,F,Function.update_apply,hi]
  rw [hlenInput,hfinal] at he₃
  refine ⟨v₃,(6*payload.length+6)+(n₂+(2*payload.length+2)),hu₃.trans (hu₂.trans hu₁),by omega,
    Exec.seq he₁' (Exec.seq he₂ he₃),?_,?_⟩
  · intro depth
    have ht₁ := mn_native_exec_within he₁' 2 (movePrefix_native ..) depth (mnSize (Host.mk v S)+depth+2*(6*payload.length+6)) (by omega)
    have hc : mnNativePushBound 0 (uclear (P := P) (Q := Q) (A := A) (U := U) input) := by
      simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]
    have ht₃ := mn_native_exec_within he₃ 0 hc depth (mnSize (Host.mk v₂ G)+depth) (by omega)
    have ht₃' : ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v₂ G)+depth+0) depth
        (uclear input) (Host.mk v₂ G) (2*payload.length+2)
        (Host.mk v₃ {S with R := Function.update (Function.update S.R queue tail) out (result++S.R out)}) :=
      ht₃
    have ht := mn_seq_within_add ht₁ (mn_seq_within_add (htrace₂ depth) ht₃')
    simpa only [retiringPacketWorker,Nat.zero_mul,Nat.add_zero] using ht
  · exact packet_replace_preserves_size queue out ‹queue ≠ out›.symm payload result tail hlen v v₃ S hqueue

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
