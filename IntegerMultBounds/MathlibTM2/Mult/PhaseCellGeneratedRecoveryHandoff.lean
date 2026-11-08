module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCroppedRecoveryReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedTakePrefix

/-! Recovery handoff from retained selection dimensions, with no supplied byte
counter. Counter generation and retirement preserve ordinary recovery readiness. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedRecoveryPlan
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem CroppedReady.generatedTakePrefix_exec {plan : ComputedRecoveryPlan T} {crop : RecoveryCropPlacement plan}
    {d : InverseMasterInput s} {r : RawRecoveryJob s} {N offset rows : ℕ}
    {wl : List (Fin (A+4))} {S : Stacks T A}
    (h : plan.CroppedReady crop d r N offset rows wl S)
    (rowCount symbols count source saved tmp : Fin T)
    (hreg : [plan.replicas,rowCount,plan.packet,symbols,count,source,plan.work 124,saved,tmp].Nodup)
    (hoff : ∀ k, plan.cropSupport crop k → source ≠ k)
    (payload tail : List (Fin (A+4))) (hlen : payload.length = N*(r.problem.span*r.W))
    (v : HS T Q A U) (hsrc : S.R source = payload++tail)
    (hrows : (S.R rowCount).length = r.problem.span)
    (hinput : S.R (plan.work 124) = []) (hblank : ∀ k ∈ [symbols,count,saved,tmp], S.R k = []) :
    let F := plan.inputState source payload tail S
    ∃ v' n, v'.user = v.user ∧ n ≤ generatedTakePrefixCost N r.problem.span r.W ∧
      plan.CroppedReady crop d r N offset rows wl F ∧
      mnSize (Host.mk v' F) = mnSize (Host.mk v S) ∧
      Exec body (generatedTakePrefix plan.replicas rowCount plan.packet symbols count source (plan.work 124) saved tmp)
        (Host.mk v S) n (Host.mk v' F) ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        2*generatedTakePrefixCost N r.problem.span r.W) depth
        (generatedTakePrefix plan.replicas rowCount plan.packet symbols count source (plan.work 124) saved tmp)
        (Host.mk v S) n (Host.mk v' F) := by
  dsimp only
  have hr := hreg
  regs_ne hr
  obtain ⟨v',n,hu,hn,he,ht⟩ := PhaseCellToeplitz.generatedTakePrefix_exec (body := body)
    plan.replicas rowCount plan.packet symbols count source (plan.work 124) saved tmp hreg
    N r.problem.span r.W payload tail hlen v S h.replicas hrows h.packet hsrc hblank
  rw [hinput,List.append_nil] at he ht
  have hready : plan.CroppedReady crop d r N offset rows wl (plan.inputState source payload tail S) := by
    apply h.of_frame
    · intro k hk
      simp only [inputState,Function.update_of_ne (cropSupport_ne_payload plan crop k hk),
        Function.update_of_ne (hoff k hk).symm]
    · intro i; rfl
  have hsize := movePrefix_preserves_size source (plan.work 124) ‹source ≠ plan.work 124›.symm
    payload tail v v' S hsrc
  rw [hinput,List.append_nil] at hsize
  exact ⟨v',n,hu,hn,hready,hsize,he,ht⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedRecoveryPlan
