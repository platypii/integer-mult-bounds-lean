module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUniformSweepControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPublicationSweepReady

/-! Build and release the two retained sweep words for consecutive cores.
All mathematical stride information is supplied by the generic origin identity. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
namespace PreparedPublicationPlan
variable {T Q K s L : ℕ} {src dst : Fin T} {P U : Type}

def uniformSweepState (plan : PreparedPublicationPlan T src dst) (N d : ℕ) (S : Stacks T (prime+K)) :=
  {S with R := (Function.update (Function.update S.R plan.count (List.replicate N tick)) plan.advances
    (gatherControls (prime+K) (List.replicate N d++[0])))}

private theorem sweep_fresh_off (plan : PreparedPublicationPlan T src dst) :
    ∀ i ∈ [plan.savedControl,plan.savedAdvances,plan.counter,plan.zero,plan.acc,plan.control,
      plan.trash,plan.tmp,plan.retireCount,plan.gap], i ≠ plan.count ∧ i ≠ plan.advances := by
  have hr := plan.hreg
  regs_ne hr
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor <;> first | assumption | (apply Ne.symm; assumption)

theorem uniformSweep_exec_within (body : P → Pr P T Q (prime+K) U)
    (plan : PreparedPublicationPlan T src dst) (rows packet : Fin T)
    (hreg : [rows,plan.count,packet,plan.advances,plan.savedAdvances,plan.savedControl].Nodup)
    (windows : PublicationWindows s L) (W depth : ℕ)
    (hstride : originAdvances W 0 windows.origins = List.replicate windows.origins.length (L*W))
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hrows : (S.R rows).length = windows.origins.length)
    (hpacket : S.R packet = List.replicate (L*W) tick)
    (hcount : S.R plan.count = []) (hadvances : S.R plan.advances = [])
    (hfresh : ∀ i ∈ [plan.savedControl,plan.savedAdvances,plan.counter,plan.zero,plan.acc,plan.control,
      plan.trash,plan.tmp,plan.retireCount,plan.gap], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ uniformSweepControlsCost windows.origins.length (L*W) ∧
      plan.SweepReady windows W [] (plan.uniformSweepState windows.origins.length (L*W) S) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        2*uniformSweepControlsCost windows.origins.length (L*W)) depth
        (uniformSweepControls rows plan.count packet plan.advances plan.savedAdvances plan.savedControl)
        (Host.mk v S) n (Host.mk v' (plan.uniformSweepState windows.origins.length (L*W) S)) := by
  obtain ⟨v',n,hu,hn,he⟩ := uniformSweepControls_exec_within body rows plan.count packet plan.advances
    plan.savedAdvances plan.savedControl hreg _ _ depth v S hrows hpacket hcount hadvances
    (hfresh _ (by simp)) (hfresh _ (by simp))
  refine ⟨v',n,hu,hn,?_,he⟩
  refine ⟨?_,?_,?_⟩
  · have hr := plan.hreg
    regs_ne hr
    simp [uniformSweepState,‹plan.count ≠ plan.advances›]
  · simp [uniformSweepState,hstride]
  · intro i hi
    simp only [uniformSweepState,Function.update_of_ne (sweep_fresh_off plan i hi).2,
      Function.update_of_ne (sweep_fresh_off plan i hi).1]
    exact hfresh i hi


end PreparedPublicationPlan
end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
