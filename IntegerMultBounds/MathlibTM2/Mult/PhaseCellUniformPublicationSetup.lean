module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUniformPublicationSweep
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOpsStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderFrameRetirement

/-! Build a canonical packet master and both uniform sweep words from ordinary
row/core/word dimensions. Release all three after a restoring consumer. -/
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

def uniformSetup (plan : PreparedPublicationPlan T src dst) (rows core word stride : Fin T) : Pr P T Q (prime+K) U :=
  .seq (unaryProduct core word stride plan.savedControl plan.tmp)
    (uniformSweepControls rows plan.count stride plan.advances plan.savedAdvances plan.savedControl)

def uniformSetupState (plan : PreparedPublicationPlan T src dst) (stride : Fin T) (N d : ℕ) (S : Stacks T (prime+K)) :=
  plan.uniformSweepState N d {S with R := Function.update S.R stride (List.replicate d tick)}

def uniformSetupCost (N L W : ℕ) := L*(4*W+9)+4+uniformSweepControlsCost N (L*W)

def uniformSetupHeaders (plan : PreparedPublicationPlan T src dst) (stride : Fin T) := [plan.count,plan.advances,stride]

theorem uniformSetupState_off (plan : PreparedPublicationPlan T src dst) (stride : Fin T) (N d : ℕ)
    (S : Stacks T (prime+K)) (i : Fin T) (hi : i ∉ plan.uniformSetupHeaders stride) :
    (plan.uniformSetupState stride N d S).R i = S.R i := by
  simp only [uniformSetupHeaders,List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
  simp only [uniformSetupState,uniformSweepState,Function.update_of_ne hi.2.1,Function.update_of_ne hi.1,
    Function.update_of_ne hi.2.2]

theorem uniformSetup_exec_within (body : P → Pr P T Q (prime+K) U)
    (plan : PreparedPublicationPlan T src dst) (rows core word stride : Fin T)
    (hreg : [rows,core,word,stride,plan.count,plan.advances,plan.savedAdvances,plan.savedControl,plan.tmp].Nodup)
    (hstrideOff : ∀ i ∈ plan.sweepSupport, i ≠ stride)
    (windows : PublicationWindows s L) (W depth : ℕ)
    (hstride : originAdvances W 0 windows.origins = List.replicate windows.origins.length (L*W))
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hrows : (S.R rows).length = windows.origins.length) (hcore : (S.R core).length = L) (hword : (S.R word).length = W)
    (hblank : ∀ i ∈ plan.uniformSetupHeaders stride, S.R i = [])
    (hfresh : ∀ i ∈ [plan.savedControl,plan.savedAdvances,plan.counter,plan.zero,plan.acc,plan.control,
      plan.trash,plan.tmp,plan.retireCount,plan.gap], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ uniformSetupCost windows.origins.length L W ∧
      plan.SweepReady windows W [] (plan.uniformSetupState stride windows.origins.length (L*W) S) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        2*uniformSetupCost windows.origins.length L W) depth (plan.uniformSetup rows core word stride)
        (Host.mk v S) n (Host.mk v' (plan.uniformSetupState stride windows.origins.length (L*W) S)) := by
  regs_ne hreg
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (show [core,word,stride,plan.savedControl,plan.tmp].Nodup by regs_nodup) v S
    (hfresh _ (by simp)) (hfresh _ (by simp))
  let M : Stacks T (prime+K) := {S with R := Function.update S.R stride (List.replicate (L*W) tick)}
  have he₁' : Exec body (unaryProduct core word stride plan.savedControl plan.tmp) (Host.mk v S) n₁ (Host.mk v₁ M) := by
    simpa only [hcore,hword,hblank stride (by simp [uniformSetupHeaders]),List.append_nil,M] using he₁
  have hn₁' : n₁ ≤ L*(4*W+9)+4 := by simpa only [hcore,hword] using hn₁
  have hw₁ := mn_native_exec_within he₁' 2 (unaryProduct_native ..) depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hn₁') _)
  have hread (i : Fin T) (hi : i ≠ stride) : M.R i = S.R i := Function.update_of_ne hi _ _
  obtain ⟨v',n₂,hu₂,hn₂,ready,he₂⟩ := uniformSweep_exec_within body plan rows stride
    (by regs_nodup) windows W depth hstride v₁ M
    (by rw [hread rows ‹rows ≠ stride›]; exact hrows) (by simp [M])
    (by rw [hread plan.count ‹stride ≠ plan.count›.symm]; exact hblank _ (by simp [uniformSetupHeaders]))
    (by rw [hread plan.advances ‹stride ≠ plan.advances›.symm]; exact hblank _ (by simp [uniformSetupHeaders]))
    (by intro i hi; rw [hread i (hstrideOff i (by simp only [sweepSupport,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; exact Or.inr (Or.inr hi)))]; exact hfresh i hi)
  refine ⟨v',n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁' hn₂,ready,?_⟩
  simpa only [uniformSetup,uniformSetupState,uniformSetupCost,M,Nat.mul_add] using mn_seq_within_add hw₁ he₂

theorem retireUniformSetup_exec_within (body : P → Pr P T Q (prime+K) U)
    (plan : PreparedPublicationPlan T src dst) (stride : Fin T) (N d : ℕ)
    (hoff : ∀ i ∈ plan.sweepSupport++[src,dst], i ≠ stride)
    (xs ys : List (Fin (prime+K+4))) (S : Stacks T (prime+K))
    (hblank : ∀ i ∈ plan.uniformSetupHeaders stride, S.R i = [])
    (v : HS T Q (prime+K) U) (depth : ℕ) :
    let M := plan.uniformSetupState stride N d S
    let F := {M with R := (Function.update (Function.update M.R src xs) dst ys)}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v F)+depth) depth
        (clearWords (plan.uniformSetupHeaders stride)) (Host.mk v F) (2*(N*d)+4*N+2*d+9)
        (Host.mk v' {S with R := (Function.update (Function.update S.R src xs) dst ys)}) := by
  have hr := plan.hreg
  regs_ne hr
  have hsCount : plan.count ≠ stride := hoff _ (by simp [sweepSupport])
  have hsAdvance : plan.advances ≠ stride := hoff _ (by simp [sweepSupport])
  have he := retireHeaderFrame_pair_exec body (plan.uniformSetupHeaders stride)
    (by simp [uniformSetupHeaders,‹plan.count ≠ plan.advances›,hsCount,hsAdvance]) S
    (plan.uniformSetupState stride N d S) rfl rfl rfl (uniformSetupState_off plan stride N d S) hblank
    src dst (by simp [uniformSetupHeaders,Ne.symm ‹plan.count ≠ src›,Ne.symm ‹plan.advances ≠ src›,hoff src (by simp)])
    (by simp [uniformSetupHeaders,Ne.symm ‹plan.count ≠ dst›,Ne.symm ‹plan.advances ≠ dst›,hoff dst (by simp)]) xs ys v depth
  have hcost : 2*((plan.uniformSetupHeaders stride).map (fun i => ((plan.uniformSetupState stride N d S).R i).length)).sum+
      2*(plan.uniformSetupHeaders stride).length+1 = 2*(N*d)+4*N+2*d+9 := by
    simp [uniformSetupHeaders,uniformSetupState,uniformSweepState,‹plan.count ≠ plan.advances›,
      hsCount,hsAdvance,hsCount.symm,hsAdvance.symm,length_gatherControls,List.sum_replicate]
    omega
  simpa only [hcost] using he

end PreparedPublicationPlan
end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
