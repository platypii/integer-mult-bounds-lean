module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedDyadicPublicationHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPublicationPlan

/-! Sweep controls are retained independently of generated packet/padding/clock
words. This is the ordinary pre-setup contract, with no virtual loaded state. -/
set_option autoImplicit false

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace PreparedPublicationPlan
variable {T Q K s L : ℕ} {src dst : Fin T}

def sweepSupport (plan : PreparedPublicationPlan T src dst) : List (Fin T) :=
  [plan.count,plan.advances,plan.savedControl,plan.savedAdvances,plan.counter,plan.zero,plan.acc,plan.control,
    plan.trash,plan.tmp,plan.retireCount,plan.gap]

theorem sweepSupport_off (plan : PreparedPublicationPlan T src dst) {i : Fin T}
    (hi : i ∈ plan.sweepSupport) : i ≠ src ∧ i ≠ dst := by
  apply plan.support_off
  simp only [sweepSupport,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [support]

structure SweepReady (plan : PreparedPublicationPlan T src dst) (windows : PublicationWindows s L)
    (w : ℕ) (borrowed : List (Fin (prime+K+4))) (S : Stacks T (prime+K)) : Prop where
  count : S.R plan.count = List.replicate windows.origins.length Node.tick
  advances : S.R plan.advances = gatherControls (prime+K) (originAdvances w 0 windows.origins++[0])++borrowed
  fresh : ∀ i ∈ [plan.savedControl,plan.savedAdvances,plan.counter,plan.zero,plan.acc,plan.control,
    plan.trash,plan.tmp,plan.retireCount,plan.gap], S.R i = []

theorem SweepReady.of_frame {plan : PreparedPublicationPlan T src dst} {windows : PublicationWindows s L}
    {w : ℕ} {borrowed : List (Fin (prime+K+4))} {S F : Stacks T (prime+K)}
    (h : plan.SweepReady windows w borrowed S)
    (hR : ∀ i ∈ plan.sweepSupport, F.R i = S.R i) : plan.SweepReady windows w borrowed F := by
  refine ⟨?_,?_,?_⟩
  · rw [hR _ (by simp [sweepSupport])]; exact h.count
  · rw [hR _ (by simp [sweepSupport])]; exact h.advances
  · intro i hi
    rw [hR i (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi))]
    exact h.fresh i hi

theorem SweepReady.generated {src dst : Fin PackedTranspose.tapeCount}
    {plan : PreparedPublicationPlan PackedTranspose.tapeCount src dst}
    {windows : PublicationWindows s L} {b N W V : ℕ}
    {borrowed : List (Fin (prime+K+4))} {S : Stacks PackedTranspose.tapeCount (prime+K)}
    (h : plan.SweepReady windows W borrowed S)
    (hoff : ∀ i ∈ plan.sweepSupport, i ∉ generatedPublicationHeaderRegisters)
    (hwindow : plan.window = headerReg 82) (hpadding : plan.padRows = headerReg 53)
    (hwordPort : plan.wordWidth = headerReg 87)
    (hword : (S.R (headerReg 87)).length = W) :
    plan.Ready windows W (2^Nat.clog 2 N-N) borrowed (generatedPublicationHeadersState b N L W V S) := by
  let F := generatedPublicationHeadersState b N L W V S
  have hread (i : Fin PackedTranspose.tapeCount) (hi : i ∈ plan.sweepSupport) : F.R i = S.R i :=
    generatedPublicationHeadersState_off b N L W V S i (hoff i hi)
  have hF := h.of_frame (F := F) hread
  have hi := headerReg_injective
  have hcap : capacityRows = headerReg 81 := rfl
  refine ⟨hF.count,hF.advances,?_,?_,?_,hF.fresh⟩
  · rw [hwindow]
    simp [F,generatedPublicationHeadersState,publicationHeadersState,countedPublicationDimensionsState,
      PublicationDimensionReg.loaded,countedPublicationDimensionBank,countedPublicationDimensionIndex,hi.eq_iff]
  · rw [hpadding]
    simp [F,generatedPublicationHeadersState,publicationHeadersState,countedPublicationDimensionsState,
      PublicationDimensionReg.loaded,countedPublicationDimensionBank,countedPublicationDimensionIndex,hi.eq_iff]
  · rw [hwordPort]
    have hreadWord : F.R (headerReg 87) = S.R (headerReg 87) := generatedPublicationHeadersState_off _ _ _ _ _ _ _
      (by simp [generatedPublicationHeaderRegisters,countedPublicationDimensionRegisters,publicationBinaryRegisters,hi.eq_iff])
    rw [hreadWord]
    exact hword

theorem generated_clock_length (b N L W V : ℕ) (S : Stacks PackedTranspose.tapeCount (prime+K)) :
    ((generatedPublicationHeadersState b N L W V S).R (headerReg 54)).length = 2^b := by
  simp [generatedPublicationHeadersState,publicationHeadersState,countedPublicationDimensionsState,
    PublicationDimensionReg.loaded,countedPublicationDimensionBank,countedPublicationDimensionIndex,headerReg_injective.eq_iff]

end PreparedPublicationPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
