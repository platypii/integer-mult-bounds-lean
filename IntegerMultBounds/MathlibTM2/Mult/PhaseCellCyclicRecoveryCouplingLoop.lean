module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryCouplingStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedListLoopStock

/-! Chronological paired recovery shares one numerical scratch reserve across
all replicas. Its cursor retains both original queues, both outputs and factors. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
local notation "jointSource" => CyclicRecoveryPlacement.bank 132
local notation "clock" => CyclicRecoveryPlacement.bank 228
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 840 Q A U}

noncomputable def cyclicRecoveryCouplingLoop (hQ : SS.states ≤ Q) : Pr P 840 Q A U :=
  countedLoop clock (cyclicRecoveryCouplingRow hQ)

theorem cyclicRecoveryCouplingLoop_exec_within (H K : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hsepL : H.span+H.band ≤ s) (hsepR : K.span+K.band ≤ s)
    (buffersL buffersR : ReplicaLoopBuffers A) (rows : List (CyclicRecoveryRow s))
    (hfitsL : ∀ row ∈ rows, ∀ j, Fits H.wordWidth (row.1 j))
    (hfitsR : ∀ row ∈ rows, ∀ j, Fits K.wordWidth (row.1 j))
    (tail rhsL rhsR rawL rawR pageL pageR : List (Fin (A+4))) (v : HS 840 Q A U) (S : Stacks 840 A)
    (headersL : ReplicaRecoveryRhsHeaders H CyclicRecoveryPlacement.leftJob.plan.gather buffersL S)
    (headersR : ReplicaRecoveryRhsHeaders K CyclicRecoveryPlacement.rightJob.plan.gather buffersR S)
    (cacheL : CachedRecoveryCouplingReady H rawL pageL (embStk CyclicRecoveryPlacement.leftJob.coupling.bank S))
    (cacheR : CachedRecoveryCouplingReady K rawR pageR (embStk CyclicRecoveryPlacement.rightJob.coupling.bank S))
    (hsource : S.R jointSource = rows.flatMap (fun row => cyclicRecoveryField H row.1++cyclicRecoveryField K row.1)++tail)
    (hrhsL : S.R (CyclicRecoveryPlacement.leftJob.coupling.bank 93) = rows.flatMap (fun row => cyclicRecoveryField H row.2.1)++rhsL)
    (hrhsR : S.R (CyclicRecoveryPlacement.rightJob.coupling.bank 93) = rows.flatMap (fun row => cyclicRecoveryField K row.2.2)++rhsR)
    (hcount : (S.R clock).length = rows.length) :
    ∃ vf F m, vf.user = v.user ∧
      m ≤ rows.length*(cyclicRecoveryCouplingPieceCost H+cyclicRecoveryCouplingPieceCost K+3)+2 ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (cyclicRecoveryCouplingPieceWorkspace (A := A) (U := U) H hQ+
          cyclicRecoveryCouplingPieceWorkspace (A := A) (U := U) K hQ))
        depth (cyclicRecoveryCouplingLoop hQ) (mk v S) m (mk vf F)) ∧ F.R clock = [] ∧
      CyclicRecoveryCouplingCursor H K buffersL buffersR rows [] tail rhsL rhsR rawL rawR pageL pageR S F := by
  let Ready := fun todo F => ∃ done, rows = done++todo ∧
    CyclicRecoveryCouplingCursor H K buffersL buffersR done todo tail rhsL rhsR rawL rawR pageL pageR S F
  have hstable : ∀ todo F xs, Ready todo F → Ready todo {F with R := Function.update F.R clock xs} := by
    intro todo F xs h
    obtain ⟨done,heq,hc⟩ := h
    exact ⟨done,heq,hc.update_clock xs⟩
  have hstep : ∀ row ∈ rows, ∀ todo (vi : HS 840 Q A U) F, Ready (row::todo) F →
      ∃ vf G m, vf.user = vi.user ∧ m ≤ cyclicRecoveryCouplingPieceCost H+cyclicRecoveryCouplingPieceCost K ∧
        (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk vi F)+depth+
          (cyclicRecoveryCouplingPieceWorkspace (A := A) (U := U) H hQ+
            cyclicRecoveryCouplingPieceWorkspace (A := A) (U := U) K hQ))
          depth (cyclicRecoveryCouplingRow hQ) (mk vi F) m (mk vf G)) ∧
        G.R clock = F.R clock ∧ Ready todo G ∧ mnSize (mk vf G) ≤ mnSize (mk vi F) := by
    intro row hr todo vi F h
    obtain ⟨done,heq,hc⟩ := h
    obtain ⟨vf,G,m,hu,hm,he,hclock,hG,hstock⟩ := cyclicRecoveryCouplingStep_exec_within (body := body)
      H K hQ hA hsepL hsepR buffersL buffersR done todo row (hfitsL row hr) (hfitsR row hr)
      tail rhsL rhsR rawL rawR pageL pageR S F vi hc
    exact ⟨vf,G,m,hu,hm,he,hclock,⟨done++[row],by simpa only [List.append_assoc,List.singleton_append] using heq,hG⟩,hstock⟩
  have hinit : Ready rows S := by
    refine ⟨[],rfl,hsource,hrhsL,hrhsR,?_,?_,?_,?_,headersL,headersR,?_,?_,rfl,rfl,rfl,?_⟩
    · simp
    · simp
    · simp
    · simp
    · simpa using cacheL
    · simpa using cacheR
    · intro k _; rfl
  obtain ⟨vf,F,m,hu,hm,he,hclock,hF⟩ := countedListLoop_exec_within (body := body)
    clock (cyclicRecoveryCouplingRow hQ) rows (fun _ => cyclicRecoveryCouplingPieceCost H+cyclicRecoveryCouplingPieceCost K)
    Ready (cyclicRecoveryCouplingPieceWorkspace (A := A) (U := U) H hQ+
      cyclicRecoveryCouplingPieceWorkspace (A := A) (U := U) K hQ) hstable hstep v S hcount hinit
  obtain ⟨done,hdone,hcursor⟩ := hF
  simp only [List.append_nil] at hdone
  subst done
  exact ⟨vf,F,m,hu,by simpa using hm,he,hclock,hcursor⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
