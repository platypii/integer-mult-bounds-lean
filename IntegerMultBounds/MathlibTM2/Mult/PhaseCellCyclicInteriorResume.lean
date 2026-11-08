module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedInteriorResume
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryCouplingCursor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryMasks
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedNativeCyclicBoundaryBatch

/-! Native projection, preparation and the coupling cursor preserve both
second-pass peripheral contracts, independently of the number of replicas. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open CyclicRecoveryPlacement
variable {s A : ℕ} [NeZero s]

theorem cyclicBoundaryProjection_resume (H K : ReplicaHaloProblem s) (buffersL buffersR : ReplicaLoopBuffers A)
    (S : Stacks 840 A) (tail output : List (Fin (A+4)))
    (hL : ReplicaInteriorResumeReady H leftJob buffersL S)
    (hR : ReplicaInteriorResumeReady K rightJob buffersR S) :
    let F := placedNativeCyclicBoundaryBatchState (cyclicRecoveryMaskState H K S) tail output
    ReplicaInteriorResumeReady H leftJob buffersL F ∧ ReplicaInteriorResumeReady K rightJob buffersR F := by
  have keep (job : CachedReplicaPassPlacement 840) (J : ReplicaHaloProblem s) (buffers : ReplicaLoopBuffers A)
      (h : ReplicaInteriorResumeReady J job buffers S)
      (hoff : ∀ (i : Fin 240) (k : Fin 840), job.Owns k → k ≠ CyclicRecoveryPlacement.bank i) :
      ReplicaInteriorResumeReady J job buffers
        (placedNativeCyclicBoundaryBatchState (cyclicRecoveryMaskState H K S) tail output) := by
    apply h.of_frame (F := placedNativeCyclicBoundaryBatchState (cyclicRecoveryMaskState H K S) tail output) rfl rfl
    intro k hk
    exact ⟨rfl,by simp only [placedNativeCyclicBoundaryBatchState,cyclicRecoveryMaskState,
      Function.update_of_ne (hoff 224 k hk),Function.update_of_ne (hoff 132 k hk),
      Function.update_of_ne (hoff 238 k hk),Function.update_of_ne (hoff 239 k hk)]⟩
  exact ⟨keep leftJob H buffersL hL native_left_disjoint,keep rightJob K buffersR hR native_right_disjoint⟩

theorem CyclicRecoveryCouplingCursor.resume {H K : ReplicaHaloProblem s}
    {buffersL buffersR : ReplicaLoopBuffers A} {done todo : List (CyclicRecoveryRow s)}
    {tail rhsL rhsR rawL rawR pageL pageR : List (Fin (A+4))} {S F : Stacks 840 A}
    (h : CyclicRecoveryCouplingCursor H K buffersL buffersR done todo tail rhsL rhsR rawL rawR pageL pageR S F)
    (hL : ReplicaInteriorResumeReady H leftJob buffersL S)
    (hR : ReplicaInteriorResumeReady K rightJob buffersR S) :
    ReplicaInteriorResumeReady H leftJob buffersL F ∧ ReplicaInteriorResumeReady K rightJob buffersR F := by
  have gatherAway (k : Fin 840) (hspan : k.val < 126 ∨ 300 ≤ k.val ∧ k.val < 426)
      (h125 : k.val ≠ 125) (h425 : k.val ≠ 425) : k ∉ cyclicRecoveryCouplingPorts := by
    simp only [cyclicRecoveryCouplingPorts,List.mem_cons,List.not_mem_nil,or_false,not_or,Fin.ext_iff]
    change k.val ≠ 732 ∧ k.val ≠ 219 ∧ k.val ≠ 236 ∧ k.val ≠ 125 ∧
      k.val ≠ 519 ∧ k.val ≠ 536 ∧ k.val ≠ 425 ∧ k.val ≠ 828
    omega
  have solverAway (k : Fin 840) (hspan : 243 ≤ k.val ∧ k.val < 247 ∨ 543 ≤ k.val ∧ k.val < 547) :
      k ∉ cyclicRecoveryCouplingPorts := by
    simp only [cyclicRecoveryCouplingPorts,List.mem_cons,List.not_mem_nil,or_false,not_or,Fin.ext_iff]
    change k.val ≠ 732 ∧ k.val ≠ 219 ∧ k.val ≠ 236 ∧ k.val ≠ 125 ∧
      k.val ≠ 519 ∧ k.val ≠ 536 ∧ k.val ≠ 425 ∧ k.val ≠ 828
    omega
  have keep (job : CachedReplicaPassPlacement 840) (J : ReplicaHaloProblem s) (buffers : ReplicaLoopBuffers A)
      (ready : ReplicaInteriorResumeReady J job buffers S)
      (hg : ∀ i : Fin 126, i ≠ 125 → job.plan.gather i ∉ cyclicRecoveryCouplingPorts)
      (hs : ∀ i : Fin 121, 117 ≤ i.val → job.plan.solver i ∉ cyclicRecoveryCouplingPorts)
      (hd : job.output ∉ cyclicRecoveryCouplingPorts) : ReplicaInteriorResumeReady J job buffers F :=
    ready.transport h.input h.output (fun i hi => h.frame _ (hg i hi))
      (fun i hi => h.frame _ (hs i hi)) (fun i => congrFun h.left _) (h.frame _ hd)
  constructor
  · apply keep leftJob H buffersL hL
    · intro i hi
      have hi125 : i.val ≠ 125 := fun he => hi (Fin.ext he)
      have hib := i.isLt
      apply gatherAway
      · exact Or.inl i.isLt
      · exact hi125
      · change i.val ≠ 425; omega
    · intro i hi
      apply solverAway
      apply Or.inl
      change 243 ≤ 126+i.val ∧ 126+i.val < 247
      have := i.isLt
      omega
    · decide
  · apply keep rightJob K buffersR hR
    · intro i hi
      have hi125 : i.val ≠ 125 := fun he => hi (Fin.ext he)
      have hib := i.isLt
      apply gatherAway
      · apply Or.inr
        change 300 ≤ 300+i.val ∧ 300+i.val < 426
        omega
      · change 300+i.val ≠ 125; omega
      · change 300+i.val ≠ 425; omega
    · intro i hi
      apply solverAway
      apply Or.inr
      change 543 ≤ 300+(126+i.val) ∧ 300+(126+i.val) < 547
      have := i.isLt
      omega
    · decide

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
