module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRecoveryInputBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedGeneratedReplicaBoundaryFactory

/-! Reuse the generated ordinary recovery headers for a cached pass. This
placement adapter supplies readiness, not an execution producing the bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack
variable {s A : ℕ} [NeZero s]

/-- A complete view of a cached bank transports its input contract under any
injective placement. No caller-specific register cases enter the proof. -/
theorem CachedReplicaPassInput.of_reindex_view {T T' : ℕ} {H : ReplicaHaloProblem s}
    {job : CachedReplicaPassPlacement T} {buffers : ReplicaLoopBuffers A}
    {S : Stacks T A} {F : Stacks T' A} (h : CachedReplicaPassInput H job buffers S)
    (e : Fin T → Fin T') (he : Function.Injective e) (hview : embStk e F = S) :
    CachedReplicaPassInput H (job.reindex e he) buffers F := by
  subst S
  refine ⟨h.headers.of_gather_view rfl,h.bank,h.cache,h.solverFresh,h.input,h.outputStream,
    h.savedGather,h.keys,h.destination,h.gatherFresh,?_,?_,?_⟩
  · intro i hi
    simpa only [CachedReplicaPassPlacement.reindex,ReplicaCouplingPlacement.reindex_bank,embStk_R]
      using h.couplingBlank i hi
  · intro i hi
    simpa only [CachedReplicaPassPlacement.reindex,ReplicaCouplingPlacement.reindex_bank,embStk_R]
      using h.couplingFresh i hi
  · intro i hi
    simpa only [CachedReplicaPassPlacement.reindex,ReplicaCouplingPlacement.reindex_bank,embStk_R]
      using h.couplingWork i hi

noncomputable def generatedCachedReplicaInput (H : ReplicaHaloProblem s)
    (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 300 A :=
  embStk (Fin.castLE (by decide : 300 ≤ 392)) (generatedRecoveryInput H inp out)

theorem generatedCachedReplicaInput_ready (H : ReplicaHaloProblem s)
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    CachedReplicaPassInput H CachedReplicaPassPlacement.standard (generatedRecoveryBuffers H inp out)
      (generatedCachedReplicaInput (A := A) H inp out) := by
  let S := generatedCachedReplicaInput (A := A) H inp out
  have hhigh (i : Fin 300) (hi : 126 ≤ i.val) : S.R i = [] := by
    apply generatedRecoveryInput_off H inp out (Fin.castLE (by decide : 300 ≤ 392) i) hi
    intro he
    have hv := congrArg Fin.val he
    have hh := i.isLt
    change i.val = 390 at hv
    omega
  have hsolver (i : Fin 121) : S.R (CachedReplicaPassPlacement.standard.plan.solver i) = [] := by
    apply hhigh
    change 126 ≤ 126+i.val
    omega
  have hheader (i : Fin 126) (hi : i ≠ 124) (hz : generatedRecoveryHeader H i = 0) :
      S.R (CachedReplicaPassPlacement.standard.plan.gather i) = [] := by
    change (generatedRecoveryInput (A := A) H inp out).R (replicaRecoveryBatchInterior.gather i) = []
    rw [generatedRecoveryInput_gather H inp out i hi,hz]
    rfl
  have hextra (i : Fin 168) (hi : 117 ≤ i.val) :
      S.R (CachedReplicaPassPlacement.standard.coupling.bank i) = [] := by
    change S.R (ReplicaCouplingPlacement.standard.bank i) = []
    unfold ReplicaCouplingPlacement.bank
    rw [dif_neg (by omega)]
    apply hhigh
    change 126 ≤ 249+(i.val-117)
    omega
  refine ⟨?_,?_,hsolver 117,?_,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_⟩
  · apply (generatedRecoveryInput_headers H inp out).of_gather_view
    rfl
  · refine Stacks.ext rfl rfl ?_ ?_
    · rfl
    · funext i
      have hh := hsolver (weightCacheCoreReg i)
      simpa only [embStk,Function.comp_apply,generatedRecoveryBuffers,
        releasedCellBank,List.nil_append,ite_self] using hh
  · intro i hi
    exact hsolver i
  · exact hheader 87 (by decide) (by simp [generatedRecoveryHeader,replicaFactoryHeaderValue])
  · exact hhigh 247 (by decide)
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl
    all_goals apply hheader _ (by decide)
    all_goals simp [generatedRecoveryHeader,replicaFactoryHeaderValue]
  · intro i hi
    apply hextra
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hi
    omega
  · intro i hi
    apply hextra
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hi
    omega
  · intro i hi
    apply hextra
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hi
    omega

/-- The two ordinary cached inputs beside an arbitrary factor bank. Shared I/O
is taken from the factor bank, so placing numerical inputs does not consume it. -/
noncomputable def generatedCyclicReplicaInput (H K : ReplicaHaloProblem s)
    (factor : Stacks 234 A) : Stacks 834 A :=
  ⟨factor.inp,factor.out,
    fun i => if hi : 600 ≤ i.val then factor.L ⟨i.val-600,by have := i.isLt; omega⟩ else [],
    fun i => if hi : i.val < 300 then
      (generatedCachedReplicaInput H factor.inp factor.out).R ⟨i.val,hi⟩
    else if hj : i.val < 600 then
      (generatedCachedReplicaInput K factor.inp factor.out).R ⟨i.val-300,by omega⟩
    else factor.R ⟨i.val-600,by have := i.isLt; omega⟩⟩

theorem generatedCyclicReplicaInput_left (H K : ReplicaHaloProblem s) (factor : Stacks 234 A) :
    embStk CyclicReplicaPlacement.leftReg (generatedCyclicReplicaInput H K factor) =
      generatedCachedReplicaInput H factor.inp factor.out := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    simp [embStk,generatedCyclicReplicaInput,CyclicReplicaPlacement.leftReg,
      generatedCachedReplicaInput,generatedRecoveryInput,show ¬600 ≤ i.val by have := i.isLt; omega]
  · funext i
    simp [embStk,generatedCyclicReplicaInput,CyclicReplicaPlacement.leftReg,i.isLt]

theorem generatedCyclicReplicaInput_right (H K : ReplicaHaloProblem s) (factor : Stacks 234 A) :
    embStk CyclicReplicaPlacement.rightReg (generatedCyclicReplicaInput H K factor) =
      generatedCachedReplicaInput K factor.inp factor.out := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    simp [embStk,generatedCyclicReplicaInput,CyclicReplicaPlacement.rightReg,
      generatedCachedReplicaInput,generatedRecoveryInput,show ¬600 ≤ 300+i.val by have := i.isLt; omega]
  · funext i
    simp [embStk,generatedCyclicReplicaInput,CyclicReplicaPlacement.rightReg,
      show ¬300+i.val < 300 by omega,show 300+i.val < 600 by have := i.isLt; omega]

theorem generatedCyclicReplicaInput_factor (H K : ReplicaHaloProblem s) (factor : Stacks 234 A) :
    embStk CyclicReplicaPlacement.factorReg (generatedCyclicReplicaInput H K factor) = factor := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    simp [embStk,generatedCyclicReplicaInput,CyclicReplicaPlacement.factorReg]
  · funext i
    simp [embStk,generatedCyclicReplicaInput,CyclicReplicaPlacement.factorReg,
      show ¬600+i.val < 300 by omega,show ¬600+i.val < 600 by omega]

/-- Both physical readiness premises of the cyclic caller follow from ordinary
headers and archives; the separate factor-input premise is preserved verbatim. -/
theorem generatedCyclicReplicaInput_ready (H K : ReplicaHaloProblem s) (factor : Stacks 234 A) :
    CachedReplicaPassInput H CyclicReplicaPlacement.left
      (generatedRecoveryBuffers H factor.inp factor.out) (generatedCyclicReplicaInput H K factor) ∧
    CachedReplicaPassInput K CyclicReplicaPlacement.right
      (generatedRecoveryBuffers K factor.inp factor.out) (generatedCyclicReplicaInput H K factor) := by
  constructor
  · exact (generatedCachedReplicaInput_ready H factor.inp factor.out).of_reindex_view
      _ CyclicReplicaPlacement.leftReg_injective (generatedCyclicReplicaInput_left H K factor)
  · exact (generatedCachedReplicaInput_ready K factor.inp factor.out).of_reindex_view
      _ CyclicReplicaPlacement.rightReg_injective (generatedCyclicReplicaInput_right H K factor)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
