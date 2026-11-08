module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseReplicaCouplingNative
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorResumeReady
public import IntegerMultBounds.MathlibTM2.Host.ClearBankExcept

/-! Release the native controls once before a second interior pass. Both payload
ports, gather metadata and reserved solver tapes survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def replicaInteriorReleasePorts (plan : ReplicaInteriorPlacement T) : List (Fin T) :=
  replicaCouplingNativeIndices.map (fun i => plan.solver (weightCacheCoreReg i))

def releaseReplicaInteriorBank (plan : ReplicaInteriorPlacement T) : Pr P T Q A U :=
  clearWords (replicaInteriorReleasePorts plan)

def releasedReplicaInteriorBank (plan : ReplicaInteriorPlacement T) (S : Stacks T A) : Stacks T A :=
  {S with R := fun k => if k ∈ replicaInteriorReleasePorts plan then [] else S.R k}

def releaseReplicaInteriorBankCost (plan : ReplicaInteriorPlacement T) (S : Stacks T A) : ℕ :=
  2*((replicaInteriorReleasePorts plan).map (fun k => (S.R k).length)).sum+
    2*(replicaInteriorReleasePorts plan).length+1

theorem releaseReplicaInteriorBank_exec (plan : ReplicaInteriorPlacement T)
    (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', v'.user = v.user ∧
      Exec body (releaseReplicaInteriorBank plan) (mk v S) (releaseReplicaInteriorBankCost plan S)
        (mk v' (releasedReplicaInteriorBank plan S)) := by
  apply clearWords_exec
  exact ((List.nodup_finRange 117).filter _).map (plan.solver_injective.comp weightCacheCoreReg_injective)

/-- Retiring the first pass's controls uses no extra live space. The exact
erasure time still charges every symbol present in the disposable ports. -/
theorem releaseReplicaInteriorBank_exec_within (plan : ReplicaInteriorPlacement T)
    (v : HS T Q A U) (S : Stacks T A) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth) depth
        (releaseReplicaInteriorBank plan) (mk v S) (releaseReplicaInteriorBankCost plan S)
        (mk v' (releasedReplicaInteriorBank plan S)) := by
  obtain ⟨v',hu,he⟩ := releaseReplicaInteriorBank_exec (body := body) plan v S
  refine ⟨v',hu,?_⟩
  apply mn_native_exec_within he 0 (clearWords_native_zero _) depth _
  omega

theorem replicaInteriorReleasePorts_native (plan : ReplicaInteriorPlacement T) (i : Fin 117) :
    plan.solver (weightCacheCoreReg i) ∈ replicaInteriorReleasePorts plan ↔ i ≠ 93 ∧ i ≠ 110 := by
  constructor
  · intro hi
    obtain ⟨j,hj,he⟩ := List.mem_map.mp hi
    have hji : j = i := weightCacheCoreReg_injective (plan.solver_injective he)
    subst j
    simpa [replicaCouplingNativeIndices] using hj
  · intro hi
    exact List.mem_map.mpr ⟨i,by simpa [replicaCouplingNativeIndices] using hi,rfl⟩

theorem replicaInteriorReleasePorts_gather (plan : ReplicaInteriorPlacement T) (i : Fin 126) :
    plan.gather i ∉ replicaInteriorReleasePorts plan := by
  intro hi
  obtain ⟨j,_,he⟩ := List.mem_map.mp hi
  exact plan.disjoint i _ he.symm

theorem replicaInteriorReleasePorts_reserved (plan : ReplicaInteriorPlacement T) (i : Fin 121)
    (hi : 117 ≤ i.val) : plan.solver i ∉ replicaInteriorReleasePorts plan := by
  intro hmem
  obtain ⟨j,_,he⟩ := List.mem_map.mp hmem
  have hv := congrArg (fun k : Fin 121 => k.val) (plan.solver_injective he)
  change j.val = i.val at hv
  have := j.isLt
  omega

theorem releasedReplicaInteriorBank_native (plan : ReplicaInteriorPlacement T) (S : Stacks T A)
    (hleft : ∀ i : Fin 117, S.L (plan.solver (weightCacheCoreReg i)) = []) :
    embStk weightCacheCoreReg (embStk plan.solver (releasedReplicaInteriorBank plan S)) =
      releasedCellBank [] (S.R (plan.solver 110)) (S.R (plan.solver 93)) S.inp S.out := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i; exact hleft i
  · funext i
    change (if plan.solver (weightCacheCoreReg i) ∈ replicaInteriorReleasePorts plan then [] else
      S.R (plan.solver (weightCacheCoreReg i))) =
      (if i.val = 93 then S.R (plan.solver 93) else if i.val = 110 then []++S.R (plan.solver 110) else [])
    simp only [replicaInteriorReleasePorts_native]
    by_cases h93 : i = 93
    · subst i; simp [weightCacheCoreReg]
    by_cases h110 : i = 110
    · subst i; simp [weightCacheCoreReg]
    have hv93 : i.val ≠ 93 := fun he => h93 (Fin.ext he)
    have hv110 : i.val ≠ 110 := fun he => h110 (Fin.ext he)
    simp only [h93,h110,ne_eq,not_false_eq_true,and_self,ite_true,hv93,hv110,ite_false]

theorem releaseReplicaInteriorBankCost_eq (plan : ReplicaInteriorPlacement T) (S F : Stacks T A)
    (hf : ∀ i, F.R (plan.solver i) = S.R (plan.solver i)) :
    releaseReplicaInteriorBankCost plan F = releaseReplicaInteriorBankCost plan S := by
  have hm : (replicaInteriorReleasePorts plan).map (fun k => (F.R k).length) =
      (replicaInteriorReleasePorts plan).map (fun k => (S.R k).length) := by
    apply List.map_congr_left
    intro k hk
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hk
    exact congrArg List.length (hf _)
  unfold releaseReplicaInteriorBankCost
  rw [hm]

theorem ReplicaInteriorResumeReady.released {s : ℕ} {H : ReplicaHaloProblem s}
    {job : CachedReplicaPassPlacement T} {buffers : ReplicaLoopBuffers A} {S : Stacks T A}
    (h : ReplicaInteriorResumeReady H job buffers S) :
    ReplicaInteriorResumeReady H job buffers (releasedReplicaInteriorBank job.plan S) := by
  apply h.transport (job' := job) (F := releasedReplicaInteriorBank job.plan S) rfl rfl
  · intro i _
    exact ite_eq_right (replicaInteriorReleasePorts_gather job.plan i)
  · intro i hi
    exact ite_eq_right (replicaInteriorReleasePorts_reserved job.plan i hi)
  · intro i; rfl
  · apply ite_eq_right
    intro hk
    obtain ⟨i,_,he⟩ := List.mem_map.mp hk
    exact job.solver_output _ he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
