module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryCounters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryRhs

/-! Prepare the mask, selector count, fold counters and symbol volume once.
Subsequent physical rows reuse the resulting RHS readiness contract. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 242 Q A U}

def initializeReplicaBoundaryRhs : Pr P 242 Q A U :=
  .seq replicaBoundaryMask replicaBoundaryCounters

def initializedReplicaBoundaryRhsState (H : ReplicaHaloProblem s) (S : Stacks 242 A) : Stacks 242 A :=
  replicaBoundaryCounterState (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card H.wordWidth
    (replicaBoundaryMaskState H S)

def initializeReplicaBoundaryRhsCost (H : ReplicaHaloProblem s) := replicaBoundaryMaskCost H+
  replicaBoundaryCountersCost (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card H.wordWidth

theorem initializedReplicaBoundaryRhsState_frame (H : ReplicaHaloProblem s) (S : Stacks 242 A)
    (k : Fin 242) (hk : k ∉ [116,117,118,120,124,167]) :
    (initializedReplicaBoundaryRhsState H S).R k = S.R k := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
  simp [initializedReplicaBoundaryRhsState,replicaBoundaryCounterState,replicaBoundaryFoldCounterState,
    replicaBoundaryMaskState,hk.1,hk.2.1,hk.2.2.1,hk.2.2.2.1,hk.2.2.2.2.1,hk.2.2.2.2.2]

theorem initializeReplicaBoundaryRhs_exec (H : ReplicaHaloProblem s) (hA : 4 ≤ A)
    (v : HS 242 Q A U) (S : Stacks 242 A)
    (hmeta : CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span
      (embStk (Fin.castLE (by decide : 168 ≤ 242)) S))
    (hvolume : (S.R 123).length = H.span*H.wordWidth) (hwidth : (S.R 130).length = H.wordWidth)
    (hscratch : ∀ k : Fin 242, k.val < 77 → S.R k = [])
    (hfresh : ∀ k ∈ [(104 : Fin 242),105,116,117,118,120,124,143,167], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ initializeReplicaBoundaryRhsCost H ∧
      Exec body initializeReplicaBoundaryRhs (mk v S) m (mk v' (initializedReplicaBoundaryRhsState H S)) ∧
      ReplicaBoundaryRhsReady H (initializedReplicaBoundaryRhsState H S) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := replicaBoundaryMask_exec (body := body) H hA v S hmeta
    (fun k hk => hscratch k (by omega)) (hfresh 167 (by simp)) (hfresh 116 (by simp))
  let J := replicaBoundaryMaskState H S
  let n := (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := replicaBoundaryCounters_exec (body := body) n H.wordWidth v₁ J
    (by simp [J,replicaBoundaryMaskState,n]) (by simpa [J,replicaBoundaryMaskState] using hwidth) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (simpa [J,replicaBoundaryMaskState] using hscratch 1 (by decide))
        | (simpa [J,replicaBoundaryMaskState] using hscratch 4 (by decide))
        | (simpa [J,replicaBoundaryMaskState] using hscratch 5 (by decide))
        | (simpa [J,replicaBoundaryMaskState] using hfresh 104 (by simp))
        | (simpa [J,replicaBoundaryMaskState] using hfresh 105 (by simp))
        | (simpa [J,replicaBoundaryMaskState] using hfresh 117 (by simp))
        | (simpa [J,replicaBoundaryMaskState] using hfresh 118 (by simp))
        | (simpa [J,replicaBoundaryMaskState] using hfresh 120 (by simp))
        | (simpa [J,replicaBoundaryMaskState] using hfresh 124 (by simp)))
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,Exec.seq he₁ he₂,?_⟩
  constructor
  · simpa [initializedReplicaBoundaryRhsState,replicaBoundaryCounterState,replicaBoundaryFoldCounterState,replicaBoundaryMaskState] using hvolume
  · simp [initializedReplicaBoundaryRhsState,replicaBoundaryCounterState,replicaBoundaryFoldCounterState,replicaBoundaryMaskState]
  · simp [initializedReplicaBoundaryRhsState,replicaBoundaryCounterState,replicaBoundaryFoldCounterState,replicaBoundaryMaskState]
  · simpa [initializedReplicaBoundaryRhsState,replicaBoundaryCounterState,replicaBoundaryFoldCounterState,replicaBoundaryMaskState] using hwidth
  · simp [initializedReplicaBoundaryRhsState,replicaBoundaryCounterState,replicaBoundaryFoldCounterState,replicaBoundaryMaskState]
  · simp [initializedReplicaBoundaryRhsState,replicaBoundaryCounterState,replicaBoundaryFoldCounterState,replicaBoundaryMaskState]
  · simp [initializedReplicaBoundaryRhsState,replicaBoundaryCounterState,replicaBoundaryFoldCounterState,replicaBoundaryMaskState]
  · simp [initializedReplicaBoundaryRhsState,replicaBoundaryCounterState,replicaBoundaryFoldCounterState,replicaBoundaryMaskState]
  · simpa [initializedReplicaBoundaryRhsState,replicaBoundaryCounterState,replicaBoundaryFoldCounterState,replicaBoundaryMaskState] using hfresh 104 (by simp)
  · simpa [initializedReplicaBoundaryRhsState,replicaBoundaryCounterState,replicaBoundaryFoldCounterState,replicaBoundaryMaskState] using hfresh 105 (by simp)
  · simpa [initializedReplicaBoundaryRhsState,replicaBoundaryCounterState,replicaBoundaryFoldCounterState,replicaBoundaryMaskState] using hfresh 143 (by simp)
  · intro k hk
    have h116 : k ≠ 116 := by intro he; subst k; omega
    have h117 : k ≠ 117 := by intro he; subst k; omega
    have h118 : k ≠ 118 := by intro he; subst k; omega
    have h120 : k ≠ 120 := by intro he; subst k; omega
    have h124 : k ≠ 124 := by intro he; subst k; omega
    have h167 : k ≠ 167 := by intro he; subst k; omega
    simpa [initializedReplicaBoundaryRhsState,replicaBoundaryCounterState,replicaBoundaryFoldCounterState,
      replicaBoundaryMaskState,h116,h117,h118,h120,h124,h167] using hscratch k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
