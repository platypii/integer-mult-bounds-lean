module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorResumeReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaPlacement

/-! Redirect the second interior pass's disposable gather tape to fresh storage.
The saved boundary archive stays in place and outside the pass's footprint. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

def ReplicaInteriorPlacement.reserveArchive {T : ℕ} (plan : ReplicaInteriorPlacement T)
    (fresh : Fin T) (hg : ∀ i, fresh ≠ plan.gather i) (hs : ∀ i, fresh ≠ plan.solver i) :
    ReplicaInteriorPlacement T where
  gather := Function.update plan.gather 125 fresh
  solver := plan.solver
  gather_injective := by
    intro i j he
    by_cases hi : i = 125
    · subst i
      by_cases hj : j = 125
      · exact hj.symm
      · simp only [Function.update_self,Function.update_of_ne hj] at he
        exact (hg j he).elim
    · by_cases hj : j = 125
      · subst j
        simp only [Function.update_self,Function.update_of_ne hi] at he
        exact (hg i he.symm).elim
      · simp only [Function.update_of_ne hi,Function.update_of_ne hj] at he
        exact plan.gather_injective he
  solver_injective := plan.solver_injective
  disjoint := by
    intro i j
    by_cases hi : i = 125
    · subst i; simpa only [Function.update_self] using hs j
    · simpa only [Function.update_of_ne hi] using plan.disjoint i j

theorem ReplicaInteriorPlacement.reserveArchive_avoids {T : ℕ} (plan : ReplicaInteriorPlacement T)
    (fresh : Fin T) (hg hs) (i : Fin 126) :
    (plan.reserveArchive fresh hg hs).gather i ≠ plan.gather 125 := by
  change Function.update plan.gather 125 fresh i ≠ _
  by_cases hi : i = 125
  · subst i; simpa only [Function.update_self] using hg 125
  · simpa only [Function.update_of_ne hi] using plan.gather_injective.ne hi

theorem ReplicaInteriorResumeReady.archive_headers {s T A : ℕ} {H : ReplicaHaloProblem s}
    {job : CachedReplicaPassPlacement T} {buffers : ReplicaLoopBuffers A} {S : Stacks T A}
    (h : ReplicaInteriorResumeReady H job buffers S) (fresh : Fin T)
    (hg : ∀ i, fresh ≠ job.plan.gather i) (hs : ∀ i, fresh ≠ job.plan.solver i)
    (hblank : S.R fresh = []) :
    ReplicaLoopHeaders H (job.plan.reserveArchive fresh hg hs).gather buffers S := by
  have hread (i : Fin 126) : S.R ((job.plan.reserveArchive fresh hg hs).gather i) =
      Function.update S.R (job.plan.gather 125) [] (job.plan.gather i) := by
    change S.R (Function.update job.plan.gather 125 fresh i) = _
    by_cases hi : i = 125
    · subst i; simpa only [Function.update_self] using hblank
    · simp only [Function.update_of_ne hi,Function.update_of_ne (job.plan.gather_injective.ne hi)]
  constructor
  · intro r hr h102 h116
    exact (congrArg List.length (hread r.1)).trans (h.headers.masters r hr h102 h116)
  · exact (congrArg List.length (hread 111)).trans h.headers.origin
  · exact (congrArg List.length (hread 113)).trans h.headers.endpoint
  · exact (congrArg List.length (hread 115)).trans h.headers.width
  · exact (congrArg List.length (hread 123)).trans h.headers.volume
  · exact (hread 124).trans h.headers.source
  · intro i hi; exact (hread i).trans (h.headers.blank i hi)
  · intro i hi; exact (hread i).trans (h.headers.fresh i hi)

theorem ReplicaInteriorResumeReady.extend {s T T' A : ℕ} {H : ReplicaHaloProblem s}
    {job : CachedReplicaPassPlacement T} {buffers : ReplicaLoopBuffers A} {S : Stacks T A}
    (h : ReplicaInteriorResumeReady H job buffers S) (hTT : T ≤ T') :
    ReplicaInteriorResumeReady H (job.reindex (Fin.castLE hTT) (Fin.castLE_injective hTT)) buffers
      (extendStacks hTT S) := by
  have hR (i : Fin T) : (extendStacks hTT S).R (Fin.castLE hTT i) = S.R i :=
    congrArg (fun C : Stacks T A => C.R i) (embStk_extendStacks hTT S)
  have hL (i : Fin T) : (extendStacks hTT S).L (Fin.castLE hTT i) = S.L i :=
    congrArg (fun C : Stacks T A => C.L i) (embStk_extendStacks hTT S)
  exact h.transport (job' := job.reindex (Fin.castLE hTT) (Fin.castLE_injective hTT))
    (F := extendStacks hTT S) rfl rfl (fun i _ => hR _) (fun i _ => hR _) (fun i => hL _) (hR _)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
