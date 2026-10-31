module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTilePlan

/-! Loading an owned payload preserves all transpose metadata. This is the
handoff from the producer's computed result bank to the archive tile executor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ArchiveTilePlan
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {t₀ T Q c d W K N : ℕ}

theorem BankReady.source_update {plan : ArchiveTilePlan t₀ T Q c d W} {S : Stacks T (prime+K)}
    (h : plan.BankReady S) (raw : List (Fin (prime+K+4))) :
    plan.BankReady {S with R := Function.update S.R plan.src raw} := by
  let M : Stacks T (prime+K) := {S with R := Function.update S.R plan.src raw}
  have hr := plan.hreg
  regs_ne hr
  have hcontrols (i : Fin T)
      (hi : i ∈ [plan.base,plan.one,plan.width,plan.exponent,plan.powTmp,plan.powSaved,plan.a,plan.half,plan.par,plan.bits,plan.cnt,plan.work]) :
      M.R i = S.R i := by simp [M,plan.hsourceControls i hi]
  have hbank (j : Fin (swapT t₀)) : M.R (plan.ι j) = S.R (plan.ι j) := by simp [M,plan.hsourceOff j]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,h.hL,?_,?_,?_,?_,?_,?_⟩
  · rw [hcontrols _ (by simp)]; exact h.hbase
  · rw [hcontrols _ (by simp)]; exact h.hone
  · rw [hcontrols _ (by simp)]; exact h.hwidth
  · rw [hcontrols _ (by simp)]; exact h.hexponent
  · intro i hi
    have hne : i ≠ plan.src := by intro he; subst i; exact plan.hsourceBank hi
    simpa only [Function.update_of_ne hne] using h.hblank i hi
  · rw [hcontrols _ (by simp)]; exact h.htmp
  · rw [hcontrols _ (by simp)]; exact h.hsaved
  · intro j hj; rw [hbank]; exact h.hpriv j hj
  · intro k; rw [hbank]; exact h.hhdr k
  · intro i hi
    have hm : i ∈ [plan.base,plan.one,plan.width,plan.exponent,plan.powTmp,plan.powSaved,plan.a,plan.half,plan.par,plan.bits,plan.cnt,plan.work] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    rw [hcontrols i hm]; exact h.hgenBlank i hi
  · simpa only [Function.update_of_ne ‹plan.src ≠ plan.count›.symm] using h.hcount
  · intro i hi
    have he : M.R i = S.R i := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hbank _
      · exact hbank _
      · simp [M,‹plan.src ≠ plan.tmp›.symm]
      · simp [M,‹plan.src ≠ plan.saved›.symm]
      · simp [M,‹plan.src ≠ plan.reRev›.symm]
      · simp [M,‹plan.src ≠ plan.imRev›.symm]
    rw [he]; exact h.hcodecBlank i hi
  · intro i hre him hhd
    rw [hbank]
    exact h.hother i hre him hhd

theorem BankReady.ready_source {plan : ArchiveTilePlan t₀ T Q c d W} {S : Stacks T (prime+K)}
    (h : plan.BankReady S) (w : ℕ) (rows : Fin N → Fin (2^d) → List GaussianInt) :
    plan.Ready w rows {S with R := (Function.update S.R plan.src
      ((List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) w (rows i j)).flatten).flatten))} :=
  ⟨h.source_update _,by simp⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ArchiveTilePlan
