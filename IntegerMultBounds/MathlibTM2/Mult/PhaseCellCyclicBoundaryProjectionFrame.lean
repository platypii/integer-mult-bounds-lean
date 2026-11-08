module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryProjectionFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaConsumerExport

/-! Structural projection-frame bookkeeping for arbitrary exported rows and
solved bytes. Numerical factor/solve terms are instantiated only afterward. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open CyclicReplicaPlacement
variable {A : ℕ}

theorem cyclicReplicaConsumerExportState_left (S : Stacks 834 A) (rows : List (Fin (A+4))) :
    (embStk factorReg (cyclicReplicaConsumerExportState S rows)).L = (embStk factorReg S).L := by
  have h := congrArg (fun F : Stacks 234 A => F.L) (cyclicReplicaConsumerExportState_factor S rows)
  simpa only [exportedCyclicResidualRows,cyclicReplicaConsumerState,cyclicReplicaArchiveHandoffState,
    cyclicReplicaConsumerHeaderState,embStk] using h

theorem cyclicReplicaConsumerExportState_high_read (S : Stacks 834 A) (rows : List (Fin (A+4)))
    (i : Fin 234) (hi : 227 ≤ i.val) (h229 : i ≠ 229) :
    (cyclicReplicaConsumerExportState S rows).R (factorReg i) = S.R (factorReg i) := by
  have h226 : i ≠ 226 := by
    intro he
    have hv := congrArg (fun k : Fin 234 => k.val) he
    change i.val = 226 at hv
    omega
  have hret : i ∉ cyclicResidualRowsRetired := by
    intro hm
    simp only [cyclicResidualRowsRetired,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at hi
  have hc : i ∉ [(130 : Fin 234),168,169,171,172,229] := by
    intro hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | he
    · norm_num at hi
    · norm_num at hi
    · norm_num at hi
    · norm_num at hi
    · norm_num at hi
    · exact h229 he
  have hh := congrArg (fun F : Stacks 234 A => F.R i) (cyclicReplicaConsumerExportState_factor S rows)
  have hread : (cyclicReplicaConsumerExportState S rows).R (factorReg i) =
      (cyclicReplicaConsumerState S).R (factorReg i) := by
    simpa only [embStk,Function.comp_apply,exportedCyclicResidualRows,ite_eq_right hret,Function.update_of_ne h226] using hh
  exact hread.trans (cyclicReplicaConsumerState_factor_read S i hc)

theorem boundaryProjectionFrame_of_export (replicas : ℕ) (S : Stacks 834 A) (raw page : Stacks 234 A)
    (rows solved : List (Fin (A+4)))
    (hleftRaw : ∀ i : Fin 224, raw.L (Fin.castLE (by decide) i) = [])
    (hfreshRaw : ∀ i ∈ [(227 : Fin 234),228,231,232,233], raw.R i = [])
    (hL : (embStk factorReg S).L = raw.L)
    (hR : ∀ i : Fin 234, i ≠ 170 → i ≠ 173 → S.R (factorReg i) = raw.R i)
    (hpageL : page.L = (embStk factorReg (cyclicReplicaConsumerExportState S rows)).L)
    (hprivate : ∀ i : Fin 234, 226 ≤ i.val →
      page.R i = (embStk factorReg (cyclicReplicaConsumerExportState S rows)).R i)
    (hreplicas : (cyclicReplicaConsumerExportState S rows).R (factorReg 229) = List.replicate replicas tick) :
    BoundaryProjectionFrame replicas {page with R := Function.update page.R 224 solved} := by
  refine ⟨?_,?_,?_⟩
  · intro i
    change page.L (Fin.castLE (by decide : 224 ≤ 234) i) = []
    rw [hpageL,cyclicReplicaConsumerExportState_left,hL]
    exact hleftRaw i
  · change (Function.update page.R 224 solved (229 : Fin 234)).length = replicas
    rw [Function.update_of_ne (by decide : (229 : Fin 234) ≠ 224),hprivate 229 (by decide)]
    change ((cyclicReplicaConsumerExportState S rows).R (factorReg 229)).length = replicas
    rw [hreplicas,List.length_replicate]
  · intro i hi
    have hvals : 227 ≤ i.val ∧ i ≠ 224 ∧ i ≠ 229 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
    have hoff (k : Fin 234) (hk : k.val < 227) : i ≠ k := by
      intro he
      have hv := congrArg (fun j : Fin 234 => j.val) he
      omega
    change Function.update page.R 224 solved i = []
    rw [Function.update_of_ne hvals.2.1,hprivate i (by omega)]
    change (cyclicReplicaConsumerExportState S rows).R (factorReg i) = []
    rw [cyclicReplicaConsumerExportState_high_read S rows i hvals.1 hvals.2.2,
      hR i (hoff 170 (by decide)) (hoff 173 (by decide))]
    exact hfreshRaw i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
