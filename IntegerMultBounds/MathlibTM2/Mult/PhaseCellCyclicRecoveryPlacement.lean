module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaPlacement

/-! Six new scratch tapes extend the existing cyclic caller. The native factor
bank stays at offset 600 and both cached pass banks stay in place. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicRecoveryPlacement
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

abbrev extend : Fin 834 → Fin 840 := Fin.castLE (by decide)

def bank (i : Fin 240) : Fin 840 := ⟨600+i.val,by have := i.isLt; omega⟩

theorem bank_injective : Function.Injective bank := by
  intro i j he
  have hv := congrArg (fun k : Fin 840 => k.val) he
  apply Fin.ext
  change 600+i.val = 600+j.val at hv
  omega

theorem bank_factor (i : Fin 234) :
    bank (Fin.castLE (by decide : 234 ≤ 240) i) = extend (CyclicReplicaPlacement.factorReg i) := by
  apply Fin.ext
  rfl

theorem bank_old_view {A : ℕ} (S : Stacks 840 A) :
    embStk (Fin.castLE (by decide : 234 ≤ 240)) (embStk bank S) =
      embStk CyclicReplicaPlacement.factorReg (embStk extend S) := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    change S.L (bank (Fin.castLE (by decide : 234 ≤ 240) i)) =
      S.L (extend (CyclicReplicaPlacement.factorReg i))
    rw [bank_factor]
  · funext i
    change S.R (bank (Fin.castLE (by decide : 234 ≤ 240) i)) =
      S.R (extend (CyclicReplicaPlacement.factorReg i))
    rw [bank_factor]

theorem bank_core_view {A : ℕ} (S : Stacks 840 A) :
    embStk (Fin.castLE (by decide : 224 ≤ 240)) (embStk bank S) =
      embStk (Fin.castLE (by decide : 224 ≤ 234))
        (embStk CyclicReplicaPlacement.factorReg (embStk extend S)) := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    have hi : i.val < 234 := by have := i.isLt; omega
    simpa only [embStk,Function.comp_apply,Fin.castLE] using
      congrArg S.L (bank_factor (⟨i.val,hi⟩ : Fin 234))
  · funext i
    have hi : i.val < 234 := by have := i.isLt; omega
    simpa only [embStk,Function.comp_apply,Fin.castLE] using
      congrArg S.R (bank_factor (⟨i.val,hi⟩ : Fin 234))

theorem bank_new (i : Fin 6) :
    bank ⟨234+i.val,by have := i.isLt; omega⟩ = (⟨834+i.val,by have := i.isLt; omega⟩ : Fin 840) := by
  apply Fin.ext
  change 600+(234+i.val) = 834+i.val
  omega

theorem bank_left_disjoint (i : Fin 240) (k : Fin 834) (hk : CyclicReplicaPlacement.left.Owns k) :
    bank i ≠ extend k := by
  intro he
  obtain ⟨j,hj⟩ := CachedReplicaPassPlacement.reindex_source _
    CyclicReplicaPlacement.leftReg CyclicReplicaPlacement.leftReg_injective hk
  have hv := congrArg (fun z : Fin 840 => z.val) he
  have hjv := congrArg (fun z : Fin 834 => z.val) hj
  change 600+i.val = k.val at hv
  change j.val = k.val at hjv
  have := j.isLt
  omega

theorem bank_right_disjoint (i : Fin 240) (k : Fin 834) (hk : CyclicReplicaPlacement.right.Owns k) :
    bank i ≠ extend k := by
  intro he
  obtain ⟨j,hj⟩ := CachedReplicaPassPlacement.reindex_source _
    CyclicReplicaPlacement.rightReg CyclicReplicaPlacement.rightReg_injective hk
  have hv := congrArg (fun z : Fin 840 => z.val) he
  have hjv := congrArg (fun z : Fin 834 => z.val) hj
  change 600+i.val = k.val at hv
  change 300+j.val = k.val at hjv
  have := j.isLt
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicRecoveryPlacement
