module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedWeightCache

/-! Coupling reuses the released numerical native bank. Its extended workspace
is disjoint from all retained gather metadata and reserved cache tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T T' A : ℕ}

def ReplicaInteriorPlacement.reindex (plan : ReplicaInteriorPlacement T)
    (e : Fin T → Fin T') (he : Function.Injective e) : ReplicaInteriorPlacement T' where
  gather := e ∘ plan.gather
  solver := e ∘ plan.solver
  gather_injective := he.comp plan.gather_injective
  solver_injective := he.comp plan.solver_injective
  disjoint i j h := plan.disjoint i j (he h)

structure ReplicaCouplingPlacement (plan : ReplicaInteriorPlacement T) where
  extra : Fin 51 → Fin T
  extra_injective : Function.Injective extra
  extra_gather_disjoint : ∀ i j, extra i ≠ plan.gather j
  extra_solver_disjoint : ∀ i j, extra i ≠ plan.solver j

namespace ReplicaCouplingPlacement
variable {plan : ReplicaInteriorPlacement T}

def reindex (placement : ReplicaCouplingPlacement plan)
    (e : Fin T → Fin T') (he : Function.Injective e) :
    ReplicaCouplingPlacement (plan.reindex e he) where
  extra := e ∘ placement.extra
  extra_injective := he.comp placement.extra_injective
  extra_gather_disjoint i j h := placement.extra_gather_disjoint i j (he h)
  extra_solver_disjoint i j h := placement.extra_solver_disjoint i j (he h)

def bank (placement : ReplicaCouplingPlacement plan) (i : Fin 168) : Fin T :=
  if h : i.val < 117 then plan.solver ⟨i.val,by omega⟩
  else placement.extra ⟨i.val-117,by omega⟩

@[simp] theorem reindex_bank (placement : ReplicaCouplingPlacement plan)
    (e : Fin T → Fin T') (he : Function.Injective e) (i : Fin 168) :
    (placement.reindex e he).bank i = e (placement.bank i) := by
  unfold bank
  split <;> rfl

theorem bank_injective (placement : ReplicaCouplingPlacement plan) : Function.Injective placement.bank := by
  intro i j h
  by_cases hi : i.val < 117 <;> by_cases hj : j.val < 117
  · simp only [bank,dite_eq_left hi,dite_eq_left hj] at h
    exact Fin.ext (congrArg (fun k : Fin 121 => k.val) (plan.solver_injective h))
  · simp only [bank,dite_eq_left hi,dite_eq_right hj] at h
    exact False.elim (placement.extra_solver_disjoint _ _ h.symm)
  · simp only [bank,dite_eq_right hi,dite_eq_left hj] at h
    exact False.elim (placement.extra_solver_disjoint _ _ h)
  · simp only [bank,dite_eq_right hi,dite_eq_right hj] at h
    have hv := congrArg Fin.val (placement.extra_injective h)
    apply Fin.ext
    dsimp only at hv
    omega

@[simp] theorem bank_native (placement : ReplicaCouplingPlacement plan) (i : Fin 117) :
    placement.bank (Fin.castLE (by decide) i) = plan.solver (weightCacheCoreReg i) := by
  simp [bank,i.isLt,weightCacheCoreReg]

@[simp] theorem bank_extra (placement : ReplicaCouplingPlacement plan) (i : Fin 51) :
    placement.bank ⟨117+i.val,by omega⟩ = placement.extra i := by
  simp [bank,show ¬117+i.val < 117 by omega]

theorem bank_gather_disjoint (placement : ReplicaCouplingPlacement plan) (i : Fin 168) (j : Fin 126) :
    placement.bank i ≠ plan.gather j := by
  unfold bank
  split
  · exact (plan.disjoint j _).symm
  · exact placement.extra_gather_disjoint _ j

theorem bank_reserved_disjoint (placement : ReplicaCouplingPlacement plan) (i : Fin 168)
    (j : Fin 121) (hj : 117 ≤ j.val) : placement.bank i ≠ plan.solver j := by
  unfold bank
  split
  · rename_i hi
    intro h
    have hv := congrArg Fin.val (plan.solver_injective h)
    dsimp only at hv
    omega
  · exact placement.extra_solver_disjoint _ j

theorem native_view (placement : ReplicaCouplingPlacement plan) (S : Stacks T A) :
    embStk (Fin.castLE (by decide : 117 ≤ 168)) (embStk placement.bank S) =
      embStk weightCacheCoreReg (embStk plan.solver S) := by
  refine Stacks.ext rfl rfl ?_ ?_ <;> funext i <;> simp [embStk]

theorem gather_frame (placement : ReplicaCouplingPlacement plan) (C : Stacks 168 A) (S : Stacks T A) (j : Fin 126) :
    (embOvr placement.bank C.get S).L (plan.gather j) = S.L (plan.gather j) ∧
      (embOvr placement.bank C.get S).R (plan.gather j) = S.R (plan.gather j) :=
  embOvr_off C.get S (fun i => placement.bank_gather_disjoint i j)

theorem reserved_frame (placement : ReplicaCouplingPlacement plan) (C : Stacks 168 A) (S : Stacks T A)
    (j : Fin 121) (hj : 117 ≤ j.val) :
    (embOvr placement.bank C.get S).L (plan.solver j) = S.L (plan.solver j) ∧
      (embOvr placement.bank C.get S).R (plan.solver j) = S.R (plan.solver j) :=
  embOvr_off C.get S (fun i => placement.bank_reserved_disjoint i j hj)

def standardInterior : ReplicaInteriorPlacement 300 :=
  ReplicaInteriorPlacement.standard.reindex (Fin.castLE (by decide : 247 ≤ 300)) (Fin.castLE_injective _)

def standard : ReplicaCouplingPlacement standardInterior where
  extra i := ⟨249+i.val,by omega⟩
  extra_injective := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp only at hv
    omega
  extra_gather_disjoint := by
    intro i j h
    have hv := congrArg Fin.val h
    dsimp only [standardInterior,ReplicaInteriorPlacement.reindex,ReplicaInteriorPlacement.standard,Function.comp_apply,Fin.castLE] at hv
    have hj := j.isLt
    omega
  extra_solver_disjoint := by
    intro i j h
    have hv := congrArg Fin.val h
    dsimp only [standardInterior,ReplicaInteriorPlacement.reindex,ReplicaInteriorPlacement.standard,Function.comp_apply,Fin.castLE] at hv
    have hj := j.isLt
    omega

theorem standard_outputs_disjoint (i : Fin 168) : standard.bank i ≠ 247 ∧ standard.bank i ≠ 248 := by
  have hv : (standard.bank i).val < 243 ∨ 249 ≤ (standard.bank i).val := by
    unfold bank
    split
    · left
      rename_i hi
      dsimp only [standardInterior,ReplicaInteriorPlacement.reindex,ReplicaInteriorPlacement.standard,Function.comp_apply,Fin.castLE]
      omega
    · right
      dsimp only [standard]
      omega
  constructor <;> intro h <;> have he := congrArg Fin.val h <;> norm_num at he <;> omega

end ReplicaCouplingPlacement
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
