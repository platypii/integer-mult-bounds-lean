module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFoldReplicaBoundaryRhs

/-! Retain fold counters outside native multiplier scratch. All other low-bank
roles, including the folded RHS and geometry, keep their existing positions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

def replicaBoundaryFoldPermutation : Equiv.Perm (Fin 168) :=
  (Equiv.swap 3 120).trans ((Equiv.swap 2 118).trans (Equiv.swap 0 117))

def replicaBoundaryFoldBank (i : Fin 168) : Fin 242 :=
  Fin.castLE (by decide) (replicaBoundaryFoldPermutation i)

theorem replicaBoundaryFoldBank_injective : Function.Injective replicaBoundaryFoldBank := by
  intro i j he
  apply replicaBoundaryFoldPermutation.injective
  exact Fin.ext (congrArg (fun k : Fin 242 => k.val) he)

theorem replicaBoundaryFoldBank_fixed (i : Fin 168)
    (hi : i ∉ [0,2,3,117,118,120]) :
    replicaBoundaryFoldBank i = Fin.castLE (by decide) i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
  simp [replicaBoundaryFoldBank,replicaBoundaryFoldPermutation,Equiv.trans_apply,
    Equiv.swap_apply_def,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,hi.2.2.2.2.1,hi.2.2.2.2.2]

theorem replicaBoundaryFoldBank_scratch (i : Fin 168) (h6 : 6 ≤ i.val) (h77 : i.val < 77) :
    replicaBoundaryFoldBank i = Fin.castLE (by decide) i := by
  apply replicaBoundaryFoldBank_fixed
  simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
  norm_num
  omega

@[simp] theorem replicaBoundaryFoldBank_floor : replicaBoundaryFoldBank 0 = 117 := by decide
@[simp] theorem replicaBoundaryFoldBank_parity : replicaBoundaryFoldBank 2 = 118 := by decide
@[simp] theorem replicaBoundaryFoldBank_bytes : replicaBoundaryFoldBank 3 = 120 := by decide

theorem replicaBoundaryFoldBank_ne_archive (i : Fin 168) : replicaBoundaryFoldBank i ≠ 238 := by
  intro he
  have hi := (replicaBoundaryFoldPermutation i).isLt
  have hv := congrArg Fin.val he
  change (replicaBoundaryFoldPermutation i).val = 238 at hv
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
