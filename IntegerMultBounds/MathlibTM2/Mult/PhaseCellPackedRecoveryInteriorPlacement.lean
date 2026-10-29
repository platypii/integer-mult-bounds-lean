module

public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Reuse the packed interior solver beside the first pass's retained headers
and coefficient page. Six fresh ports hold its private runtime roles. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

def packedRecoveryInteriorPerm : Equiv (Fin 248) (Fin 248) :=
  (Equiv.swap 125 242).trans ((Equiv.swap 128 243).trans
    ((Equiv.swap 130 244).trans ((Equiv.swap 138 245).trans
      ((Equiv.swap 140 246).trans (Equiv.swap 157 247)))))

def packedRecoveryInteriorReg (i : Fin 168) : Fin 248 :=
  packedRecoveryInteriorPerm ⟨i.val,by omega⟩

theorem packedRecoveryInteriorReg_injective : Function.Injective packedRecoveryInteriorReg := by
  intro i j h
  have hh := packedRecoveryInteriorPerm.injective h
  exact Fin.ext (congrArg (fun k : Fin 248 => k.val) hh)

theorem packedRecoveryInteriorReg_low (i : Fin 168) (hi : i.val < 117) :
    packedRecoveryInteriorReg i = ⟨i.val,by omega⟩ := by
  have hne (n : ℕ) (hn : 117 ≤ n) : i.val ≠ n := by omega
  simp [packedRecoveryInteriorReg,packedRecoveryInteriorPerm,Equiv.swap_apply_def,
    Fin.ext_iff,hne 125 (by decide),hne 242 (by decide),hne 128 (by decide),hne 243 (by decide),hne 130 (by decide),hne 244 (by decide),hne 138 (by decide),hne 245 (by decide),hne 140 (by decide),hne 246 (by decide),hne 157 (by decide),hne 247 (by decide)]

theorem packedRecoveryInteriorReg_fixed (i : Fin 168)
    (hn : i ∉ ([125,128,130,138,140,157] : List (Fin 168))) :
    packedRecoveryInteriorReg i = ⟨i.val,by omega⟩ := by
  have hi := i.isLt
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or,Fin.ext_iff] at hn
  norm_num at hn
  simp [packedRecoveryInteriorReg,packedRecoveryInteriorPerm,Equiv.swap_apply_def,Fin.ext_iff,
    hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,hn.2.2.2.2.2,
    show i.val ≠ 242 by omega,
    show i.val ≠ 243 by omega,
    show i.val ≠ 244 by omega,
    show i.val ≠ 245 by omega,
    show i.val ≠ 246 by omega,
    show i.val ≠ 247 by omega]

@[simp] theorem packedRecoveryInteriorReg_125 : packedRecoveryInteriorReg 125 = 242 := by decide

@[simp] theorem packedRecoveryInteriorReg_128 : packedRecoveryInteriorReg 128 = 243 := by decide

@[simp] theorem packedRecoveryInteriorReg_130 : packedRecoveryInteriorReg 130 = 244 := by decide

@[simp] theorem packedRecoveryInteriorReg_138 : packedRecoveryInteriorReg 138 = 245 := by decide

@[simp] theorem packedRecoveryInteriorReg_140 : packedRecoveryInteriorReg 140 = 246 := by decide

@[simp] theorem packedRecoveryInteriorReg_157 : packedRecoveryInteriorReg 157 = 247 := by decide

private theorem packedRecoveryInteriorReg_inverse (i : Fin 168) (k : Fin 248)
    (h : packedRecoveryInteriorReg i = k) : i.val = (packedRecoveryInteriorPerm.symm k).val := by
  have hh := congrArg packedRecoveryInteriorPerm.symm h
  simp only [packedRecoveryInteriorReg,Equiv.symm_apply_apply] at hh
  exact congrArg (fun j : Fin 248 => j.val) hh

/-- The old runtime roles are retained, not cleared or copied. -/
theorem packedRecoveryInteriorReg_avoids_retained (i : Fin 168) (k : Fin 248)
    (hk : k ∈ ([125,128,130,138,140,157] : List (Fin 248))) : packedRecoveryInteriorReg i ≠ k := by
  intro he
  have hh := packedRecoveryInteriorReg_inverse i k he
  have hi := i.isLt
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals (change i.val = _ at hh; norm_num [packedRecoveryInteriorPerm,Equiv.swap_apply_def] at hh; omega)

/-- The numerical factor bank between the local and fresh banks is untouched. -/
theorem packedRecoveryInteriorReg_avoids_factors (i : Fin 168) (k : Fin 248)
    (hk : 168 ≤ k.val) (hk' : k.val < 242) : packedRecoveryInteriorReg i ≠ k := by
  intro he
  have hh := packedRecoveryInteriorReg_inverse i k he
  have hi := i.isLt
  have hne (n : ℕ) (hn : n < 168 ∨ 242 ≤ n) : k.val ≠ n := by omega
  have hfix : packedRecoveryInteriorPerm.symm k = k := by
    simp [packedRecoveryInteriorPerm,Equiv.swap_apply_def,Fin.ext_iff,
      hne 125 (by decide),
      hne 128 (by decide),
      hne 130 (by decide),
      hne 138 (by decide),
      hne 140 (by decide),
      hne 157 (by decide),
      hne 242 (by decide),
      hne 243 (by decide),
      hne 244 (by decide),
      hne 245 (by decide),
      hne 246 (by decide),
      hne 247 (by decide)]
  rw [hfix] at hh
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
