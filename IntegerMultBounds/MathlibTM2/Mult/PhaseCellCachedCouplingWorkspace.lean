module

public import IntegerMultBounds.MathlibTM2.Host.Embed
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCouplingOperands
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedCouplingRow

/-! Keep a captured ambient source outside the coupling arithmetic register file. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

def cachedCouplingCoreReg (i : Fin 117) : Fin 118 := ⟨i.val,by omega⟩

def cachedCouplingLookupReg (i : Fin 117) : Fin 118 :=
  if i = 92 then 117 else cachedCouplingCoreReg i

theorem cachedCouplingCoreReg_injective : Function.Injective cachedCouplingCoreReg := by
  intro i j he
  exact Fin.ext (congrArg (fun k : Fin 118 => k.val) he)

theorem cachedCouplingCoreReg_off (i : Fin 117) : cachedCouplingCoreReg i ≠ 117 := by
  intro he
  have hv := congrArg (fun k : Fin 118 => k.val) he
  change i.val = 117 at hv
  have hi := i.isLt
  omega

theorem cachedCouplingLookupReg_injective : Function.Injective cachedCouplingLookupReg := by
  intro i j he
  by_cases hi : i = 92 <;> by_cases hj : j = 92
  · exact hi.trans hj.symm
  · simp only [cachedCouplingLookupReg,hi,hj,ite_true,ite_false] at he
    exact False.elim (cachedCouplingCoreReg_off j he.symm)
  · simp only [cachedCouplingLookupReg,hi,hj,ite_true,ite_false] at he
    exact False.elim (cachedCouplingCoreReg_off i he)
  · simp only [cachedCouplingLookupReg,hi,hj,ite_false] at he
    exact cachedCouplingCoreReg_injective he

theorem cachedCouplingLookupReg_ne_source (i : Fin 117) : cachedCouplingLookupReg i ≠ 92 := by
  by_cases hi : i = 92
  · simp [cachedCouplingLookupReg,hi]
  · have hn : cachedCouplingCoreReg i ≠ 92 := cachedCouplingCoreReg_injective.ne hi
    simpa only [cachedCouplingLookupReg,hi,ite_false] using hn

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
