module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableRetirement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableUpdate

/-! Retire a restored input table while retaining two generated output words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {T Q A n : ℕ} {P U : Type}

theorem retireInputTable_pair_exec_within (body : P → Pr P T Q A U)
    (rg : TblR n → Fin T) (hinj : Function.Injective rg) (input : Fin n → Fin T)
    (D : ℕ) (value : Fin T → ℕ) (k l : Fin T)
    (hk : ∀ r, rg r ≠ k) (hl : ∀ r, rg r ≠ l)
    (xs ys : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ r, S.R (rg r) = []) (depth : ℕ) :
    let M := loadedInputTable rg input D value S
    let F : Stacks T A := {M with R := (Function.update (Function.update M.R k xs) l ys)}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth) depth
        (Mult.ShortConv.clearWords (inputTableWords rg)) (mk v F) ((2*n+2)*D+2*n+3)
        (mk v' {S with R := (Function.update (Function.update S.R k xs) l ys)}) := by
  have hb : ∀ r, ({S with R := Function.update S.R k xs} : Stacks T A).R (rg r) = [] := by
    intro r
    simpa only [Function.update_of_ne (hk r)] using hblank r
  obtain ⟨v',hu,he⟩ := retireInputTable_exec_within body rg hinj input D value l hl ys v
    {S with R := Function.update S.R k xs} hb depth
  rw [loadedInputTable_update_off rg input D value S k xs hk] at he
  exact ⟨v',hu,by simpa only [Nat.add_zero] using he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
