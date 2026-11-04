module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableUpdate
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyWordHeaders

/-! Independent format exports and numerical-table loading have the same
endpoint in either order. Prove this over the copy list, not concrete banks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T A n : ℕ}

theorem loadedInputTable_copyWordHeaders (rg : TblR n → Fin T) (input : Fin n → Fin T)
    (D : ℕ) (value : Fin T → ℕ) (words : Fin T → List (Fin (A+4)))
    (rs : List (Fin T × Fin T)) (S : Stacks T A)
    (hoff : ∀ p ∈ rs, ∀ r, rg r ≠ p.2) :
    loadedInputTable rg input D value {S with R := copyWordHeadersR words rs S.R} =
      {loadedInputTable rg input D value S with R :=
        (copyWordHeadersR words rs (loadedInputTable rg input D value S).R)} := by
  induction rs generalizing S with
  | nil => rfl
  | cons p ps ih =>
    let M : Stacks T A := {S with R := Function.update S.R p.2 (words p.1++S.R p.2)}
    have htail := ih M (by intro q hq; exact hoff q (by simp [hq]))
    have hhead := loadedInputTable_update_off rg input D value S p.2
      (words p.1++S.R p.2) (hoff p (by simp))
    have hread := loadedInputTable_off rg input D value S p.2 (fun r => (hoff p (by simp) r).symm)
    change loadedInputTable rg input D value {M with R := copyWordHeadersR words ps M.R} = _
    rw [htail]
    change {loadedInputTable rg input D value M with R :=
      (copyWordHeadersR words ps (loadedInputTable rg input D value M).R)} = _
    rw [show loadedInputTable rg input D value M = _ from hhead]
    simp only [copyWordHeadersR,hread]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
