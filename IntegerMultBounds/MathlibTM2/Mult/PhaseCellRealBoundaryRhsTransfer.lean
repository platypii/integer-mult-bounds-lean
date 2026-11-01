module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakeMappedPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealPrefix

/-! Project and route the folded boundary RHS in one restoring transfer.
The retained boundary-symbol count is shared by all replica rows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def realBoundaryRhsTransfer (volume src dst saved tmp : Fin T) : Pr P T Q A U :=
  takeMappedPrefix volume src dst saved tmp realPartSymbol

theorem realBoundaryRhsTransfer_exec (volume src dst saved tmp : Fin T)
    (hreg : [volume,src,dst,saved,tmp].Nodup) (hA : 4 ≤ A) (w : ℕ) (xs : List GaussianInt)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hvolume : (S.R volume).length = xs.length*w) (hsrc : S.R src = cstream A w xs++tail)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (realBoundaryRhsTransfer volume src dst saved tmp) (mk v S) (6*(xs.length*w)+6)
        (mk v' {S with R := (Function.update (Function.update S.R src tail) dst
          (cstream A w (xs.map realPartWord)++S.R dst))}) := by
  obtain ⟨v',hu,he⟩ := takeMappedPrefix_exec (body := body) hreg realPartSymbol v S
    (cstream A w xs) tail hsrc (by simpa using hvolume) hsaved htmp
  exact ⟨v',hu,by simpa only [realBoundaryRhsTransfer,length_cstream,realPartSymbol_cstream hA] using he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
