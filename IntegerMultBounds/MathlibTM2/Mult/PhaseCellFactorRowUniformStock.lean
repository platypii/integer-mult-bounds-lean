module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorRowLoopStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorWordWorkspaceBound

/-! Derive one lookup reserve for a complete descending factor-row interval. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

theorem factorRowLoop_exec_uniform_workspace {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q W start L m : ℕ)
    (depth : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat (2*q+8) columns) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (hW : (S.R 94).length = W) (hN : (S.R 116).length = B.card)
    (hcolumn : (S.R 107).length = start+L) (hrow : (S.R 108).length = m) (hcount : (S.R 105).length = L)
    (hsource : S.R 132 = bandTableWords A (2*q+8) B W columns 0++tail) (h0 : S.R 0 = []) (h106 : S.R 106 = [])
    (hfresh : ∀ k ∈ [(131 : Fin 154),134,135,136,137,138,151,152,153], S.R k = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ factorRowLoopCost q W B.card start L m ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+L*(2*q+8)+depth+factorWordUniformWorkspace q (start+L) m W B.card)
        depth factorRowLoop (mk v S) steps
        (mk v' {S with R := (Function.update (Function.update S.R 107 ((S.R 107).drop L)) 140
          (cstream A (2*q+8) ((List.range' start L).map (fun n => factorRankWord B W columns n m))++S.R 140))}) := by
  apply factorRowLoop_exec_within (body := body) B q W start L m
    (factorWordUniformWorkspace q (start+L) m W B.card) depth ?_
    columns hlen hformat hA tail v S hq hW hN hcolumn hrow hcount hsource h0 h106 hfresh hblank
  intro i hi
  exact factorWordWorkspace_le_uniform q (start+L-(i+1)) m (start+L) m W B.card
    (Nat.sub_le _ _) le_rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
