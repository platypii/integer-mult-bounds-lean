module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedBoundaryRhsFold
public import IntegerMultBounds.MathlibTM2.Host.StackFrame

/-! The existing numerical fold preserves arbitrary left-bank spectators. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- This footprint proof depends on the fold structure, not any geometry or data. -/
theorem bandFoldLineP_nonLeft {T Q A : ℕ} {P U : Type} (rg : RsbR → Fin T) :
    programOn nonLeft (bandFoldLineP (P := P) (Q := Q) (A := A) (U := U) rg) := by
  simp [bandFoldLineP,bandRec1P,bandILeaveP,bandRevP,rsbRep,rsbScanIf,rsbMv,
    rsbMvTop,scanR,drainR,keepIn,popDo,moveR,whileR,moveStep,peekR,popPush,programOn,actionOn,nonLeft]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 148 Q A U}

theorem framedBoundaryRhsFold_exec (s : ℕ) [NeZero s] (B : Finset (ZMod s))
    (C : ZMod s → GaussianInt) (w : ℕ) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hsource : S.R 143 = cstream A w ((bOrder s B).map C))
    (hwidth : (S.R 94).length = w) (hcount : (S.R 116).length = B.card)
    (hfloor : (S.R 0).length = B.card/2)
    (hparity : (S.R 2).length = (B.card+1)/2-B.card/2)
    (hbytes : (S.R 3).length = (B.card+1)/2*w)
    (hblank : ∀ r : Fin 148, 6 ≤ r.val → r.val < 77 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 60*(B.card+1)*w+60*B.card+60 ∧
      Exec body retainedBoundaryRhsFold (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 143 [])
          6 (cstream A w ((bFoldOrder s B).map C)))}) := by
  let S₀ : Stacks 148 A := {S with L := fun _ => []}
  obtain ⟨v',m,hu,hm,he⟩ := retainedBoundaryRhsFold_exec (body := body) s B C w v S₀
    hsource hwidth hcount hfloor hparity hbytes hblank (by intro r; rfl)
  have hf := exec_withLeft he (bandFoldLineP_nonLeft BoundaryRhsFoldPlacement.reg) S.L
  exact ⟨v',m,hu,hm,hf⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
