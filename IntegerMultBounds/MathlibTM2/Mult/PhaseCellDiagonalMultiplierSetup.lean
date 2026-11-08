module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalDiagonalLayout
public import IntegerMultBounds.MathlibTM2.Mult.ChirpMultiplierSetup

/-! Reuse the computed multiplier-header setup in the fixed diagonal allocation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
noncomputable section
variable {Q A : ℕ} {P U : Type} {body : P → Pr P tapes Q A U}

def diagonalMultiplierTable (r : TblR 5) : Fin tapes :=
  diagonalTable (r.rename (Fin.castLE (by decide : 5 ≤ 48)))
def diagonalCr (c : CR) : Fin tapes := diagonalRole (.cm c)

theorem diagonalMultiplierTable_injective : Function.Injective diagonalMultiplierTable :=
  diagonalTable_injective.comp (TblR.rename_injective (by intro i j h; have hh := congrArg (fun k : Fin 48 => k.val) h; exact Fin.ext hh))
theorem diagonalCr_injective : Function.Injective diagonalCr := by
  intro c d h; exact RsbR.cm.inj (diagonalRole_injective h)

def diagonalMultiplierSetup : Pr P tapes Q A U := chirpMultiplierSetup diagonalMultiplierTable diagonalCr

def diagonalCounterR {A : ℕ} (p w : ℕ) (R : Regs tapes A) : Regs tapes A :=
  unaryCopiesR (chirpMultiplierDimensionValues p w) R (chirpMultiplierAssignments diagonalCr)

theorem diagonalCounter_ready (p w : ℕ) (R : Regs tapes A)
    (hblank : ∀ c : CR, R (diagonalCr c) = []) :
    RsbReady (fun r => diagonalCounterR p w R (diagonalRole r)) w p := by
  have hc := chirpMultiplierSetup_ready diagonalCr diagonalCr_injective R p w (fun c _ => hblank c)
  refine ⟨hc.wn,hc.pn,hc.nn,?_⟩
  intro c hxs hys hout hwn hpn hnn
  cases c <;> simp_all [diagonalCounterR,unaryCopiesR,chirpMultiplierAssignments,
    chirpMultiplierDimensionValues,diagonalCr,diagonalRole_injective.eq_iff]

theorem diagonalMultiplierSetup_exec {B e p w : ℕ}
    (wl nl : List (Fin (A+4))) (hwl : wl.length = B) (hnl : nl.length = e) (heB : e ≤ B)
    (st : TblSt 5 A) (hp : st.val 0 = p) (hw : st.val 1 = w) (hw1 : 1 ≤ w)
    (hroom : 4*w+2 < 2^B) (hzero : ∀ i : Fin 5, 2 ≤ i.val → st.val i = 0)
    (hfit : ∀ i, st.val i < 2^B) (v : HS tapes Q A U) (S : Stacks tapes A)
    (hS : tblHolds diagonalMultiplierTable S (tblRho B wl nl st))
    (hblank : ∀ c : CR, S.R (diagonalCr c) = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ chirpMultiplierSetupCost B e p w ∧
      Exec body diagonalMultiplierSetup (Host.mk v S) steps
        (Host.mk v' {S with R := diagonalCounterR p w S.R}) ∧
      RsbReady (fun r => diagonalCounterR p w S.R (diagonalRole r)) w p := by
  obtain ⟨v',steps,hu,hn,he⟩ := chirpMultiplierSetup_exec (body := body) diagonalMultiplierTable_injective diagonalCr
    (by intro c _ i; exact diagonalTable_ne_role _ (.cm c)) wl nl hwl hnl heB st p w hp hw hw1 hroom hzero hfit v S hS
  exact ⟨v',steps,hu,hn,he,diagonalCounter_ready p w S.R hblank⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
