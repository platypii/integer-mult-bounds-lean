module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalMultiplierBorrowed
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalFreshBank

/-! Fixed conversion ports and fresh-bank specialization of multiplier setup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
noncomputable section
variable {Q A : ℕ} {P U : Type} {body : P → Pr P tapes Q A U}

def diagonalWidthSource : Fin tapes := recovery (.scalar .wr)
def diagonalHeader : Fin tapes := recovery (.work 304)
def diagonalWord : Fin tapes := recovery (.work 305)
def diagonalConvertSaved : Fin tapes := recovery (.work 306)
def diagonalConvertTmp : Fin tapes := recovery (.work 307)
def diagonalCarry : Fin tapes := recovery (.work 308)

theorem diagonal_width_regs : [diagonalWidthSource,diagonalMultiplierTable .wr,diagonalConvertTmp].Nodup := by
  have ht := diagonalTable_ne_work (TblR.wr : TblR 48) 307 (by decide)
  have hs : diagonalWidthSource ≠ diagonalMultiplierTable .wr := by
    simp [diagonalWidthSource,diagonalMultiplierTable,diagonalTable,recovery_injective.eq_iff]
  have hx : diagonalWidthSource ≠ diagonalConvertTmp := by
    simp [diagonalWidthSource,diagonalConvertTmp,recovery_injective.eq_iff]
  regs_nodup

theorem diagonal_conversion_regs : ∀ src ∈ diagonalMultiplierInputs.map Prod.snd,
    [src,diagonalMultiplierTable .wr,diagonalWord,diagonalConvertSaved,diagonalConvertTmp,diagonalHeader].Nodup := by
  intro src hsrc
  have ht304 := diagonalTable_ne_work (TblR.wr : TblR 48) 304 (by decide)
  have ht305 := diagonalTable_ne_work (TblR.wr : TblR 48) 305 (by decide)
  have ht306 := diagonalTable_ne_work (TblR.wr : TblR 48) 306 (by decide)
  have ht307 := diagonalTable_ne_work (TblR.wr : TblR 48) 307 (by decide)
  have hwork : [diagonalWord,diagonalConvertSaved,diagonalConvertTmp,diagonalHeader].Nodup := by
    simp [diagonalWord,diagonalConvertSaved,diagonalConvertTmp,diagonalHeader,recovery_injective.eq_iff]
  regs_ne hwork
  simp only [diagonalMultiplierInputs,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hsrc
  rcases hsrc with hsrc | hsrc <;> subst src
  all_goals
    have htable (c : RecoveryControl) : recovery (.control c) ≠ diagonalMultiplierTable .wr := by
      simp [diagonalMultiplierTable,diagonalTable,recovery_injective.eq_iff]
    have hword (c : RecoveryControl) : recovery (.control c) ≠ diagonalWord := by simp [diagonalWord,recovery_injective.eq_iff]
    have hsaved (c : RecoveryControl) : recovery (.control c) ≠ diagonalConvertSaved := by simp [diagonalConvertSaved,recovery_injective.eq_iff]
    have htmp (c : RecoveryControl) : recovery (.control c) ≠ diagonalConvertTmp := by simp [diagonalConvertTmp,recovery_injective.eq_iff]
    have hhead (c : RecoveryControl) : recovery (.control c) ≠ diagonalHeader := by simp [diagonalHeader,recovery_injective.eq_iff]
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,and_true,not_false_eq_true,←ne_eq]
    and_intros <;> first | assumption | exact Ne.symm (by assumption) | exact htable _ | exact hword _ | exact hsaved _ | exact htmp _ | exact hhead _

def diagonalMultiplierLocal : Pr P tapes Q A U :=
  diagonalMultiplierBorrowed diagonalWidthSource diagonalHeader diagonalWord diagonalConvertSaved diagonalConvertTmp diagonalCarry

theorem diagonalMultiplierLocal_exec (B p w : ℕ) (hpw : p ≤ w) (hw : 1 ≤ w) (hroom : 4*w+2 < 2^B)
    (v : HS tapes Q A U) (S : Stacks tapes A) (hB : (S.R diagonalWidthSource).length = B)
    (hp : (S.R (recovery (.control .precision))).length = p)
    (hwide : (S.R (recovery (.control .packet))).length = w) (hfresh : DiagonalFresh S) :
    let cost := diagonalMultiplierFromUnaryCost B p w+(2*(5*B)+11)
    ∃ v' steps, v'.user = v.user ∧ steps ≤ (4*B+4)+cost+(2*B+2) ∧
      (∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        (2*(4*B+4)+3*cost)) depth diagonalMultiplierLocal (Host.mk v S) steps
        (Host.mk v' {S with R := diagonalCounterR p w S.R})) ∧
      RsbReady (fun r => diagonalCounterR p w S.R (diagonalRole r)) w p := by
  exact diagonalMultiplierBorrowed_exec (body := body) _ _ _ _ _ _ diagonal_width_regs
    (fun r => diagonalTable_ne_work _ 304 (by decide)) diagonal_conversion_regs B p w hpw hw hroom v S hB hp hwide
    (fun r => hfresh.table _) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with hk | hk | hk <;> subst k <;> exact hfresh.work _) (fun c => hfresh.role (.cm c))

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
