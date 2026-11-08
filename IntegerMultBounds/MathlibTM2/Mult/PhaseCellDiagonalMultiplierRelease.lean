module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalMultiplierFromUnary
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseScalarBank
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock

/-! Retire the temporary scalar variables after ordinary multiplier setup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
noncomputable section
variable {Q A : ℕ} {P U : Type} {body : P → Pr P tapes Q A U}

def diagonalMultiplierFinished (header word saved tmp carry : Fin tapes) : Pr P tapes Q A U :=
  .seq (diagonalMultiplierFromUnary header word saved tmp carry) (releaseScalarBank diagonalMultiplierTable)

theorem diagonalMultiplierFinished_native (header word saved tmp carry : Fin tapes) :
    mnNativePushBound 3 (diagonalMultiplierFinished (P := P) (Q := Q) (A := A) (U := U) header word saved tmp carry) :=
  ⟨diagonalMultiplierFromUnary_native ..,mnNativePushBound_mono (by decide : 0 ≤ 3)
    (ShortConv.clearWords_native _)⟩

theorem diagonalCounter_off_table (p w : ℕ) (R : Regs tapes A) (r : TblR 5) :
    diagonalCounterR p w R (diagonalMultiplierTable r) = R (diagonalMultiplierTable r) :=
  chirpMultiplierSetup_off diagonalCr R p w _ (diagonalTable_ne_role _ (.cm .wn))
    (diagonalTable_ne_role _ (.cm .pn)) (diagonalTable_ne_role _ (.cm .nn))

theorem diagonalMultiplierFinished_exec (header word saved tmp carry : Fin tapes)
    (hheader : ∀ r, diagonalMultiplierTable r ≠ header)
    (hregs : ∀ src ∈ diagonalMultiplierInputs.map Prod.snd,
      [src,diagonalMultiplierTable .wr,word,saved,tmp,header].Nodup)
    (B p w : ℕ) (hpw : p ≤ w) (hw : 1 ≤ w) (hroom : 4*w+2 < 2^B)
    (wl : List (Fin (A+4))) (hwl : wl.length = B) (v : HS tapes Q A U) (S : Stacks tapes A)
    (hp : (S.R (recovery (.control .precision))).length = p)
    (hwide : (S.R (recovery (.control .packet))).length = w)
    (hwidth : S.R (diagonalMultiplierTable .wr) = wl)
    (hblank : ∀ r : TblR 5, r ≠ .wr → S.R (diagonalMultiplierTable r) = [])
    (hwork : ∀ k ∈ [word,saved,tmp], S.R k = []) (hcm : ∀ c : CR, S.R (diagonalCr c) = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ diagonalMultiplierFromUnaryCost B p w+(2*(5*B)+11) ∧
      Exec body (diagonalMultiplierFinished header word saved tmp carry) (Host.mk v S) steps
        (Host.mk v' {S with R := diagonalCounterR p w S.R}) ∧
      (∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        3*(diagonalMultiplierFromUnaryCost B p w+(2*(5*B)+11))) depth
        (diagonalMultiplierFinished header word saved tmp carry) (Host.mk v S) steps
        (Host.mk v' {S with R := diagonalCounterR p w S.R})) ∧
      RsbReady (fun r => diagonalCounterR p w S.R (diagonalRole r)) w p := by
  obtain ⟨v₁,M,steps₁,hu₁,hn₁,he₁,_,hhM,_,hin,hout,hL,hframe⟩ :=
    diagonalMultiplierFromUnary_exec (body := body) header word saved tmp carry hheader hregs B p w hpw hw hroom
      wl hwl v S hp hwide hwidth hblank hwork hcm
  let st : TblSt 5 A := loadedBinaryState [(0,p),(1,w)] ⟨fun _ => 0,[]⟩
  let F : Stacks tapes A := {M with R := diagonalCounterR p w M.R}
  let G : Stacks tapes A := {S with R := diagonalCounterR p w S.R}
  have hhF : tblHolds diagonalMultiplierTable F (tblRho B wl [] st) := by
    intro r
    exact (diagonalCounter_off_table p w M.R r).trans (hhM r)
  have hframeCounter k (hoff : ∀ r, diagonalMultiplierTable r ≠ k) : F.R k = G.R k := by
    apply unaryCopiesR_congr_base
    · intro a ha
      simp only [chirpMultiplierAssignments,List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl <;> exact hframe _ (fun r => diagonalTable_ne_role _ _)
    · exact hframe k hoff
  obtain ⟨v₂,hu₂,he₂⟩ := releaseScalarBank_to_state_exec (body := body) diagonalMultiplierTable diagonalMultiplierTable_injective
    B wl st (loadedBinaryState_acc _ _) v₁ F G hhF
    ((diagonalCounter_off_table p w S.R .wr).trans hwidth)
    (fun r hr => (diagonalCounter_off_table p w S.R r).trans (hblank r hr)) hin hout hL hframeCounter
  have hn : steps₁+(2*(5*B)+11) ≤ diagonalMultiplierFromUnaryCost B p w+(2*(5*B)+11) :=
    Nat.add_le_add_right hn₁ _
  have hex : Exec body (diagonalMultiplierFinished header word saved tmp carry) (Host.mk v S)
      (steps₁+(2*(5*B)+11)) (Host.mk v₂ G) := (Exec.seq he₁ he₂).cast (by omega) rfl
  exact ⟨v₂,_,hu₂.trans hu₁,hn,hex,fun depth =>
    mn_native_exec_within hex 3 (diagonalMultiplierFinished_native ..) depth _ (by omega),
    diagonalCounter_ready p w S.R hcm⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
