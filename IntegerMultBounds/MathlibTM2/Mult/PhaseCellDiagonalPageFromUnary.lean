module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalPageLoading

/-! Generate the shared diagonal page from ordinary unary geometry inputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM
noncomputable section
variable {Q A : ℕ} {P U : Type} {body : P → Pr P tapes Q A U}

def diagonalPageFromUnary : Pr P tapes Q A U :=
  .seq loadDiagonalPageInputs (.seq installDiagonalStreamWidth
    (ownedDiagonalPage diagonalTable (diagonalRole .df)))

def diagonalPageFromUnaryCost (R : Regs tapes A) (p w u t n : ℕ) : ℕ :=
  let B := diagonalPageWidth p w u t
  binaryHeaderQueueCost R B (diagonalPageInputs.map Prod.snd)+48*(4*B+4)+6*(8*B+8)+2+
    ((4*w+4)+ownedDiagonalPageCost B w p n)

theorem diagonalPageFromUnary_native :
    mnNativePushBound 3 (diagonalPageFromUnary (P := P) (Q := Q) (A := A) (U := U)) := by
  refine ⟨installUnaryScalarInputs_native ..,?_,ownedDiagonalPage_native ..⟩
  simp [installDiagonalStreamWidth,ucopy,umulSym,scanR,drainR,popDo,keepIn,
    pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem diagonalPageFromUnary_exec (s t u alpha p w c n : ℕ)
    (hs : 0 < s) (hst : s ≤ t) (hfit : c+n ≤ s)
    (hprec : 13 ≤ p) (halpha : 2 ≤ alpha) (hsquare : u = alpha^2) (hbudget : alpha^2 ≤ p)
    (wl : List (Fin (A+4))) (hwl : wl.length = diagonalPageWidth p w u t)
    (v : HS tapes Q A U) (S : Stacks tapes A)
    (hS : (S.R (recovery (.parameter 4))).length = s)
    (hT : (S.R (recovery (.parameter 5))).length = t)
    (hu : (S.R (recovery (.parameter 1))).length = u)
    (hp : (S.R (recovery (.parameter 0))).length = p)
    (hc : (S.R diagonalCoreStart).length = c) (hend : (S.R diagonalCoreEnd).length = c+n)
    (hpacket : (S.R (recovery (.control .packet))).length = w)
    (hwidth : S.R (diagonalTable .wr) = wl)
    (hblank : ∀ r : TblR 48, r ≠ .wr → S.R (diagonalTable r) = [])
    (hwork : ∀ k ∈ [diagonalWord,diagonalConvertSaved,diagonalConvertTmp], S.R k = []) :
    ∃ v' F steps, v'.user = v.user ∧ steps ≤ diagonalPageFromUnaryCost S.R p w u t n ∧
      Exec body diagonalPageFromUnary (mk v S) steps (mk v' F) ∧
      F.R (diagonalRole .df) = cstream A w (packedInterval c n (diagonalField s t alpha p))++S.R (diagonalRole .df) ∧
      (∃ st', st'.acc = [] ∧ tblHolds diagonalTable F (tblRho (diagonalPageWidth p w u t) wl (List.replicate w tick) st')) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ k, k ≠ diagonalRole .df → (∀ r, diagonalTable r ≠ k) → F.R k = S.R k) ∧
      (∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (mk v S)+depth+
        3*diagonalPageFromUnaryCost S.R p w u t n) depth diagonalPageFromUnary
        (mk v S) steps (mk v' F)) := by
  obtain ⟨v₁,M,m₁,hv₁,hm₁,he₁,hh,hbound,hin,hout,hL,hframe⟩ :=
    loadDiagonalPageInputs_exec (body := body) s t u p w c n hst hfit wl hwl v S
      hS hT hu hp hc hend hwidth hblank hwork
  let st : TblSt 48 A := loadedBinaryState (diagonalPageWords s t u p c n) ⟨fun _ => 0,[]⟩
  have hpacketM : (M.R (recovery (.control .packet))).length = w := by
    rw [hframe _ (by intro r; simp [diagonalTable,recovery_injective.eq_iff])]; exact hpacket
  have htmpM : M.R diagonalConvertTmp = [] := by
    have hoff : ∀ r, diagonalTable r ≠ diagonalConvertTmp :=
      fun r => diagonalTable_ne_work r 307 (by decide)
    exact (hframe diagonalConvertTmp hoff).trans (hwork _ (by simp))
  obtain ⟨v₂,hv₂,he₂,hh₂⟩ := installDiagonalStreamWidth_exec (body := body)
    (diagonalPageWidth p w u t) w wl st v₁ M hpacketM hh htmpM
  let E : Stacks tapes A := {M with R := Function.update M.R (diagonalTable .wn) (List.replicate w tick)}
  obtain ⟨hsval,htval,huval,hpval,hcval,hendval,hacc⟩ := diagonalPageState_values (A := A) s t u p c n
  have hroom : alpha^2*(s+t)^2*2^(13*p+8) < 2^diagonalPageWidth p w u t := by
    rw [← hsquare]
    exact (diagonalPageWidth_bound p w s t u hst).2
  obtain ⟨v₃,F,m₃,hv₃,hm₃,he₃,hpage,htable,hi₃,ho₃,hl₃,hf₃,_⟩ :=
    ownedDiagonalPage_exec (body := body) diagonalTable diagonalTable_injective (diagonalRole .df)
      (fun r => diagonalTable_ne_role r .df) wl (List.replicate w tick) hwl (by simp)
      (diagonalPageWidth_bound p w s t u hst).1 st hsval htval (huval.trans hsquare)
      hpval hcval hendval hs hfit hprec halpha hbudget hroom hbound hacc v₂ E hh₂
  have hE (k : Fin tapes) (hoff : ∀ r, diagonalTable r ≠ k) : E.R k = S.R k := by
    exact (Function.update_of_ne (hoff .wn).symm _ _).trans (hframe k hoff)
  have hcost : m₁+((4*w+4)+m₃) ≤ diagonalPageFromUnaryCost S.R p w u t n := by
    dsimp [diagonalPageFromUnaryCost]; omega
  have hex : Exec body diagonalPageFromUnary (mk v S) (m₁+((4*w+4)+m₃)) (mk v₃ F) :=
    Exec.seq he₁ (Exec.seq he₂ he₃)
  refine ⟨v₃,F,_,hv₃.trans (hv₂.trans hv₁),hcost,hex,?_,htable,
    hi₃.trans hin,ho₃.trans hout,hl₃.trans hL,?_,fun depth => ?_⟩
  · rw [hpage,hE _ (fun r => diagonalTable_ne_role r .df)]
  · intro k hk hoff
    exact (hf₃ k hk hoff).trans (hE k hoff)
  · exact mn_native_exec_within hex 3 diagonalPageFromUnary_native depth
      (mnSize (mk v S)+depth+3*diagonalPageFromUnaryCost S.R p w u t n) (by omega)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
