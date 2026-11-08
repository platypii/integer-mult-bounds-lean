module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalPageFromUnary
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseScalarBank
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock

/-! Retire the page evaluator's private scalar bank, retaining only its output. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
noncomputable section
variable {Q A : ℕ} {P U : Type} {body : P → Pr P tapes Q A U}

def diagonalPageFinished : Pr P tapes Q A U :=
  .seq diagonalPageFromUnary
    (.seq (uclear (diagonalTable .wn)) (releaseScalarBank diagonalTable))

def diagonalPageFinishedCost (R : Regs tapes A) (p w u t n : ℕ) : ℕ :=
  diagonalPageFromUnaryCost R p w u t n+
    ((2*w+2)+(2*(48*diagonalPageWidth p w u t)+97))

theorem diagonalPageFinished_native :
    mnNativePushBound 3 (diagonalPageFinished (P := P) (Q := Q) (A := A) (U := U)) := by
  refine ⟨diagonalPageFromUnary_native,?_,mnNativePushBound_mono (by decide : 0 ≤ 3)
    (clearWords_native _)⟩
  simp [uclear,drainR,peekR,popDo,mnNativePushBound,mnActPush]

theorem diagonalPageFinished_exec (s t u alpha p w c n : ℕ)
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
    ∃ v' steps, v'.user = v.user ∧ steps ≤ diagonalPageFinishedCost S.R p w u t n ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (mk v S)+depth+
        3*diagonalPageFinishedCost S.R p w u t n) depth diagonalPageFinished
        (mk v S) steps (mk v' {S with R := (Function.update S.R (diagonalRole .df)
          (cstream A w (packedInterval c n (diagonalField s t alpha p))++S.R (diagonalRole .df)))}) := by
  obtain ⟨v₁,F,m,hv₁,hm,he,hpage,⟨st,hacc,hh⟩,hin,hout,hL,hframe,_⟩ :=
    diagonalPageFromUnary_exec (body := body) s t u alpha p w c n hs hst hfit hprec halpha
      hsquare hbudget wl hwl v S hS hT hu hp hc hend hpacket hwidth hblank hwork
  obtain ⟨v₂,hv₂,hclear⟩ := uclear_exec (body := body) (diagonalTable .wn) v₁ F
  have hlen : (F.R (diagonalTable .wn)).length = w := by rw [hh .wn]; simp [tblRho]
  let E : Stacks tapes A := {F with R := Function.update F.R (diagonalTable .wn) []}
  let page := cstream A w (packedInterval c n (diagonalField s t alpha p))++S.R (diagonalRole .df)
  let G : Stacks tapes A := {S with R := Function.update S.R (diagonalRole .df) page}
  have hhE : tblHolds diagonalTable E (tblRho (diagonalPageWidth p w u t) wl [] st) := by
    intro r
    by_cases hr : r = .wn
    · subst r; simp [E,tblRho]
    · have hne : diagonalTable r ≠ diagonalTable .wn := fun h => hr (diagonalTable_injective h)
      change Function.update F.R (diagonalTable .wn) [] (diagonalTable r) = _
      rw [Function.update_of_ne hne,hh r]
      cases r <;> first | rfl | exact (hr rfl).elim
  have hGtable (r : TblR 48) : G.R (diagonalTable r) = S.R (diagonalTable r) :=
    Function.update_of_ne (diagonalTable_ne_role r .df) _ _
  have hframeE (k : Fin tapes) (hoff : ∀ r, diagonalTable r ≠ k) : E.R k = G.R k := by
    change Function.update F.R (diagonalTable .wn) [] k = Function.update S.R (diagonalRole .df) page k
    rw [Function.update_of_ne (hoff .wn).symm]
    by_cases hk : k = diagonalRole .df
    · subst k; simpa only [Function.update_self] using hpage
    · rw [Function.update_of_ne hk]
      exact hframe k hk hoff
  obtain ⟨v₃,hv₃,hrelease⟩ := releaseScalarBank_to_state_exec (body := body)
    diagonalTable diagonalTable_injective (diagonalPageWidth p w u t) wl st hacc v₂ E G hhE
    ((hGtable .wr).trans hwidth) (fun r hr => (hGtable r).trans (hblank r hr)) hin hout hL hframeE
  have hex : Exec body diagonalPageFinished (mk v S)
      (m+((2*w+2)+(2*(48*diagonalPageWidth p w u t)+97))) (mk v₃ G) := by
    have hclear' : Exec body (uclear (diagonalTable .wn)) (mk v₁ F) (2*w+2) (mk v₂ E) := by
      simpa only [hlen] using hclear
    exact (Exec.seq he (Exec.seq hclear' hrelease)).cast (by omega) rfl
  refine ⟨v₃,m+((2*w+2)+(2*(48*diagonalPageWidth p w u t)+97)),
    hv₃.trans (hv₂.trans hv₁),?_,fun depth => ?_⟩
  · dsimp [diagonalPageFinishedCost]; omega
  · exact mn_native_exec_within hex 3 diagonalPageFinished_native depth
      (mnSize (mk v S)+depth+3*diagonalPageFinishedCost S.R p w u t n)
      (by dsimp [diagonalPageFinishedCost]; omega)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
