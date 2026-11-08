module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOrdinaryDiagonalPage

/-! Initialize the multiplier while preserving the freshly generated shared page. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
noncomputable section
variable {Q A : ℕ} {P U : Type} {body : P → Pr P tapes Q A U}

def diagonalMultiplierLocalCost (B p w : ℕ) : ℕ :=
  (4*B+4)+(diagonalMultiplierFromUnaryCost B p w+(2*(5*B)+11))+(2*B+2)

theorem diagonalMultiplierLocal_native :
    mnNativePushBound 3 (diagonalMultiplierLocal (P := P) (Q := Q) (A := A) (U := U)) := by
  change mnNativePushBound 3 (.seq (ucopy diagonalWidthSource (diagonalMultiplierTable .wr) diagonalConvertTmp)
    (.seq (diagonalMultiplierFinished diagonalHeader diagonalWord diagonalConvertSaved diagonalConvertTmp diagonalCarry)
      (uclear (diagonalMultiplierTable .wr))))
  refine ⟨?_,diagonalMultiplierFinished_native ..,?_⟩
  · simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  · simp [uclear,drainR,peekR,popDo,mnNativePushBound,mnActPush]

theorem diagonalCounter_role_off (p w : ℕ) (R : Regs tapes A) (r : RsbR)
    (hwn : r ≠ .cm .wn) (hpn : r ≠ .cm .pn) (hnn : r ≠ .cm .nn) :
    diagonalCounterR p w R (diagonalRole r) = R (diagonalRole r) := by
  exact chirpMultiplierSetup_off diagonalCr R p w _
    (fun h => hwn (diagonalRole_injective h)) (fun h => hpn (diagonalRole_injective h))
    (fun h => hnn (diagonalRole_injective h))

theorem diagonalPage_multiplier_frame (p w : ℕ) (S : Stacks tapes A)
    (hfresh : DiagonalFresh S) (page : List (Fin (A+4))) :
    let E : Stacks tapes A := {S with R := Function.update S.R (diagonalRole .df) page}
    let F : Stacks tapes A := {E with R := diagonalCounterR p w E.R}
    RsbClean diagonalMul F ∧ F.R (diagonalRole .df) = page ∧
      F.R (diagonalRole .src) = [] ∧ F.R (diagonalRole .dst) = [] := by
  dsimp only
  let R := Function.update S.R (diagonalRole .df) page
  refine ⟨⟨hfresh.left,?_⟩,?_,?_,?_⟩
  · intro j
    have hcounter := chirpMultiplierSetup_off diagonalCr R p w (diagonalMul j)
      (diagonalRole_ne_mul (.cm .wn) j).symm (diagonalRole_ne_mul (.cm .pn) j).symm
      (diagonalRole_ne_mul (.cm .nn) j).symm
    exact hcounter.trans ((Function.update_of_ne (diagonalRole_ne_mul .df j).symm _ _).trans (hfresh.multiplier j))
  · exact (diagonalCounter_role_off p w R .df (by simp) (by simp) (by simp)).trans (Function.update_self ..)
  · have hne : diagonalRole .src ≠ diagonalRole .df := fun h => by cases diagonalRole_injective h
    exact (diagonalCounter_role_off p w R .src (by simp) (by simp) (by simp)).trans
      ((Function.update_of_ne hne _ _).trans (hfresh.role .src))
  · have hne : diagonalRole .dst ≠ diagonalRole .df := fun h => by cases diagonalRole_injective h
    exact (diagonalCounter_role_off p w R .dst (by simp) (by simp) (by simp)).trans
      ((Function.update_of_ne hne _ _).trans (hfresh.role .dst))

theorem diagonalMultiplierLocal_after_page (B p w : ℕ) (hpw : p ≤ w) (hw : 1 ≤ w)
    (hroom : 4*w+2 < 2^B) (v : HS tapes Q A U) (S : Stacks tapes A)
    (hB : (S.R diagonalWidthSource).length = B)
    (hp : (S.R (recovery (.control .precision))).length = p)
    (hwide : (S.R (recovery (.control .packet))).length = w)
    (hfresh : DiagonalFresh S) (page : List (Fin (A+4))) :
    let E : Stacks tapes A := {S with R := Function.update S.R (diagonalRole .df) page}
    ∃ v' steps, v'.user = v.user ∧ steps ≤ diagonalMultiplierLocalCost B p w ∧
      Exec body diagonalMultiplierLocal (mk v E) steps
        (mk v' {E with R := diagonalCounterR p w E.R}) ∧
      RsbReady (fun r => diagonalCounterR p w E.R (diagonalRole r)) w p := by
  dsimp only
  let E : Stacks tapes A := {S with R := Function.update S.R (diagonalRole .df) page}
  have hcontrol (c : RecoveryControl) : recovery (.control c) ≠ diagonalRole .df := by
    simp [diagonalRole,recovery_injective.eq_iff]
  have hwidth : diagonalWidthSource ≠ diagonalRole .df := by
    simp [diagonalWidthSource,diagonalRole,recovery_injective.eq_iff]
  have hE (k : Fin tapes) (hk : k ≠ diagonalRole .df) : E.R k = S.R k := Function.update_of_ne hk _ _
  obtain ⟨v',steps,hv,hm,he,hr⟩ := diagonalMultiplierBorrowed_exec (body := body)
    diagonalWidthSource diagonalHeader diagonalWord diagonalConvertSaved diagonalConvertTmp diagonalCarry
    diagonal_width_regs (fun r => diagonalTable_ne_work _ 304 (by decide)) diagonal_conversion_regs
    B p w hpw hw hroom v E
    ((congrArg List.length (hE _ hwidth)).trans hB)
    ((congrArg List.length (hE _ (hcontrol .precision))).trans hp)
    ((congrArg List.length (hE _ (hcontrol .packet))).trans hwide)
    (fun r => (hE _ (diagonalTable_ne_role _ .df)).trans (hfresh.table _))
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl
      all_goals exact (hE _ (diagonalRole_ne_work _ _ (by decide)).symm).trans (hfresh.work _))
    (by
      intro c
      have hne : diagonalCr c ≠ diagonalRole .df := by
        intro h
        have hh := diagonalRole_injective h
        cases hh
      exact (hE _ hne).trans (hfresh.role (.cm c)))
  exact ⟨v',steps,hv,hm,(he 0).toExec,hr⟩

def prepareDiagonalPage : Pr P tapes Q A U := .seq ordinaryDiagonalPage diagonalMultiplierLocal

theorem prepareDiagonalPage_native :
    mnNativePushBound 16 (prepareDiagonalPage (P := P) (Q := Q) (A := A) (U := U)) :=
  ⟨ordinaryDiagonalPage_native,mnNativePushBound_mono (by decide : 3 ≤ 16) diagonalMultiplierLocal_native⟩

theorem prepareDiagonalPage_exec (s t u alpha B p w a radius n : ℕ)
    (hs : 0 < s) (hst : s ≤ t) (hfit : a+radius+n ≤ s)
    (hprec : 13 ≤ p) (halpha : 2 ≤ alpha) (hsquare : u = alpha^2) (hbudget : alpha^2 ≤ p)
    (hpw : p ≤ w) (hw : 1 ≤ w) (hroom : 4*w+2 < 2^B)
    (v : HS tapes Q A U) (S : Stacks tapes A)
    (hS : (S.R (recovery (.parameter 4))).length = s)
    (hT : (S.R (recovery (.parameter 5))).length = t)
    (hu : (S.R (recovery (.parameter 1))).length = u)
    (hp : (S.R (recovery (.parameter 0))).length = p)
    (hprecision : (S.R (recovery (.control .precision))).length = p)
    (hpacket : (S.R (recovery (.control .packet))).length = w)
    (hB : (S.R diagonalWidthSource).length = B)
    (ha : (S.R diagonalHaloStart).length = a)
    (hradius : (S.R diagonalCropOffset).length = radius)
    (hn : (S.R diagonalCropRows).length = n) (hfresh : DiagonalFresh S) :
    let page := cstream A w (packedInterval (a+radius) n (diagonalField s t alpha p))++S.R (diagonalRole .df)
    let E : Stacks tapes A := {S with R := Function.update S.R (diagonalRole .df) page}
    let cost := ordinaryDiagonalPageCost S p w u t a radius n+diagonalMultiplierLocalCost B p w
    ∃ v' steps, v'.user = v.user ∧ steps ≤ cost ∧
      (∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (mk v S)+depth+16*cost)
        depth prepareDiagonalPage (mk v S) steps (mk v' {E with R := diagonalCounterR p w E.R})) ∧
      RsbReady (fun r => diagonalCounterR p w E.R (diagonalRole r)) w p := by
  dsimp only
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁⟩ := ordinaryDiagonalPage_exec (body := body)
    s t u alpha p w a radius n hs hst hfit hprec halpha hsquare hbudget v S
    hS hT hu hp hprecision hpacket ha hradius hn hfresh
  let page := cstream A w (packedInterval (a+radius) n (diagonalField s t alpha p))++S.R (diagonalRole .df)
  let E : Stacks tapes A := {S with R := Function.update S.R (diagonalRole .df) page}
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂,hr⟩ := diagonalMultiplierLocal_after_page (body := body)
    B p w hpw hw hroom v₁ S hB hprecision hpacket hfresh page
  have hex : Exec body prepareDiagonalPage (mk v S) (m₁+m₂)
      (mk v₂ {E with R := diagonalCounterR p w E.R}) := Exec.seq ((he₁ 0).toExec) he₂
  refine ⟨v₂,m₁+m₂,hv₂.trans hv₁,by omega,fun depth => ?_,hr⟩
  exact mn_native_exec_within hex 16 prepareDiagonalPage_native depth
    (mnSize (mk v S)+depth+16*(ordinaryDiagonalPageCost S p w u t a radius n+diagonalMultiplierLocalCost B p w))
    (by omega)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
