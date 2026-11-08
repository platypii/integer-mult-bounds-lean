module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalCoreInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalWidthPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalPageRelease

/-! A complete shared-page lifetime from retained unary recovery metadata. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
noncomputable section
variable {Q A : ℕ} {P U : Type} {body : P → Pr P tapes Q A U}

def diagonalPagePrivate : List (Fin tapes) := [diagonalPageRuler,diagonalCoreStart,diagonalCoreEnd]

def ordinaryDiagonalPage : Pr P tapes Q A U :=
  .seq prepareLocalDiagonalWidth (.seq prepareDiagonalCoreInputs
    (.seq diagonalPageFinished (clearWords diagonalPagePrivate)))

def diagonalPagePrepared (S : Stacks tapes A) (p w u t c n : ℕ) : Stacks tapes A :=
  {S with R := (Function.update (Function.update (Function.update S.R diagonalPageRuler
    (List.replicate (diagonalPageWidth p w u t) tick)) diagonalCoreStart (List.replicate c tick))
      diagonalCoreEnd (List.replicate (c+n) tick))}

def ordinaryDiagonalPageCost (S : Stacks tapes A) (p w u t a radius n : ℕ) : ℕ :=
  (coefficientWidthCost p w 1 u 0 t+6)+prepareDiagonalCoreInputsCost a radius n+
    diagonalPageFinishedCost (diagonalPagePrepared S p w u t (a+radius) n).R p w u t n+
      (2*(diagonalPageWidth p w u t+(a+radius)+(a+radius+n))+7)

theorem ordinaryDiagonalPage_native :
    mnNativePushBound 16 (ordinaryDiagonalPage (P := P) (Q := Q) (A := A) (U := U)) :=
  ⟨prepareLocalDiagonalWidth_native,mnNativePushBound_mono (by decide : 2 ≤ 16) prepareDiagonalCoreInputs_native,
    mnNativePushBound_mono (by decide : 3 ≤ 16) diagonalPageFinished_native,
    mnNativePushBound_mono (by decide : 0 ≤ 16) (clearWords_native _)⟩

theorem ordinaryDiagonalPage_exec (s t u alpha p w a radius n : ℕ)
    (hs : 0 < s) (hst : s ≤ t) (hfit : a+radius+n ≤ s)
    (hprec : 13 ≤ p) (halpha : 2 ≤ alpha) (hsquare : u = alpha^2) (hbudget : alpha^2 ≤ p)
    (v : HS tapes Q A U) (S : Stacks tapes A)
    (hS : (S.R (recovery (.parameter 4))).length = s)
    (hT : (S.R (recovery (.parameter 5))).length = t)
    (hu : (S.R (recovery (.parameter 1))).length = u)
    (hp : (S.R (recovery (.parameter 0))).length = p)
    (hprecision : (S.R (recovery (.control .precision))).length = p)
    (hpacket : (S.R (recovery (.control .packet))).length = w)
    (ha : (S.R diagonalHaloStart).length = a)
    (hradius : (S.R diagonalCropOffset).length = radius)
    (hn : (S.R diagonalCropRows).length = n) (hfresh : DiagonalFresh S) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ ordinaryDiagonalPageCost S p w u t a radius n ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (mk v S)+depth+
        16*ordinaryDiagonalPageCost S p w u t a radius n) depth ordinaryDiagonalPage
        (mk v S) steps (mk v' {S with R := (Function.update S.R (diagonalRole .df)
          (cstream A w (packedInterval (a+radius) n (diagonalField s t alpha p))++S.R (diagonalRole .df)))}) := by
  let B := diagonalPageWidth p w u t
  let wl : List (Fin (A+4)) := List.replicate B tick
  let M : Stacks tapes A := {S with R := Function.update S.R diagonalPageRuler wl}
  let V := diagonalPagePrepared S p w u t (a+radius) n
  have htableStart : diagonalPageRuler ≠ diagonalCoreStart := diagonalTable_ne_work (TblR.wr : TblR 48) 309 (by decide)
  have htableEnd : diagonalPageRuler ≠ diagonalCoreEnd := diagonalTable_ne_work (TblR.wr : TblR 48) 310 (by decide)
  have hstartEnd : diagonalCoreStart ≠ diagonalCoreEnd := by
    simp [diagonalCoreStart,diagonalCoreEnd,recovery_injective.eq_iff]
  have hM (k : Fin tapes) (hk : k ≠ diagonalPageRuler) : M.R k = S.R k := Function.update_of_ne hk _ _
  have hV (k : Fin tapes) (hw : k ≠ diagonalPageRuler) (hc : k ≠ diagonalCoreStart)
      (he : k ≠ diagonalCoreEnd) : V.R k = S.R k := by
    change Function.update (Function.update (Function.update S.R diagonalPageRuler wl)
      diagonalCoreStart (List.replicate (a+radius) tick)) diagonalCoreEnd (List.replicate (a+radius+n) tick) k = _
    simp only [Function.update_of_ne he,Function.update_of_ne hc,Function.update_of_ne hw]
  have hcontrol (k : RecoveryControl) : recovery (.control k) ≠ diagonalPageRuler ∧
      recovery (.control k) ≠ diagonalCoreStart ∧ recovery (.control k) ≠ diagonalCoreEnd := by
    simp [diagonalPageRuler,diagonalTable,diagonalCoreStart,diagonalCoreEnd,recovery_injective.eq_iff]
  have hparameter (i : Fin 8) : recovery (.parameter i) ≠ diagonalPageRuler ∧
      recovery (.parameter i) ≠ diagonalCoreStart ∧ recovery (.parameter i) ≠ diagonalCoreEnd := by
    simp [diagonalPageRuler,diagonalTable,diagonalCoreStart,diagonalCoreEnd,recovery_injective.eq_iff]
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁⟩ := prepareLocalDiagonalWidth_exec (body := body) p w u t v S
    hprecision hpacket hu hT hfresh
  have hcore (k : Fin 392) (hk : 300 ≤ k.val) : M.R (recovery (.work k)) = [] :=
    (hM _ (diagonalTable_ne_work _ k hk).symm).trans (hfresh.work k)
  obtain ⟨v₂,hv₂,he₂⟩ := prepareDiagonalCoreInputs_exec (body := body) a radius n v₁ M
    (by exact (congrArg List.length (hM diagonalHaloStart (hparameter 6).1)).trans ha)
    (by exact (congrArg List.length (hM diagonalCropOffset (hcontrol .cropOffset).1)).trans hradius)
    (by exact (congrArg List.length (hM diagonalCropRows (hcontrol .cropRows).1)).trans hn)
    (by intro k hk; apply hcore k; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> decide)
  have hvals (i : Fin 8) : V.R (recovery (.parameter i)) = S.R (recovery (.parameter i)) :=
    hV _ (hparameter i).1 (hparameter i).2.1 (hparameter i).2.2
  have hwidth : V.R (diagonalTable .wr) = wl := by
    change Function.update (Function.update (Function.update S.R diagonalPageRuler wl)
      diagonalCoreStart _) diagonalCoreEnd _ diagonalPageRuler = wl
    rw [Function.update_of_ne htableEnd,Function.update_of_ne htableStart]
    exact Function.update_self ..
  have hblank : ∀ r : TblR 48, r ≠ .wr → V.R (diagonalTable r) = [] := by
    intro r hr
    exact (hV _ (fun h => hr (diagonalTable_injective h))
      (diagonalTable_ne_work r 309 (by decide)) (diagonalTable_ne_work r 310 (by decide))).trans (hfresh.table r)
  have hwork (k : Fin tapes) (hk : k ∈ [diagonalWord,diagonalConvertSaved,diagonalConvertTmp]) : V.R k = [] := by
    have hww (i j : Fin 392) (hij : i ≠ j) : recovery (.work i) ≠ recovery (.work j) :=
      fun h => hij (RecoveryBank.work.inj (recovery_injective h))
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl
    all_goals apply (hV _ (diagonalTable_ne_work _ _ (by decide)).symm
      (hww _ _ (by decide)) (hww _ _ (by decide))).trans
    all_goals exact hfresh.work _
  obtain ⟨v₃,m₃,hv₃,hm₃,he₃⟩ := diagonalPageFinished_exec (body := body) s t u alpha p w (a+radius) n
    hs hst hfit hprec halpha hsquare hbudget wl (by simp [wl,B]) v₂ V
    (by rw [hvals 4]; exact hS) (by rw [hvals 5]; exact hT) (by rw [hvals 1]; exact hu)
    (by rw [hvals 0]; exact hp)
    (by simp [V,diagonalPagePrepared,Function.update_of_ne hstartEnd])
    (by simp [V,diagonalPagePrepared])
    (by rw [hV _ (hcontrol .packet).1 (hcontrol .packet).2.1 (hcontrol .packet).2.2]; exact hpacket)
    hwidth hblank hwork
  let page := cstream A w (packedInterval (a+radius) n (diagonalField s t alpha p))++S.R (diagonalRole .df)
  have hdf : V.R (diagonalRole .df) = S.R (diagonalRole .df) :=
    hV _ (diagonalTable_ne_role .wr .df).symm (diagonalRole_ne_work _ 309 (by decide))
      (diagonalRole_ne_work _ 310 (by decide))
  let N : Stacks tapes A := {V with R := Function.update V.R (diagonalRole .df) page}
  have he₃' : Exec body diagonalPageFinished (mk v₂ V) m₃ (mk v₃ N) := by
    simpa only [hdf] using (he₃ 0).toExec
  have hnd : diagonalPagePrivate.Nodup := by
    have he : diagonalPageRuler ≠ diagonalCoreEnd := htableEnd
    have hc : diagonalPageRuler ≠ diagonalCoreStart := htableStart
    simp [diagonalPagePrivate,hc,he,hstartEnd]
  obtain ⟨v₄,hv₄,hclear⟩ := clearWords_exec (body := body) diagonalPagePrivate hnd v₃ N
  have hpageWidth : diagonalPageRuler ≠ diagonalRole .df := diagonalTable_ne_role .wr .df
  have hpageStart : diagonalCoreStart ≠ diagonalRole .df := (diagonalRole_ne_work .df 309 (by decide)).symm
  have hpageEnd : diagonalCoreEnd ≠ diagonalRole .df := (diagonalRole_ne_work .df 310 (by decide)).symm
  have hsum : (diagonalPagePrivate.map (fun r => (N.R r).length)).sum = B+(a+radius)+(a+radius+n) := by
    simp only [diagonalPagePrivate,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,N,
      Function.update_of_ne hpageWidth,Function.update_of_ne hpageStart,Function.update_of_ne hpageEnd]
    have hw : V.R diagonalPageRuler = wl := hwidth
    rw [hw]
    simp only [V,diagonalPagePrepared,Function.update_of_ne hstartEnd,
      Function.update_self,List.length_replicate,wl]
    omega
  have hrestore : {N with R := fun k => if k ∈ diagonalPagePrivate then [] else N.R k} =
      ({S with R := Function.update S.R (diagonalRole .df) page} : Stacks tapes A) := by
    refine Stacks.ext (show N.inp = S.inp from rfl) (show N.out = S.out from rfl)
      (show N.L = S.L from rfl) ?_
    funext k
    have hw : S.R diagonalPageRuler = [] := hfresh.table .wr
    have hc : S.R diagonalCoreStart = [] := hfresh.work 309
    have he : S.R diagonalCoreEnd = [] := hfresh.work 310
    change (if k ∈ diagonalPagePrivate then [] else N.R k) = _
    by_cases hk : k ∈ diagonalPagePrivate
    · simp only [diagonalPagePrivate,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl
      · rw [ite_eq_left (by simp [diagonalPagePrivate])]
        exact ((Function.update_of_ne hpageWidth _ _).trans hw).symm
      · rw [ite_eq_left (by simp [diagonalPagePrivate])]
        exact ((Function.update_of_ne hpageStart _ _).trans hc).symm
      · rw [ite_eq_left (by simp [diagonalPagePrivate])]
        exact ((Function.update_of_ne hpageEnd _ _).trans he).symm
    · have hne : k ≠ diagonalPageRuler ∧ k ≠ diagonalCoreStart ∧ k ≠ diagonalCoreEnd := by
        simpa [diagonalPagePrivate] using hk
      rw [ite_eq_right hk]
      by_cases hd : k = diagonalRole .df
      · subst k; simp [N]
      · exact (Function.update_of_ne hd _ _).trans ((hV k hne.1 hne.2.1 hne.2.2).trans
          (Function.update_of_ne hd _ _).symm)
  have hex : Exec body ordinaryDiagonalPage (mk v S)
      (m₁+(prepareDiagonalCoreInputsCost a radius n+(m₃+(2*(B+(a+radius)+(a+radius+n))+7))))
      (mk v₄ {S with R := Function.update S.R (diagonalRole .df) page}) := by
    have hc : Exec body (clearWords diagonalPagePrivate) (mk v₃ N)
        (2*(B+(a+radius)+(a+radius+n))+7)
        (mk v₄ {S with R := Function.update S.R (diagonalRole .df) page}) :=
      hclear.cast (by rw [hsum]; simp only [diagonalPagePrivate,List.length_cons,List.length_nil])
        (congrArg (mk v₄) hrestore)
    exact Exec.seq he₁ (Exec.seq ((he₂ 0).toExec) (Exec.seq he₃' hc))
  have hcost : m₁+(prepareDiagonalCoreInputsCost a radius n+(m₃+(2*(B+(a+radius)+(a+radius+n))+7))) ≤
      ordinaryDiagonalPageCost S p w u t a radius n := by
    change _ ≤ (coefficientWidthCost p w 1 u 0 t+6)+prepareDiagonalCoreInputsCost a radius n+
      diagonalPageFinishedCost V.R p w u t n+(2*(B+(a+radius)+(a+radius+n))+7)
    omega
  refine ⟨v₄,_,hv₄.trans (hv₃.trans (hv₂.trans hv₁)),hcost,fun depth => ?_⟩
  exact mn_native_exec_within hex 16 ordinaryDiagonalPage_native depth
    (mnSize (mk v S)+depth+16*ordinaryDiagonalPageCost S p w u t a radius n) (by omega)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
