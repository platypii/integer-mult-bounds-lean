module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStandardBoundaryCounterRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryCounterRestore

/-! Execute boundary metadata directly into the standard seam master tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix BoundaryCropMetadata
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

theorem restoredStandardBoundaryCounters_exec (last : Bool)
    (D s width W : ℕ) (st : TblSt 9 A)
    (hs : st.val 0 = s) (hw : st.val 1 = width) (hW : st.val 2 = W)
    (hwidth : 0 < width) (hword : 0 < W) (hroom : 3*width < s)
    (hfit : s*W < 2^D) (hvalues : ∀ j, st.val j < 2^D)
    (wl : List (Fin (A+4))) (hwl : wl.length = D)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hholds : tblHolds boundaryCounterRegister S (tblRho D wl [] st))
    (hblank : S.R 26 = [] ∧ S.R 24 = [])
    (hzero : ∀ i : Fin 9, 3 ≤ i.val → st.val i = 0) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 16*tblC D 0+6*(s*W)+22*D+13 ∧
      Exec body (.seq (standardBoundaryCounterProgram last) (tblCompile boundaryCounterRegister restoreCode))
        (mk v S) n (mk v' {S with R := (Function.update (Function.update S.R 26
          (List.replicate (coreStart width (index last s width)*W) tick)) 24
          (List.replicate (coreLength s width (index last s width)*W) tick))}) := by
  obtain ⟨u,F,n,z,hu,hn,he,hh,hkeep,hacc,hfitZ,hskip,hcount,hi,ho,hl,hframe⟩ :=
    standardBoundaryCounters_exec (body := body) last D s width W st hs hw hW hwidth hword hroom
      hfit hvalues wl hwl v S hholds hblank
  have hkept (i : Fin 9) (hi : i.val < 3) : z.val i = st.val i := by
    have heq : i = Fin.castAdd 6 (⟨i.val,hi⟩ : Fin 3) := Fin.ext rfl
    rw [heq]
    exact hkeep _
  obtain ⟨v',G,m,hv,hm,hrestore,hhG,hGi,hGo,hGl,hGframe⟩ := restoreCode_exec body
    boundaryCounterRegister boundaryCounterRegister_injective D z st hkept hzero hacc
    hfitZ wl hwl u F hh
  have hGskip : G.R 26 = List.replicate (coreStart width (index last s width)*W) tick :=
    (hGframe 26 (fun r => (boundaryCounterRegister_off_masters r).1)).trans hskip
  have hGcount : G.R 24 = List.replicate (coreLength s width (index last s width)*W) tick :=
    (hGframe 24 (fun r => (boundaryCounterRegister_off_masters r).2)).trans hcount
  have hend : G = {S with R := (Function.update (Function.update S.R 26
      (List.replicate (coreStart width (index last s width)*W) tick)) 24
      (List.replicate (coreLength s width (index last s width)*W) tick))} := by
    refine Stacks.ext (hGi.trans hi) (hGo.trans ho) (hGl.trans hl) ?_
    funext i
    by_cases h24 : i = 24
    · subst i; simpa using hGcount
    by_cases h26 : i = 26
    · subst i; simpa using hGskip
    have hsame : G.R i = S.R i := by
      by_cases ht : ∃ r, boundaryCounterRegister r = i
      · obtain ⟨r,rfl⟩ := ht
        exact (hhG r).trans (hholds r).symm
      · have hoff : ∀ r, boundaryCounterRegister r ≠ i := by simpa only [not_exists] using ht
        exact (hGframe i hoff).trans (hframe i hoff h26 h24)
    simpa only [Function.update_of_ne h24,Function.update_of_ne h26] using hsame
  refine ⟨v',n+m,hv.trans hu,by omega,?_⟩
  rw [←hend]
  exact Exec.seq he hrestore

theorem restoredStandardBoundaryCounters_within (last : Bool)
    (v v' : HS 117 Q A U) (S F : Stacks 117 A) (n depth : ℕ)
    (he : Exec body (.seq (standardBoundaryCounterProgram last) (tblCompile boundaryCounterRegister restoreCode))
      (mk v S) n (mk v' F)) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*n) depth
      (.seq (standardBoundaryCounterProgram last) (tblCompile boundaryCounterRegister restoreCode))
      (mk v S) n (mk v' F) :=
  mn_native_exec_within he 3
    ⟨counterProgram_native _ _ _ _,tblCompile_native _ _⟩ depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
