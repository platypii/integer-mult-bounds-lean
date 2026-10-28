module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundHeaderFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinalRoundList
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinalRoundCost
public import IntegerMultBounds.MathlibTM2.StackLifecycleResources

/-! Generate, execute and release final-rounding controls from binary dimensions. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def generatedFinalRound (rg : TblR 8 → Fin T) (ports : Fin 4 → Fin T)
    (src dst tmp sp sg cy : Fin T) : Pr P T Q A U :=
  .seq (generatedRoundHeaders rg ports)
    (.seq (topPass src dst (topShiftWord src dst tmp (ports 0) (ports 1) (ports 2) (ports 3) sp sg cy))
      (clearWords ((List.finRange 4).map ports)))

theorem generatedFinalRound_list_exec (hA : 4 ≤ A) (rg : TblR 8 → Fin T) (hrg : Function.Injective rg)
    (ports : Fin 4 → Fin T) (hports : Function.Injective ports) (hsep : ∀ i r, rg r ≠ ports i)
    {src dst tmp sp sg cy : Fin T}
    (hreg : [src,dst,tmp,ports 0,ports 1,ports 2,ports 3,sp,sg,cy].Nodup)
    {W w q p j E : ℕ} (wl : List (Fin (A+4))) (hwl : wl.length = W)
    (st : TblSt 8 A) (h0 : st.val 0 = w) (h1 : st.val 1 = q) (h2 : st.val 2 = p)
    (h3 : st.val 3 = j) (h4 : st.val 4 = E)
    (h5 : st.val 5 = 0) (h6 : st.val 6 = 0) (h7 : st.val 7 = 0)
    (hp : p ≤ q) (hw : 1 ≤ w) (hsize : q-p+j+(p+E+5) ≤ w) (hroom : w < 2^W)
    (hfit : ∀ i, st.val i < 2^W) (xs : List GaussianInt)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl [] st))
    (hsrc : S.R src = cstream A w xs)
    (hblank : ∀ r ∈ [dst,tmp,sp,sg,cy], S.R r = []) (hheaders : ∀ i, S.R (ports i) = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 13*tblC W 0+16*w+44*W+38+xs.length*(14*w+23) ∧
      Exec body (generatedFinalRound rg ports src dst tmp sp sg cy) (mk v S) n
        (mk v' {S with R := (Function.update S.R src (cstream A (p+E+5) (xs.map (finalRoundWord w q p j))))}) ∧
      (∀ z ∈ xs, value p (finalRoundWord w q p j z) = rhoC p (((2 : ℂ)^j)⁻¹*
          value q (IntegerMultBounds.MathlibTM2.LayerMachine.symZ w z))) ∧
      ∀ C, mnProgPush (generatedFinalRound (P := P) (U := U) (A := A) (Q := Q) rg ports src dst tmp sp sg cy) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*(13*tblC W 0+16*w+44*W+38+xs.length*(14*w+23))) depth
          (generatedFinalRound rg ports src dst tmp sp sg cy) (mk v S) n
          (mk v' {S with R := (Function.update S.R src (cstream A (p+E+5) (xs.map (finalRoundWord w q p j))))}) := by
  have hsepRound := roundPorts_separate hreg
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hh₁,hi₁,ho₁,hL₁,hhead,hframe⟩ :=
    generatedRoundHeaders_exec (body := body) rg hrg ports hports hsep wl hwl st
      h0 h1 h2 h3 h4 h5 h6 h7 hp hsize hroom hfit v S hS
  have hoff (r : Fin T) (hr : ∀ i, ports i ≠ r) : S₁.R r = S.R r :=
    roundHeader_frame rg ports S S₁ _ hS hh₁ hframe r hr
  have hhead₁ (i : Fin 4) : S₁.R (ports i) = List.replicate (roundHeaderValues w q p j E i) tick := by
    simpa only [hheaders,List.append_nil] using hhead i
  have hfree (r : Fin T) (hr : r ∈ [src,dst,tmp,sp,sg,cy]) : S₁.R r = S.R r := by
    exact hoff r (fun i => hsepRound i r hr)
  have hg := roundHeaders_ready w q p j E ports tmp sp sg cy S₁ hhead₁
    ((hfree tmp (by simp)).trans (hblank tmp (by simp)))
    ((hfree sp (by simp)).trans (hblank sp (by simp)))
    ((hfree sg (by simp)).trans (hblank sg (by simp)))
    ((hfree cy (by simp)).trans (hblank cy (by simp)))
  obtain ⟨v₂,hu₂,he₂,hd⟩ := finalRound_list_exec (body := body) hA hreg w q p j (p+E+5)
    hp hw hsize xs v₁ S₁ ((hfree src (by simp)).trans hsrc)
    ((hfree dst (by simp)).trans (hblank dst (by simp))) hg
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R src (cstream A (p+E+5) (xs.map (finalRoundWord w q p j)))}
  let rs := (List.finRange 4).map ports
  have hnd : rs.Nodup := (List.nodup_finRange 4).map hports
  have hs₂ (i : Fin 4) : S₂.R (ports i) = S₁.R (ports i) := by
    have hne : ports i ≠ src := hsepRound i src (by simp)
    exact Function.update_of_ne hne _ _
  have hsum : (rs.map fun r => (S₂.R r).length).sum = 2*w := by
    simp only [rs,List.map_map,Function.comp_def,hs₂,hhead₁,List.length_replicate]
    simp [roundHeaderValues,List.finRange_succ]
    omega
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) rs hnd v₂ S₂
  have hfinal : {S₂ with R := fun r => if r ∈ rs then [] else S₂.R r} =
      {S with R := Function.update S.R src (cstream A (p+E+5) (xs.map (finalRoundWord w q p j)))} := by
    apply Stacks.ext
    · exact hi₁
    · exact ho₁
    · exact hL₁
    funext r
    by_cases hr : r ∈ rs
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
      have hne : ports i ≠ src := hsepRound i src (by simp)
      simp only [hr,ite_true,Function.update_of_ne hne,hheaders]
    · have hoffr : ∀ i, ports i ≠ r := by
        intro i he
        exact hr (List.mem_map.mpr ⟨i,List.mem_finRange i,he⟩)
      simp only [hr,ite_false,S₂]
      by_cases he : r = src
      · subst r; simp only [Function.update_self]
      · simp only [Function.update_of_ne he]
        exact hoff r hoffr
  have he := (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl (congrArg (mk v₃) hfinal)
  have hc : n₁+((1+(xs.length*(topShiftWordCost w (q-p+j) (p+E+5)+1)+1)+(2*(xs.length*(p+E+5))+2))+
      (2*(rs.map fun r => (S₂.R r).length).sum+2*rs.length+1)) ≤
      13*tblC W 0+16*w+44*W+38+xs.length*(14*w+23) := by
    simp only [hsum,rs,List.length_map,List.length_finRange]
    have hpass := finalRound_pass_cost_le hsize xs.length
    omega
  exact ⟨v₃,_,hu₃.trans (hu₂.trans hu₁),hc,he,hd,mn_bounded_exec_certify he hc⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
