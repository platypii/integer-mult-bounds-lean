module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRoundList
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Apply generated signed rounding to one local prefix, preserving later keys. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def roundPackedPrefix (rg : TblR 8 → Fin T) (ports : Fin 4 → Fin T)
    (count src work saved tmp sp sg cy : Fin T) : Pr P T Q A U :=
  .seq (transfer count src saved tmp)
    (.seq (moveR saved work id)
      (.seq (generatedFinalRound rg ports work saved tmp sp sg cy)
        (.seq (moveR work tmp id) (moveR tmp src id))))

/-- Only local coefficients enter the existing rounding pass. The count and
scalar bank restore, and the later-key suffix is neither rounded nor scanned. -/
theorem roundPackedPrefix_exec (hA : 4 ≤ A)
    (rg : TblR 8 → Fin T) (hrg : Function.Injective rg)
    (ports : Fin 4 → Fin T) (hports : Function.Injective ports)
    (hsep : ∀ i r, rg r ≠ ports i)
    {count src work saved tmp sp sg cy : Fin T}
    (hreg : [count,src,work,saved,tmp,ports 0,ports 1,ports 2,ports 3,sp,sg,cy].Nodup)
    (hscalar : ∀ r, rg r ∉ [src,work,saved])
    (B w q p j E : ℕ) (wl : List (Fin (A+4))) (hwl : wl.length = B)
    (st : TblSt 8 A) (hval : st.val = ![w,q,p,j,E,0,0,0])
    (hp : p ≤ q) (hw : 1 ≤ w) (hsize : q-p+j+(p+E+5) ≤ w)
    (hroom : w < 2^B) (hfit : ∀ i, st.val i < 2^B)
    (xs : List GaussianInt) (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho B wl [] st))
    (hsrc : S.R src = cstream A w xs++tail) (hcount : (S.R count).length = xs.length*w)
    (hblank : ∀ r ∈ [work,saved,tmp,sp,sg,cy], S.R r = [])
    (hheaders : ∀ i, S.R (ports i) = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 13*tblC B 0+16*w+44*B+48+xs.length*(20*w+4*(p+E+5)+23) ∧
      Exec body (roundPackedPrefix rg ports count src work saved tmp sp sg cy) (mk v S) n
        (mk v' {S with R := (Function.update S.R src
          (cstream A (p+E+5) (xs.map (finalRoundWord w q p j))++tail))}) := by
  have hr := hreg
  regs_ne hr
  let X := cstream A w xs
  let Y := cstream A (p+E+5) (xs.map (finalRoundWord w q p j))
  have hX : X.length = xs.length*w := by simp [X]
  have hY : Y.length = xs.length*(p+E+5) := by simp [Y]
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body)
    (show [count,src,saved,tmp].Nodup by regs_nodup) v S X tail hsrc
    (by simpa [hX] using hcount) (hblank tmp (by simp))
  let S₁ : Stacks T A := {S with R := (Function.update (Function.update S.R src tail) saved X.reverse)}
  have he₁' : Exec body (transfer count src saved tmp) (mk v S) (4*X.length+4) (mk v₁ S₁) := by
    simpa [S₁,hblank saved (by simp)] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec (body := body) saved work ‹work ≠ saved›.symm id v₁ S₁
  let S₂ : Stacks T A := {S₁ with R := (Function.update (Function.update S₁.R saved []) work X)}
  have he₂' : Exec body (moveR saved work id) (mk v₁ S₁) (2*X.length+2) (mk v₂ S₂) := by
    simpa [S₂,S₁,movedR,‹src ≠ work›.symm,‹work ≠ saved›,hblank work (by simp)] using he₂
  have htable : tblHolds rg S₂ (tblRho B wl [] st) := by
    intro r
    have hne := hscalar r
    have hs : rg r ≠ src := by intro he; exact hne (by simp [he])
    have hw : rg r ≠ work := by intro he; exact hne (by simp [he])
    have hb : rg r ≠ saved := by intro he; exact hne (by simp [he])
    simpa [S₂,S₁,hs,hw,hb] using hS r
  have hsmall : ∀ r ∈ [saved,tmp,sp,sg,cy], S₂.R r = [] := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [S₂,S₁,Function.update_apply, *, Ne.symm]
  have hhead : ∀ i, S₂.R (ports i) = [] := by
    intro i
    fin_cases i <;> simp [S₂,S₁,Function.update_apply, *, Ne.symm]
  have hv (i : Fin 8) := congrFun hval i
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃,_⟩ := generatedFinalRound_list_exec (body := body) hA rg hrg ports hports hsep
    (show [work,saved,tmp,ports 0,ports 1,ports 2,ports 3,sp,sg,cy].Nodup by regs_nodup)
    (w := w) (q := q) (p := p) (j := j) (E := E) wl hwl st (hv 0) (hv 1) (hv 2) (hv 3) (hv 4) (hv 5) (hv 6) (hv 7)
    hp hw hsize hroom hfit xs v₂ S₂ htable (by simp [S₂,X]) hsmall hhead
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R work Y}
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec (body := body) work tmp ‹work ≠ tmp› id v₃ S₃
  let S₄ : Stacks T A := {S₃ with R := movedR S₃.R work tmp id (S₃.R work)}
  obtain ⟨v₅,hu₅,he₅⟩ := moveR_exec (body := body) tmp src ‹src ≠ tmp›.symm id v₄ S₄
  have h₃work : S₃.R work = Y := by simp [S₃]
  have h₃tmp : S₃.R tmp = [] := by
    simp [S₃,S₂,S₁,‹work ≠ tmp›.symm,‹saved ≠ tmp›.symm,‹src ≠ tmp›.symm,hblank tmp (by simp)]
  have h₄tmp : S₄.R tmp = Y.reverse := by simp [S₄,movedR,h₃work,h₃tmp]
  refine ⟨v₅,(4*X.length+4)+(2*X.length+2)+n₃+(2*Y.length+2)+(2*Y.length+2),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast ?_ ?_⟩
  · rw [hX,hY]
    change n₃ ≤ 13*tblC B 0+16*w+44*B+38+xs.length*(14*w+23) at hn₃
    nlinarith only [hn₃]
  · simp [h₃work,h₄tmp,Nat.add_assoc]
  · apply congrArg (mk v₅)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hs : i = src
    · subst i; simp [S₄,S₃,S₂,S₁,movedR,Function.update_apply, *, Ne.symm,Y]
    by_cases hw : i = work
    · subst i; simp [S₄,S₃,S₂,S₁,movedR,Function.update_apply, *, Ne.symm,Y]
    by_cases hb : i = saved
    · subst i; simp [S₄,S₃,S₂,S₁,movedR,Function.update_apply, *, Ne.symm,Y]
    by_cases ht : i = tmp
    · subst i; simp [S₄,S₃,S₂,S₁,movedR,Function.update_apply, *, Ne.symm,Y]
    · simp [S₄,S₃,S₂,S₁,movedR,Function.update_apply,hs,hw,hb,ht]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
