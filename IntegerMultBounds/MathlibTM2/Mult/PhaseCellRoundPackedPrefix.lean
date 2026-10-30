module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRoundList
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTransformPrefix

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
  transformPrefix count src work saved tmp (generatedFinalRound rg ports work saved tmp sp sg cy)

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
  let S₂ := isolatedPrefixState S src work saved X tail
  have htable : tblHolds rg S₂ (tblRho B wl [] st) := by
    intro r
    have hne := hscalar r
    have hs : rg r ≠ src := by intro he; exact hne (by simp [he])
    have hw : rg r ≠ work := by intro he; exact hne (by simp [he])
    have hb : rg r ≠ saved := by intro he; exact hne (by simp [he])
    simpa [S₂,isolatedPrefixState,hs,hw,hb] using hS r
  have hsmall : ∀ r ∈ [saved,tmp,sp,sg,cy], S₂.R r = [] := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [S₂,isolatedPrefixState,Function.update_apply, *, Ne.symm]
  have hhead : ∀ i, S₂.R (ports i) = [] := by
    intro i
    fin_cases i <;> simp [S₂,isolatedPrefixState,Function.update_apply, *, Ne.symm]
  have hv (i : Fin 8) := congrFun hval i
  have hrun : ∀ v₂ : HS T Q A U, ∃ v₃ n₃, v₃.user = v₂.user ∧
      n₃ ≤ 13*tblC B 0+16*w+44*B+38+xs.length*(14*w+23) ∧
      Exec body (generatedFinalRound rg ports work saved tmp sp sg cy) (mk v₂ S₂) n₃
        (mk v₃ {S₂ with R := Function.update S₂.R work Y}) := by
    intro v₂
    obtain ⟨v₃,n₃,hu₃,hn₃,he₃,_⟩ := generatedFinalRound_list_exec (body := body) hA rg hrg ports hports hsep
      (show [work,saved,tmp,ports 0,ports 1,ports 2,ports 3,sp,sg,cy].Nodup by regs_nodup)
      (w := w) (q := q) (p := p) (j := j) (E := E) wl hwl st (hv 0) (hv 1) (hv 2) (hv 3) (hv 4) (hv 5) (hv 6) (hv 7)
      hp hw hsize hroom hfit xs v₂ S₂ htable (by simp [S₂,isolatedPrefixState,X]) hsmall hhead
    exact ⟨v₃,n₃,hu₃,hn₃,he₃⟩
  obtain ⟨v',n,hu,hn,he⟩ := transformPrefix_exec (body := body)
    (show [count,src,work,saved,tmp].Nodup by regs_nodup) _ X Y tail
    (13*tblC B 0+16*w+44*B+38+xs.length*(14*w+23)) v S hsrc
    (by simpa [hX] using hcount) (hblank work (by simp)) (hblank saved (by simp))
    (hblank tmp (by simp)) hrun
  refine ⟨v',n,hu,?_,he⟩
  rw [hX,hY] at hn
  nlinarith only [hn]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
