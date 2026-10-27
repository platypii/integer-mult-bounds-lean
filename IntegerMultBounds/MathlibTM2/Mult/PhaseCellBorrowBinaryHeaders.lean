module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryHeaderLoad
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Borrow a retained binary header packet, restoring every register outside the table. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A n : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def borrowBinaryHeaders (rg : TblR n → Fin T) (src work count saved tmp : Fin T)
    (fields : List (Fin n)) : Pr P T Q A U :=
  .seq (umul fields.length (rg .wr) count tmp)
    (.seq (copyPrefix count src work saved tmp)
      (.seq (loadBinaryHeaders rg work fields) (uclear count)))

theorem borrowBinaryHeaders_exec {rg : TblR n → Fin T} (hrg : Function.Injective rg)
    (src work count saved tmp : Fin T) (hreg : [src,work,count,saved,tmp].Nodup)
    (hsep : ∀ k ∈ [src,work,count,saved,tmp], ∀ r, rg r ≠ k)
    (rs : List (Fin n × ℕ)) (W : ℕ) (wl nl : List (Fin (A+4))) (hwl : wl.length = W)
    (st : TblSt n A) (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl st))
    (hsrc : S.R src = rs.flatMap (fun r => binSyms (A := A) W r.2)++tail)
    (hcount : S.R count = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ rs.length*(20*W+8)+4*W+17 ∧
      Exec body (borrowBinaryHeaders rg src work count saved tmp (rs.map Prod.fst)) (mk v S) m (mk v' S') ∧
      tblHolds rg S' (tblRho W wl nl (loadedBinaryState rs st)) ∧ tblFr rg S S' := by
  have hr := hreg
  regs_ne hr
  have hwidth : (S.R (rg .wr)).length = W := by rw [hS .wr]; simpa [tblRho] using hwl
  have hpacket : (rs.flatMap (fun r => binSyms (A := A) W r.2)).length = rs.length*W := by
    simp [List.length_flatMap,List.map_map,Function.comp_def]
  obtain ⟨v₁,hu₁,he₁⟩ := umul_exec (body := body) rs.length
    (a := rg .wr) (b := count) (t := tmp) (hsep count (by simp) .wr)
    (hsep tmp (by simp) .wr) ‹count ≠ tmp› v S htmp
  let S₁ : Stacks T A := {S with R := Function.update S.R count (List.replicate (rs.length*W) tick)}
  have he₁' : Exec body (umul rs.length (rg .wr) count tmp) (mk v S)
      (4*W+4) (mk v₁ S₁) := by
    simpa [S₁,hwidth,hcount] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := copyPrefix_exec (body := body)
    (count := count) (src := src) (dst := work) (saved := saved) (tmp := tmp) (by regs_nodup)
    v₁ S₁ (rs.flatMap (fun r => binSyms (A := A) W r.2)) tail
    (by simpa [S₁,‹src ≠ count›] using hsrc) (by simp [S₁,hpacket])
    (by simpa [S₁,‹count ≠ saved›.symm] using hsaved)
    (by simpa [S₁,‹count ≠ tmp›.symm] using htmp)
  let S₂ : Stacks T A := {S₁ with R := (Function.update S₁.R work
    (rs.flatMap (fun r => binSyms (A := A) W r.2)++S.R work))}
  have hh₂ : tblHolds rg S₂ (tblRho W wl nl st) := by
    intro r
    simpa [S₂,S₁,hsep work (by simp) r,hsep count (by simp) r] using hS r
  have he₂' : Exec body (copyPrefix count src work saved tmp) (mk v₁ S₁)
      (10*(rs.length*W)+10) (mk v₂ S₂) := by
    simpa [S₂,S₁,‹work ≠ count›,hpacket] using he₂
  obtain ⟨v₃,S₃,hu₃,he₃,hh₃,hw₃,hi₃,ho₃,hl₃,hf₃⟩ := loadBinaryHeaders_exec (body := body)
    hrg work (hsep work (by simp)) rs W wl nl hwl st (S.R work) v₂ S₂ hh₂ (by simp [S₂])
  have hc₃ : S₃.R count = List.replicate (rs.length*W) tick := by
    rw [hf₃ count ‹work ≠ count›.symm (hsep count (by simp))]
    simp [S₂,S₁,‹work ≠ count›.symm]
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) count v₃ S₃
  let S₄ : Stacks T A := {S₃ with R := Function.update S₃.R count []}
  have he : Exec body (borrowBinaryHeaders rg src work count saved tmp (rs.map Prod.fst)) (mk v S)
      ((4*W+4)+((10*(rs.length*W)+10)+((rs.length*(8*W+8)+1)+(2*(rs.length*W)+2))))
      (mk v₄ S₄) := by
    simpa only [borrowBinaryHeaders,List.length_map,hc₃,List.length_replicate] using
      (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄)))
  refine ⟨v₄,S₄,_,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),by nlinarith,he,?_,?_,?_,?_,?_⟩
  · intro r
    simpa [S₄,hsep count (by simp) r] using hh₃ r
  · exact hi₃
  · exact ho₃
  · exact hl₃
  · intro k hk
    by_cases hkc : k = count
    · subst k; simpa [S₄] using hcount.symm
    by_cases hkw : k = work
    · subst k; simpa [S₄,‹work ≠ count›] using hw₃
    rw [show S₄.R k = S₃.R k by simp [S₄,hkc],hf₃ k hkw hk]
    simp [S₂,S₁,hkw,hkc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
