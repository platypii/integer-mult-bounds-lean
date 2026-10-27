module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix

/-! Pad an owned word prefix with its cyclic suffix and prefix, preserving its borrowed tail. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def padPrefixInPlace (full band skip src dst savedSkip saved tmp buf : Fin T) : Pr P T Q A U :=
  .seq (copyPrefix band src dst saved tmp)
    (.seq (copyPrefix full src dst saved tmp)
      (.seq (copySlice skip band src dst savedSkip saved tmp)
        (.seq (discardPrefix full src saved tmp)
          (.seq (moveR dst buf id) (moveR buf src id)))))

theorem padPrefixInPlace_exec {full band skip src dst savedSkip saved tmp buf : Fin T}
    (hreg : [full,band,skip,src,dst,savedSkip,saved,tmp,buf].Nodup)
    (w b : ℕ) (xs : List GaussianInt) (hb : b ≤ xs.length) (tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hfull : (S.R full).length = xs.length*w) (hband : (S.R band).length = b*w)
    (hskip : (S.R skip).length = (xs.length-b)*w)
    (hsrc : S.R src = cstream A w xs++tail)
    (hfresh : ∀ k ∈ [dst,savedSkip,saved,tmp,buf], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ (26*xs.length+28*b)*w+46 ∧
      Exec body (padPrefixInPlace full band skip src dst savedSkip saved tmp buf) (mk v S) m
        (mk v' {S with R := (Function.update S.R src
          (cstream A w (xs.drop (xs.length-b)++xs++xs.take b)++tail))}) := by
  have hr := hreg
  regs_ne hr
  have hdst : S.R dst = [] := hfresh dst (by simp)
  have hbuf : S.R buf = [] := hfresh buf (by simp)
  let first := cstream A w (xs.take b)
  let last := cstream A w (xs.drop (xs.length-b))
  let words := cstream A w xs
  have hfirst : first.length = b*w := by simp [first,Nat.min_eq_left hb]
  have hlast : last.length = b*w := by simp [last]; omega
  have hwords : words.length = xs.length*w := by simp [words]
  have hprefix : S.R src = first++(cstream A w (xs.drop b)++tail) := by
    rw [hsrc,← List.append_assoc,← cstream_append,List.take_append_drop]
  obtain ⟨v₁,hu₁,he₁⟩ := copyPrefix_exec (body := body)
    (count := band) (src := src) (dst := dst) (saved := saved) (tmp := tmp) (by regs_nodup)
    v S first (cstream A w (xs.drop b)++tail) hprefix (hband.trans hfirst.symm)
    (hfresh saved (by simp)) (hfresh tmp (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R dst first}
  have he₁' : Exec body (copyPrefix band src dst saved tmp) (mk v S) (10*(b*w)+10) (mk v₁ S₁) := by
    simpa [S₁,hfirst,hfresh dst (by simp)] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := copyPrefix_exec (body := body)
    (count := full) (src := src) (dst := dst) (saved := saved) (tmp := tmp) (by regs_nodup)
    v₁ S₁ words tail (by simpa [S₁,‹src ≠ dst›] using hsrc)
    (by simpa [S₁,‹full ≠ dst›,hwords] using hfull)
    (by simpa [S₁,‹dst ≠ saved›.symm] using hfresh saved (by simp))
    (by simpa [S₁,‹dst ≠ tmp›.symm] using hfresh tmp (by simp))
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R dst (words++first)}
  have he₂' : Exec body (copyPrefix full src dst saved tmp) (mk v₁ S₁) (10*words.length+10) (mk v₂ S₂) := by
    simpa [S₂,S₁] using he₂
  have hslice : S₂.R src = cstream A w (xs.take (xs.length-b))++last++tail := by
    simp only [S₂,S₁,Function.update_of_ne ‹src ≠ dst›]
    dsimp only [last]
    rw [hsrc,← cstream_append,List.take_append_drop]
  obtain ⟨v₃,hu₃,he₃⟩ := copySlice_exec (body := body)
    (skip := skip) (count := band) (src := src) (dst := dst) (savedSkip := savedSkip)
    (saved := saved) (tmp := tmp) (by regs_nodup) v₂ S₂
    (cstream A w (xs.take (xs.length-b))) last tail hslice
    (by simpa [S₂,S₁,‹skip ≠ dst›,Nat.min_eq_left (Nat.sub_le xs.length b)] using hskip)
    (by simpa [S₂,S₁,‹band ≠ dst›,hlast] using hband)
    (by simpa [S₂,S₁,‹dst ≠ savedSkip›.symm] using hfresh savedSkip (by simp))
    (by simpa [S₂,S₁,‹dst ≠ saved›.symm] using hfresh saved (by simp))
    (by simpa [S₂,S₁,‹dst ≠ tmp›.symm] using hfresh tmp (by simp))
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R dst (last++(words++first))}
  have he₃' : Exec body (copySlice skip band src dst savedSkip saved tmp) (mk v₂ S₂)
      (6*(cstream A w (xs.take (xs.length-b))).length+10*last.length+16) (mk v₃ S₃) := by
    simpa [S₃,S₂,S₁] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := discardPrefix_exec (body := body)
    (count := full) (src := src) (trash := saved) (tmp := tmp) (by regs_nodup)
    words tail v₃ S₃ (by simpa [S₃,S₂,S₁,‹src ≠ dst›] using hsrc)
    (by simpa [S₃,S₂,S₁,‹full ≠ dst›,hwords] using hfull)
    (by simpa [S₃,S₂,S₁,‹dst ≠ saved›.symm] using hfresh saved (by simp))
    (by simpa [S₃,S₂,S₁,‹dst ≠ tmp›.symm] using hfresh tmp (by simp))
  let S₄ : Stacks T A := {S₃ with R := Function.update S₃.R src tail}
  obtain ⟨v₅,hu₅,he₅⟩ := moveR_exec body dst buf ‹dst ≠ buf› id v₄ S₄
  let S₅ : Stacks T A := {S₄ with R := movedR S₄.R dst buf id (S₄.R dst)}
  obtain ⟨v₆,hu₆,he₆⟩ := moveR_exec body buf src ‹src ≠ buf›.symm id v₅ S₅
  refine ⟨v₆,(10*(b*w)+10)+((10*words.length+10)+
    ((6*(cstream A w (xs.take (xs.length-b))).length+10*last.length+16)+
    ((6*words.length+6)+((2*(S₄.R dst).length+2)+(2*(S₅.R buf).length+2))))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄ (Exec.seq he₅ he₆))))).cast rfl ?_⟩
  · have hsub : (xs.length-b)*w ≤ xs.length*w := Nat.mul_le_mul_right w (Nat.sub_le _ _)
    simp [S₅,S₄,S₃,S₂,S₁,movedR,
      Function.update_of_ne ‹src ≠ dst›.symm,Function.update_of_ne ‹src ≠ buf›.symm,
      Function.update_of_ne ‹dst ≠ buf›.symm,List.map_id,hfresh buf (by simp),
      List.append_nil,List.length_append,List.length_reverse,hfirst,hlast,hwords,
      length_cstream,List.length_take,Nat.min_eq_left (Nat.sub_le xs.length b)]
    nlinarith only [hsub]
  · apply congrArg (mk v₆)
    refine Stacks.ext rfl rfl rfl ?_
    have hbs : buf ≠ src := ‹src ≠ buf›.symm
    have hbd : buf ≠ dst := ‹dst ≠ buf›.symm
    have hds : dst ≠ src := ‹src ≠ dst›.symm
    funext k
    by_cases hs : k = src <;> by_cases hd : k = dst <;> by_cases hb' : k = buf <;>
      simp_all [S₅,S₄,S₃,S₂,S₁,movedR,first,last,words,cstream_append,List.append_assoc,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
