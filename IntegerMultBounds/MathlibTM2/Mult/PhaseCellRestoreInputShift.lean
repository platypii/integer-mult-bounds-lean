module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputShiftInverse
public import IntegerMultBounds.MathlibTM2.Mult.SignedWidenExec

/-! Undo exact input conversion and restore the source's original physical word width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def restoreInputShift (src dst tmp cW cS cE cD sp sg cy : Fin T) : Pr P T Q A U :=
  .seq (topPass src dst (topShiftWord src dst tmp cW cS cE cD sp sg cy))
    (topPass src dst (topWidenWord src dst cE cS sp))

theorem restoreInputShift_exec (hA : 4 ≤ A) {src dst tmp cW cS cE cD sp sg cy : Fin T}
    (hreg : [src,dst,tmp,cW,cS,cE,cD,sp,sg,cy].Nodup)
    (w d : ℕ) (hd : d < w) (xs : List GaussianInt)
    (hxs : ∀ z ∈ xs, TopFitsZ (w-d) z)
    (hshifted : ∀ z ∈ xs, TopFitsZ w ((2 : GaussianInt)^d*z))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w (xs.map fun z => (2 : GaussianInt)^d*z))
    (hdst : S.R dst = []) (hg : topShiftG tmp cW cS cE cD sp sg cy w d (w-d) S.R) :
    ∃ v' n, v'.user = v.user ∧ n ≤ xs.length*(20*w+44)+8 ∧
      Exec body (restoreInputShift src dst tmp cW cS cE cD sp sg cy) (mk v S) n
        (mk v' {S with R := (Function.update S.R src (cstream A w xs))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := signedRound_exec (body := body) hA hreg w d (w-d) (by omega) (by omega)
    (xs.map fun z => (2 : GaussianInt)^d*z) (by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
      exact hshifted x hx) v S hsrc hdst hg
  let S₁ : Stacks T A := {S with R := Function.update S.R src (cstream A (w-d) xs)}
  have he₁' : Exec body (topPass src dst (topShiftWord src dst tmp cW cS cE cD sp sg cy))
      (mk v S) (1+(xs.length*(topShiftWordCost w d (w-d)+1)+1)+(2*(xs.length*(w-d))+2))
      (mk v₁ S₁) := by
    simpa only [List.length_map,inputShift_roundtrip] using he₁
  have hwiden : topWidenG cE cS sp (w-d) w S₁.R := by
    rcases hg with ⟨hW,hD,hK,hDrop,hsp,hsg,hcy,htmp⟩
    have heq : w-(w-d) = d := by omega
    simp only [topWidenG,S₁,Function.update_of_ne ‹src ≠ cE›.symm,
      Function.update_of_ne ‹src ≠ cS›.symm,Function.update_of_ne ‹src ≠ sp›.symm,heq]
    exact ⟨hK,hD,hsp⟩
  obtain ⟨v₂,hu₂,he₂⟩ := signedWiden_exec (body := body)
    (show [src,dst,cE,cS,sp].Nodup by regs_nodup) (w-d) w (by omega) (by omega) xs hxs v₁ S₁
    (by simp only [S₁,Function.update_self])
    (by simpa only [S₁,Function.update_of_ne ‹src ≠ dst›.symm] using hdst) hwiden
  have he := Exec.seq he₁' he₂
  refine ⟨v₂,_,hu₂.trans hu₁,?_,he.cast rfl ?_⟩
  · unfold topShiftWordCost
    have hsum : d+(w-d) = w := by omega
    have hdrop : w-d-(w-d) = 0 := by omega
    have hcomp : w-(w-d) = d := by omega
    rw [hdrop,hcomp]
    have hscaled := congrArg (fun n => xs.length*n) hsum
    nlinarith only [hscaled,Nat.zero_le (xs.length*d)]
  · congr 1
    simp only [S₁,Function.update_idem]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
