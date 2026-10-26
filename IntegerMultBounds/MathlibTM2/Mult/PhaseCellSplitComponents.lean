module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairComponentsData

/-! Split an owned complex prefix into real inputs while preserving both borrowed suffixes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

def imagPartWord (z : GaussianInt) : GaussianInt := ⟨z.im,0⟩

def imagPartSymbol {A : ℕ} (x : Fin (A+4)) : Fin (A+4) := pairSym A (pairIm x) false

theorem imagPartSymbol_csyms {A : ℕ} (hA : 4 ≤ A) (w : ℕ) (z : GaussianInt) :
    (csyms A w z).map imagPartSymbol = csyms A w (imagPartWord z) := by
  simp [csyms,coeffSyms,List.map_ofFn,Function.comp_def,imagPartSymbol,
    pairIm_pairSym hA,imagPartWord,red]

theorem imagPartSymbol_cstream {A : ℕ} (hA : 4 ≤ A) (w : ℕ) (zs : List GaussianInt) :
    (cstream A w zs).map imagPartSymbol = cstream A w (zs.map imagPartWord) := by
  induction zs with
  | nil => simp
  | cons z zs ih => simp [ih,imagPartSymbol_csyms hA]

@[simp] theorem pairComponentWord_parts (z : GaussianInt) :
    pairComponentWord (realPartWord z) (imagPartWord z) = z := by cases z; rfl

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def splitComponentPrefix (count src dst saved tmp : Fin T) : Pr P₀ T Q A U :=
  .seq (transfer count src saved tmp)
    (.seq (copyR saved dst tmp imagPartSymbol) (moveR saved src realPartSymbol))

theorem splitComponentPrefix_exec {count src dst saved tmp : Fin T}
    (hreg : [count,src,dst,saved,tmp].Nodup) (hA : 4 ≤ A) (w : ℕ) (zs : List GaussianInt)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w zs++tail) (hlen : (S.R count).length = zs.length*w)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (splitComponentPrefix count src dst saved tmp) (mk v S) (10*zs.length*w+10)
        (mk v' {S with R := (Function.update (Function.update S.R
          src (cstream A w (zs.map realPartWord)++tail))
          dst (cstream A w (zs.map imagPartWord)++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  let xs := cstream A w zs
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body)
    (count := count) (src := src) (dst := saved) (tmp := tmp) (by regs_nodup)
    v S xs tail hsrc (by simpa [xs] using hlen) htmp
  let S₁ : Stacks T A := {S with R := Function.update (Function.update S.R src tail) saved xs.reverse}
  have he₁' : Exec body (transfer count src saved tmp) (mk v S) (4*xs.length+4) (mk v₁ S₁) := by
    simpa [S₁,hsaved] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := copyR_exec body saved dst tmp ‹dst ≠ saved›.symm ‹saved ≠ tmp›
    ‹dst ≠ tmp› imagPartSymbol v₁ S₁ (by simp [S₁,‹src ≠ tmp›.symm,‹saved ≠ tmp›.symm,htmp])
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R dst ((xs.map imagPartSymbol)++S.R dst)}
  have he₂' : Exec body (copyR saved dst tmp imagPartSymbol) (mk v₁ S₁) (4*xs.length+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,‹dst ≠ saved›,‹src ≠ dst›.symm,List.map_reverse] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body saved src ‹src ≠ saved›.symm realPartSymbol v₂ S₂
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),(Exec.seq he₁' (Exec.seq he₂' he₃)).cast ?_ ?_⟩
  · simp [S₂,S₁,‹dst ≠ saved›.symm,xs]
    ring
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hsrc' : k = src <;> by_cases hdst : k = dst <;> by_cases hsaved' : k = saved <;>
      simp_all [S₂,S₁,movedR,List.map_reverse,xs,realPartSymbol_cstream hA,imagPartSymbol_cstream hA,ne_comm]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
