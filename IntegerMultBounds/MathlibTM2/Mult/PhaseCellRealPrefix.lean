module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvDecode

/-! Execute real projection on an owned prefix, preserving its order and borrowed suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def realPartWord (z : GaussianInt) : GaussianInt := ⟨z.re,0⟩

def realPartSymbol {A : ℕ} (x : Fin (A+4)) : Fin (A+4) := pairSym A (pairRe x) false

theorem realPartSymbol_csyms {A : ℕ} (hA : 4 ≤ A) (w : ℕ) (z : GaussianInt) :
    (csyms A w z).map realPartSymbol = csyms A w (realPartWord z) := by
  simp [csyms,coeffSyms,List.map_ofFn,Function.comp_def,realPartSymbol,
    pairRe_pairSym hA,realPartWord,red]

theorem realPartSymbol_cstream {A : ℕ} (hA : 4 ≤ A) (w : ℕ) (zs : List GaussianInt) :
    (cstream A w zs).map realPartSymbol = cstream A w (zs.map realPartWord) := by
  induction zs with
  | nil => simp
  | cons z zs ih => simp [ih,realPartSymbol_csyms hA]

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def realPrefix (count src saved tmp : Fin T) : Pr P₀ T Q A U :=
  .seq (transfer count src saved tmp) (moveR saved src realPartSymbol)

theorem realPrefix_exec {count src saved tmp : Fin T}
    (hreg : [count,src,saved,tmp].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (xs tail : List (Fin (A+4))) (hsrc : S.R src = xs++tail)
    (hlen : (S.R count).length = xs.length) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧ Exec body (realPrefix count src saved tmp) (mk v S)
      (6*xs.length+6) (mk v' {S with R := Function.update S.R src (xs.map realPartSymbol++tail)}) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body) hreg v S xs tail hsrc hlen htmp
  let S₁ : Stacks T A := {S with R := (Function.update (Function.update S.R src tail)
    saved (xs.reverse++S.R saved))}
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body saved src ‹src ≠ saved›.symm realPartSymbol v₁ S₁
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast ?_ ?_⟩
  · simp [S₁,hsaved]
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hsrc' : k = src <;> by_cases hsaved' : k = saved <;>
      simp_all [S₁,movedR,List.map_reverse]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
