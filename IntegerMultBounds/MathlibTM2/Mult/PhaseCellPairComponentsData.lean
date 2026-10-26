module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairComponents

/-! Encoding and accuracy of paired real-component words. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def pairComponentWord (x y : GaussianInt) : GaussianInt := ⟨x.re,y.re⟩

theorem pairComponentSymbol_csyms {A : ℕ} (hA : 4 ≤ A) (w : ℕ) (x y : GaussianInt) :
    List.zipWith pairComponentSymbol (csyms A w x) (csyms A w y) =
      csyms A w (pairComponentWord x y) := by
  apply List.ext_getElem
  · simp [csyms]
  · intro i hi hj
    simp [List.getElem_zipWith,csyms,coeffSyms,pairComponentSymbol,pairComponentWord,
      pairRe_pairSym hA,red]

theorem pairComponentSymbol_cstream {A : ℕ} (hA : 4 ≤ A) (w : ℕ) (xs ys : List GaussianInt)
    (hlen : xs.length = ys.length) :
    List.zipWith pairComponentSymbol (cstream A w xs) (cstream A w ys) =
      cstream A w (List.zipWith pairComponentWord xs ys) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [cstream]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons,Nat.succ.injEq] at hlen
      simp only [cstream_cons,List.zipWith_cons_cons]
      rw [List.zipWith_append (by simp [csyms]),pairComponentSymbol_csyms hA,ih ys hlen]

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def pairComponentsToFirst (count x y tmp : Fin T) : Pr P₀ T Q A U :=
  .seq (pairComponents count x y tmp) (moveR tmp x id)

theorem pairComponentsToFirst_exec {count x y tmp : Fin T} (hreg : [count,x,y,tmp].Nodup)
    (hA : 4 ≤ A) (w : ℕ) (xs ys : List GaussianInt) (hlen : xs.length = ys.length)
    (tailX tailY : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hc : (S.R count).length = xs.length*w)
    (hx : S.R x = cstream A w xs++tailX) (hy : S.R y = cstream A w ys++tailY)
    (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 6*xs.length*w+4 ∧
      Exec body (pairComponentsToFirst count x y tmp) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          y tailY) x (cstream A w (List.zipWith pairComponentWord xs ys)++tailX)) count [])}) := by
  have hr := hreg
  regs_ne hr
  let X := cstream A w xs
  let Y := cstream A w ys
  let Z := cstream A w (List.zipWith pairComponentWord xs ys)
  have hX : X.length = xs.length*w := by simp [X,length_cstream]
  have hY : Y.length = X.length := by simp [X,Y,length_cstream,hlen]
  have hZ : Z.length = X.length := by simp [Z,X,length_cstream,hlen]
  have hzip : List.zipWith pairComponentSymbol X Y = Z := pairComponentSymbol_cstream hA w xs ys hlen
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := pairComponents_exec (body := body)
    (count := count) (x := x) (y := y) (dst := tmp) (by regs_nodup)
    X Y tailX tailY hY.symm v S (by simpa [hX] using hc) hx hy
  let S₁ : Stacks T A := {S with R := Function.update (Function.update (Function.update (Function.update
    S.R x tailX) y tailY) tmp Z.reverse) count []}
  have he₁' : Exec body (pairComponents count x y tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hzip,htmp] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body tmp x ‹x ≠ tmp›.symm id v₁ S₁
  refine ⟨v₂,n₁+(2*Z.length+2),hu₂.trans hu₁,?_,(Exec.seq he₁' he₂).cast ?_ ?_⟩
  · rw [hZ,hX]
    rw [hX] at hn₁
    nlinarith only [hn₁]
  · simp [S₁,‹count ≠ tmp›.symm]
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hc : k = count <;> by_cases hx : k = x <;> by_cases hy : k = y <;> by_cases ht : k = tmp <;>
      simp_all [S₁,movedR,Z,ne_comm]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
