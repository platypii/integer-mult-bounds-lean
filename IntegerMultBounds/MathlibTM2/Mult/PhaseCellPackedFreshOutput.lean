module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellZeroWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundedEncodedStream
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Allocate the next packed output above previously completed outputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

def packedFreshOutput : Pr P 248 Q A U :=
  .seq (toUnary 165 246 0 1 2)
    (.seq (zeroWords 246 174 132 247 242 243) (uclear 246))

def packedFreshOutputCost (V N w : ℕ) : ℕ :=
  6*N+11*V+6+(10*N*w+9*N+10)+(2*N+2)

theorem packedFreshOutput_exec (V N w : ℕ) (hNV : N < 2^V)
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hN : S.R 165 = binSyms V N) (hw : (S.R 174).length = w)
    (hclean : ∀ i ∈ ([0,1,2,246,247,242,243] : List (Fin 248)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ packedFreshOutputCost V N w ∧
      Exec body packedFreshOutput (mk v S) n
        (mk v' {S with R := Function.update S.R 132 (cstream A w (List.replicate N 0)++S.R 132)}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toUnary_exec_linear (body := body)
    (a := 165) (z := 246) (w := 0) (t := 1) (t₂ := 2) (by decide) hNV v S hN
    (hclean 0 (by decide)) (hclean 1 (by decide)) (hclean 2 (by decide))
  let S₁ : Stacks 248 A := {S with R := Function.update S.R 246 (List.replicate N tick)}
  have he₁' : Exec body (toUnary 165 246 0 1 2) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hclean 246 (by decide),List.append_nil] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := zeroWords_exec (body := body)
    (rows := 246) (width := 174) (dst := 132) (count := 247) (saved := 242) (tmp := 243)
    (by decide) N w v₁ S₁ (by simp [S₁]) (by simpa [S₁] using hw)
    (by simpa [S₁] using hclean 247 (by decide))
    (by simpa [S₁] using hclean 242 (by decide))
    (by simpa [S₁] using hclean 243 (by decide))
  let S₂ : Stacks 248 A := {S₁ with R := Function.update S₁.R 132 (cstream A w (List.replicate N 0)++S₁.R 132)}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 246 v₂ S₂
  have hcount : (S₂.R 246).length = N := by simp [S₂,S₁]
  refine ⟨v₃,n₁+(n₂+(2*N+2)),hu₃.trans (hu₂.trans hu₁),by
    dsimp only [packedFreshOutputCost]; omega,?_⟩
  refine (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hcount]) ?_
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi : i = 246 <;> by_cases hj : i = 132 <;>
    simp [S₂,S₁,hi,hj,hclean 246 (by decide)]

theorem packedFreshOutput_range (A w q e N : ℕ) :
    EncodedRange A w q e (cstream A w (List.replicate N 0)) := by
  refine ⟨List.replicate N 0,rfl,?_⟩
  intro z hz
  have hz0 : z = 0 := (List.mem_replicate.mp hz).2
  subst z
  have hzero : value q (0 : GaussianInt) = 0 := by apply Complex.ext <;> simp [value]
  rw [hzero]
  simp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
