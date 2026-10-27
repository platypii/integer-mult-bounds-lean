module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRhsGather

/-! Generate the gather clock from the retained boundary cardinality and retire it. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 148 Q A U}

def boundaryRhsPrepare : Pr P 148 Q A U := .seq (ucopy 116 0 1) boundaryRhsGather

def boundaryRhsPrepareCost (V w N s : ℕ) : ℕ := 4*N+4+boundaryRhsGatherCost V w N s

theorem boundaryRhsPrepare_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (V w : ℕ)
    (hA : 4 ≤ A) (hs : s ≤ 2^V) (C : ZMod s → GaussianInt)
    (coordinateTail rhsTail : List (Fin (A+4))) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hN : (S.R 116).length = B.card) (hV : (S.R 115).length = V) (hw : (S.R 94).length = w)
    (hcoordinates : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++coordinateTail)
    (hrhs : S.R 110 = cstream A w (chirpLine s C)++rhsTail)
    (h0 : S.R 0 = []) (h106 : S.R 106 = []) (h139 : S.R 139 = [])
    (hblank : ∀ r : Fin 148, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ boundaryRhsPrepareCost V w B.card s ∧
      Exec body boundaryRhsPrepare (mk v S) n
        (mk v' {S with R := (Function.update S.R 143
          (cstream A w ((List.range B.card).map (fun j => C (bFoldAt s B j)))++S.R 143))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body (a := 116) (b := 0) (t := 1)
    (by decide) (by decide) (by decide) v S (hblank 1 (by decide) (by decide))
  let S₁ : Stacks 148 A := {S with R := Function.update S.R 0 (List.replicate B.card tick)}
  have he₁' : Exec body (ucopy 116 0 1) (mk v S) (4*B.card+4) (mk v₁ S₁) := by
    simpa [S₁,hN,h0] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := boundaryRhsGather_exec (body := body) B V w hA hs C coordinateTail rhsTail v₁ S₁
    (by simp [S₁]) (by simpa [S₁] using hV) (by simpa [S₁] using hw)
    (by simpa [S₁] using hcoordinates) (by simpa [S₁] using hrhs)
    (by simpa [S₁] using h106) (by simpa [S₁] using h139) (by
      intro r hr1 hr7
      simpa [S₁,show r ≠ 0 by omega] using hblank r hr1 hr7)
  refine ⟨v₂,(4*B.card+4)+n₂,hu₂.trans hu₁,Nat.add_le_add_left hn₂ _,(Exec.seq he₁' he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk0 : k = 0 <;> by_cases hk143 : k = 143 <;> simp [S₁,hk0,hk143,h0]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
