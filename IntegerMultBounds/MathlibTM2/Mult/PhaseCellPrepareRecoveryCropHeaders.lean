module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Compute crop/archive controls from retained precision and endpoints and
ordinary offset, row-count and replica headers. Payload and spectators restore. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 19 Q A U}

/-- Borrowed ports 0--5 are q, origin, end, offset, rows and replicas.
Generated ports 6--10 are word width, span, skip symbols, row symbols and clock. -/
def prepareRecoveryCropHeaders : Pr P 19 Q A U :=
  .seq (generateWordWidth 0 6 15)
    (.seq (ucopy 2 7 15) (.seq (usub 1 7 15)
      (.seq (unaryProduct 3 6 8 17 15)
        (.seq (unaryProduct 4 6 9 17 15) (ucopy 5 10 15)))))

def prepareRecoveryCropHeadersCost (q a b offset rows N : ℕ) : ℕ :=
  (8*q+9)+(4*b+4)+(4*a+4)+(offset*(4*(2*q+8)+9)+4)+
    (rows*(4*(2*q+8)+9)+4)+(4*N+4)

def recoveryCropHeaderState (q a b offset rows N : ℕ) (S : Stacks 19 A) : Stacks 19 A :=
  {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update S.R
    6 (List.replicate (2*q+8) tick)) 7 (List.replicate (b-a) tick))
      8 (List.replicate (offset*(2*q+8)) tick)) 9 (List.replicate (rows*(2*q+8)) tick))
      10 (List.replicate N tick))}

theorem prepareRecoveryCropHeaders_exec (q a b offset rows N : ℕ) (v : HS 19 Q A U) (S : Stacks 19 A)
    (hq : (S.R 0).length = q) (ha : (S.R 1).length = a) (hb : (S.R 2).length = b)
    (hoffset : (S.R 3).length = offset) (hrows : (S.R 4).length = rows) (hN : (S.R 5).length = N)
    (hblank : ∀ k ∈ ([(6 : Fin 19),7,8,9,10,15,17]), S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareRecoveryCropHeadersCost q a b offset rows N ∧
      Exec body prepareRecoveryCropHeaders (Host.mk v S) n
        (Host.mk v' (recoveryCropHeaderState q a b offset rows N S)) := by
  obtain ⟨v₁,hu₁,he₁⟩ := generateWordWidth_exec (body := body)
    (show ([(0 : Fin 19),6,15]).Nodup by decide) q v S hq (hblank 6 (by simp)) (hblank 15 (by simp))
  let S₁ : Stacks 19 A := {S with R := Function.update S.R 6 (List.replicate (2*q+8) tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := body) (a := 2) (b := 7) (t := 15)
    (by decide) (by decide) (by decide) v₁ S₁ (by simp [S₁,hblank 15 (by simp)])
  let S₂ : Stacks 19 A := {S₁ with R := Function.update S₁.R 7 (List.replicate b tick)}
  have he₂' : Exec body (ucopy 2 7 15) (Host.mk v₁ S₁) (4*b+4) (Host.mk v₂ S₂) := by
    simpa [S₂,S₁,hb,hblank 7 (by simp)] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := usub_exec (body := body) (a := 1) (b := 7) (t := 15)
    (by decide) (by decide) (by decide) v₂ S₂ (by simp [S₂,S₁,hblank 15 (by simp)])
  let S₃ : Stacks 19 A := {S₂ with R := Function.update S₂.R 7 (List.replicate (b-a) tick)}
  have he₃' : Exec body (usub 1 7 15) (Host.mk v₂ S₂) (4*a+4) (Host.mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,ha] using he₃
  obtain ⟨v₄,n₄,hu₄,hn₄,he₄⟩ := unaryProduct_exec (body := body)
    (show ([(3 : Fin 19),6,8,17,15]).Nodup by decide) v₃ S₃
    (by simp [S₃,S₂,S₁,hblank 17 (by simp)]) (by simp [S₃,S₂,S₁,hblank 15 (by simp)])
  let S₄ : Stacks 19 A := {S₃ with R := Function.update S₃.R 8 (List.replicate (offset*(2*q+8)) tick)}
  have he₄' : Exec body (unaryProduct 3 6 8 17 15) (Host.mk v₃ S₃) n₄ (Host.mk v₄ S₄) := by
    simpa [S₄,S₃,S₂,S₁,hoffset,hblank 8 (by simp)] using he₄
  have hn₄' : n₄ ≤ offset*(4*(2*q+8)+9)+4 := by simpa [S₃,S₂,S₁,hoffset] using hn₄
  obtain ⟨v₅,n₅,hu₅,hn₅,he₅⟩ := unaryProduct_exec (body := body)
    (show ([(4 : Fin 19),6,9,17,15]).Nodup by decide) v₄ S₄
    (by simp [S₄,S₃,S₂,S₁,hblank 17 (by simp)]) (by simp [S₄,S₃,S₂,S₁,hblank 15 (by simp)])
  let S₅ : Stacks 19 A := {S₄ with R := Function.update S₄.R 9 (List.replicate (rows*(2*q+8)) tick)}
  have he₅' : Exec body (unaryProduct 4 6 9 17 15) (Host.mk v₄ S₄) n₅ (Host.mk v₅ S₅) := by
    simpa [S₅,S₄,S₃,S₂,S₁,hrows,hblank 9 (by simp)] using he₅
  have hn₅' : n₅ ≤ rows*(4*(2*q+8)+9)+4 := by simpa [S₄,S₃,S₂,S₁,hrows] using hn₅
  obtain ⟨v₆,hu₆,he₆⟩ := ucopy_exec (body := body) (a := 5) (b := 10) (t := 15)
    (by decide) (by decide) (by decide) v₅ S₅ (by simp [S₅,S₄,S₃,S₂,S₁,hblank 15 (by simp)])
  have he₆' : Exec body (ucopy 5 10 15) (Host.mk v₅ S₅) (4*N+4)
      (Host.mk v₆ (recoveryCropHeaderState q a b offset rows N S)) := by
    simpa [recoveryCropHeaderState,S₅,S₄,S₃,S₂,S₁,hN,hblank 10 (by simp)] using he₆
  refine ⟨v₆,_,hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),?_,
    Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' (Exec.seq he₅' he₆'))))⟩
  unfold prepareRecoveryCropHeadersCost
  omega

theorem prepareRecoveryCropHeaders_native :
    mnNativePushBound 8 (prepareRecoveryCropHeaders (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [prepareRecoveryCropHeaders,generateWordWidth,ucopy,usub,dropTop,unaryProduct,
    scanP,popPush,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,whileR,moveStep,peekR,
    mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
