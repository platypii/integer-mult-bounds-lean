module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Convert the generated weight-page counters to replica cache dimensions.
The replica count is an ordinary unary header in 113, preserved by the factory. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def prepareReplicaFactoryDimensions : Pr P 117 Q A U :=
  .seq (unaryProduct 116 103 64 104 105)
    (.seq (moveR 116 115 id) (.seq (moveR 113 116 id)
      (.seq (uclear 103) (moveR 64 103 id))))

def prepareReplicaFactoryDimensionsCost (N B L : ℕ) : ℕ := 6*(B*L)+11*B+2*N+2*L+12

def replicaFactoryDimensionsBank {A : ℕ} (S : Stacks 117 A) (N B L : ℕ) : Stacks 117 A :=
  {S with R := (Function.update (Function.update (Function.update (Function.update S.R
    103 (List.replicate (B*L) tick)) 116 (List.replicate N tick))
    115 (List.replicate B tick)) 113 [])}

theorem prepareReplicaFactoryDimensions_native :
    mnNativePushBound 2 (prepareReplicaFactoryDimensions (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [prepareReplicaFactoryDimensions,unaryProduct,ucopy,umulSym,scanP,scanR,
    drainR,popDo,keepIn,pushN,popPush,moveR,moveStep,whileR,peekR,uclear,
    mnNativePushBound,mnActPush]

theorem prepareReplicaFactoryDimensions_exec (N B L : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hN : S.R 113 = List.replicate N tick) (hB : S.R 116 = List.replicate B tick)
    (hL : (S.R 103).length = L) (h64 : S.R 64 = []) (h115 : S.R 115 = [])
    (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareReplicaFactoryDimensionsCost N B L ∧
      Exec body prepareReplicaFactoryDimensions (mk v S) n
        (mk v' (replicaFactoryDimensionsBank S N B L)) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (show [(116 : Fin 117),103,64,104,105].Nodup by decide) v S h104 h105
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 64 (List.replicate (B*L) tick)}
  have he₁' : Exec body (unaryProduct 116 103 64 104 105) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hB,hL,h64] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body 116 115 (by decide) id v₁ S₁
  let S₂ : Stacks 117 A := {S₁ with R := movedR S₁.R 116 115 id (S₁.R 116)}
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body 113 116 (by decide) id v₂ S₂
  let S₃ : Stacks 117 A := {S₂ with R := movedR S₂.R 113 116 id (S₂.R 113)}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec body 103 v₃ S₃
  let S₄ : Stacks 117 A := {S₃ with R := Function.update S₃.R 103 []}
  obtain ⟨v₅,hu₅,he₅⟩ := moveR_exec body 64 103 (by decide) id v₄ S₄
  refine ⟨v₅,n₁+((2*(S₁.R 116).length+2)+((2*(S₂.R 113).length+2)+
    ((2*(S₃.R 103).length+2)+(2*(S₄.R 64).length+2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,?_⟩
  · simp only [hB,List.length_replicate,hL] at hn₁
    simp [S₄,S₃,S₂,S₁,movedR,hB,hN,hL,prepareReplicaFactoryDimensionsCost]
    nlinarith only [hn₁]
  · refine (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast rfl ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h103 : k = 103 <;> by_cases h113 : k = 113 <;>
        by_cases h116 : k = 116 <;> by_cases h115' : k = 115 <;> by_cases h64' : k = 64 <;>
        simp [S₄,S₃,S₂,S₁,movedR,replicaFactoryDimensionsBank,
          h103,h113,h116,h115',h64',hN,hB,h64,h115]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
