module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyComplexBatchProgram
public import IntegerMultBounds.MathlibTM2.StackCallResources

/-! Compose the live loop with its initialization and finish, charging scratch once. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Node
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 263 Q A U}

theorem familyComplexBatch_certify (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    {S S₁ S₂ S₃ S₄ : Store (HΓ (T := 263) A) (HS 263 Q A U)}
    {m₁ m₂ m₃ m₄ s w N K : ℕ}
    (he₁ : Exec body (unaryProduct 121 160 243 245 244) S m₁ S₁)
    (hn₁ : m₁ ≤ s*(4*w+9)+4)
    (he₂ : Exec body (ucopy 246 240 244) S₁ m₂ S₂) (hn₂ : m₂ ≤ 4*N+4)
    (hloop : ∀ C, mnProgPush (familyComplexBatchStep (P := P) (U := U) (A := A) recovery hR hQ) ≤ C →
      (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize S₂+N*s*w+depth+(C+1)*K)
        depth (countedLoop 240 (familyComplexBatchStep recovery hR hQ)) S₂ m₃ S₃)
    (he₄ : Exec body familyComplexBatchFinish S₃ m₄ S₄)
    (hn₄ : m₄ ≤ 4*(N*s*w)+2*(s*w)+6) :
    ∀ C, mnProgPush (familyComplexBatch (P := P) (U := U) (A := A) recovery hR hQ) ≤ C →
      (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize S+depth+(C+1)*familyComplexBatchStockCost s w N K)
        depth (familyComplexBatch recovery hR hQ) S (m₁+(m₂+(m₃+m₄))) S₄ := by
  intro C hp hb depth
  change max (mnProgPush (unaryProduct 121 160 243 245 244))
    (max (mnProgPush (ucopy 246 240 244))
      (max (mnProgPush (countedLoop 240 (familyComplexBatchStep recovery hR hQ)))
        (mnProgPush familyComplexBatchFinish))) ≤ C at hp
  obtain ⟨hp₁,hpTail⟩ := max_le_iff.mp hp
  obtain ⟨hp₂,hpTail⟩ := max_le_iff.mp hpTail
  obtain ⟨hp₃,hp₄⟩ := max_le_iff.mp hpTail
  change max (mnProgPush (.act (peekR 240)))
    (max (mnProgPush (.act (.pop (.rt 240) (fun v _ => v) .done)))
      (max (mnProgPush (familyComplexBatchStep recovery hR hQ))
        (mnProgPush (.act (peekR 240))))) ≤ C at hp₃
  have hpstep := (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp hp₃).2).2).1
  have ht := hloop C hpstep hb depth
  have ht₀ : mnSize S₃+0 ≤ mnSize S₂+N*s*w+0+(C+1)*K :=
    (hloop C hpstep hb 0).final
  simp only [Nat.add_zero] at ht₀
  have hs₁ := mn_exec_size he₁ hp₁ hb
  have hs₂ := mn_exec_size (Exec.seq he₁ he₂) (show mnProgPush (.seq _ _) ≤ C from max_le hp₁ hp₂) hb
  let I := s*(4*w+9)+4
  let J := 4*N+4
  let O := N*s*w
  let F := 4*(N*s*w)+2*(s*w)+6
  have htotal : familyComplexBatchStockCost s w N K = I+J+O+F+K := rfl
  change m₁ ≤ I at hn₁
  change m₂ ≤ J at hn₂
  change m₄ ≤ F at hn₄
  change mnSize S₃ ≤ mnSize S₂+O+(C+1)*K at ht₀
  have hw₁ := mn_exec_within he₁ hp₁ hb depth
    (mnSize S+depth+(C+1)*familyComplexBatchStockCost s w N K)
    (by rw [htotal]; nlinarith only [hn₁])
  have hw₂ := mn_exec_within he₂ hp₂ hb depth
    (mnSize S+depth+(C+1)*familyComplexBatchStockCost s w N K)
    (by rw [htotal]; nlinarith only [hs₁,hn₁,hn₂])
  have hw₃ : ExecWithin body (fun d z => mnSize z+d ≤ mnSize S+depth+
      (C+1)*familyComplexBatchStockCost s w N K) depth
      (countedLoop 240 (familyComplexBatchStep recovery hR hQ)) S₂ m₃ S₃ := by
    apply ht.mono
    intro d z hz
    change mnSize z+d ≤ mnSize S₂+O+depth+(C+1)*K at hz
    rw [htotal]
    nlinarith only [hs₂,hn₁,hn₂,hz]
  have hw₄ := mn_exec_within he₄ hp₄ hb depth
    (mnSize S+depth+(C+1)*familyComplexBatchStockCost s w N K)
    (by rw [htotal]; nlinarith only [hs₂,ht₀,hn₁,hn₂,hn₄])
  exact .seq hw₁ (.seq hw₂ (.seq hw₃ hw₄))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
