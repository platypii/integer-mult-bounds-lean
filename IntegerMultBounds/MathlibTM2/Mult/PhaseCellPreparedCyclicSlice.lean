module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCyclicSlice
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth

/-! Generate and retire the crop width from the retained precision master. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def preparedCyclicSlice : Pr P 224 Q A U :=
  .seq (generateWordWidth 119 94 4) (.seq generatedCyclicSlice (uclear 94))

def preparedCyclicSliceCost (q s a n : ℕ) : ℕ :=
  (8*q+9)+(generatedCyclicSliceCost s a n (2*q+8)+(2*(2*q+8)+2))

theorem preparedCyclicSlice_exec {s : ℕ} [NeZero s] (q a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (G : ZMod s → GaussianInt) (tail : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hq : (S.R 119).length = q)
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a))
    (hfresh : ∀ k ∈ ([(0 : Fin 224),1,2,3,4,5,6,7,94,138,141,143]), S.R k = [])
    (hsource : S.R 132 = cstream A (2*q+8) (chirpLine s G)++tail) :
    ∃ v' m, v'.user = v.user ∧ m ≤ preparedCyclicSliceCost q s a n ∧
      Exec body preparedCyclicSlice (mk v S) m
        (mk v' {S with R := Function.update S.R 147 (cstream A (2*q+8) (cyclicInterval a n G)++S.R 147)}) := by
  obtain ⟨v₁,hv₁,he₁⟩ := generateWordWidth_exec (body := body)
    (precision := 119) (width := 94) (tmp := 4) (by decide) q v S hq
    (hfresh 94 (by simp)) (hfresh 4 (by simp))
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 94 (List.replicate (2*q+8) tick)}
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := generatedCyclicSlice_exec (body := body) a n (2*q+8) ha hn G tail v₁ S₁
    (by simpa [S₁] using haSrc) (by simpa [S₁] using hleftEnd) (by simpa [S₁] using hrightEnd)
    (by simp [S₁]) (by
      intro k hk
      have hne : k ≠ 94 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hc : S.R k = [] := hfresh k (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
      simpa only [S₁,Function.update_of_ne hne] using hc)
    (by simpa [S₁] using hsource)
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 147 (cstream A (2*q+8) (cyclicInterval a n G)++S₁.R 147)}
  obtain ⟨v₃,hv₃,he₃⟩ := uclear_exec body 94 v₂ S₂
  refine ⟨v₃,(8*q+9)+(m₂+(2*(2*q+8)+2)),hv₃.trans (hv₂.trans hv₁),
    Nat.add_le_add_left (Nat.add_le_add_right hm₂ _) _,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by simp [S₂,S₁]) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h94 : k = 94 <;> by_cases h147 : k = 147 <;>
    simp [S₂,S₁,h94,h147,hfresh 94 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
