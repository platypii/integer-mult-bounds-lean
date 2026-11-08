module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicNormalizationControls
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Own the physical normalization rulers around any restoring packet operation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 280 Q A U}

def cyclicNormalizationPrepared (P₀ q n : ℕ) (S : Stacks 280 A) : Stacks 280 A :=
  {S with R := (Function.update (Function.update (Function.update S.R 249
    (List.replicate (cyclicNormalizationWidth P₀ q) tick)) 94 (List.replicate (2*q+8) tick)) 95
      (List.replicate n tick))}

def withCyclicNormalizationControls (core : Pr P 280 Q A U) : Pr P 280 Q A U :=
  .seq (generateCyclicNormalizationWidth 117 119 249 0 1 2 3 4)
    (.seq cyclicNormalizationControls (.seq core (clearWords [94,95,249])))

theorem withCyclicNormalizationControls_exec (core : Pr P 280 Q A U)
    (P₀ q a n s coreCost : ℕ) (output : List (Fin (A+4)))
    (v : HS 280 Q A U) (S : Stacks 280 A)
    (hP : (S.R 117).length = P₀) (hq : (S.R 119).length = q)
    (ha : (S.R 144).length = a) (hleft : (S.R 145).length = a+min n (s-a))
    (hright : (S.R 146).length = n-min n (s-a))
    (hfresh : ∀ k ∈ ([(0 : Fin 280),1,2,3,4,7,94,95,249]), S.R k = [])
    (hcore : ∀ v₀ : HS 280 Q A U, ∃ v' m, v'.user = v₀.user ∧ m ≤ coreCost ∧
      Exec body core (mk v₀ (cyclicNormalizationPrepared P₀ q n S)) m
        (mk v' {cyclicNormalizationPrepared P₀ q n S with R :=
          (Function.update (cyclicNormalizationPrepared P₀ q n S).R 147 output)})) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (19*P₀+19*q+17)+(8*q+4*(2*a+n)+21)+coreCost+
        (2*((2*q+8)+n+cyclicNormalizationWidth P₀ q)+7) ∧
      Exec body (withCyclicNormalizationControls core) (mk v S) m
        (mk v' {S with R := Function.update S.R 147 output}) := by
  let B := cyclicNormalizationWidth P₀ q
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := generateCyclicNormalizationWidth_exec (body := body)
    (kernel := 117) (precision := 119) (width := 249) (a := 0) (h := 1) (par := 2) (bits := 3) (saved := 4)
    (by decide) P₀ q v S hP hq (hfresh 249 (by simp))
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp))
  let S₁ : Stacks 280 A := {S with R := Function.update S.R 249 (List.replicate B tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := cyclicNormalizationControls_exec (body := body) q a (min n (s-a)) (n-min n (s-a))
    v₁ S₁ (by simpa [S₁] using hq) (by simpa [S₁] using ha)
    (by simpa [S₁] using hleft) (by simpa [S₁] using hright)
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl
        · simpa [S₁] using hfresh 4 (by simp)
        · simpa [S₁] using hfresh 7 (by simp)
        · simpa [S₁] using hfresh 94 (by simp)
        · simpa [S₁] using hfresh 95 (by simp))
  have hparts : min n (s-a)+(n-min n (s-a)) = n := Nat.add_sub_of_le (min_le_left ..)
  let S₂ := cyclicNormalizationPrepared P₀ q n S
  have he₂' : Exec body cyclicNormalizationControls (mk v₁ S₁) (8*q+4*(2*a+n)+21) (mk v₂ S₂) := by
    simpa only [S₂,cyclicNormalizationPrepared,S₁,hparts,Nat.add_assoc] using he₂
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := hcore v₂
  let S₃ : Stacks 280 A := {S₂ with R := Function.update S₂.R 147 output}
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) [94,95,249] (by decide) v₃ S₃
  refine ⟨v₄,m₁+((8*q+4*(2*a+n)+21)+(m₃+(2*((2*q+8)+n+B)+7))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),by dsimp only [B]; omega,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ he₄))).cast ?_ ?_⟩
  · simp [S₃,S₂,cyclicNormalizationPrepared,B,List.sum_cons,List.sum_nil]
    omega
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h94 : k = 94 <;> by_cases h95 : k = 95 <;> by_cases h249 : k = 249 <;>
      simp [S₃,S₂,cyclicNormalizationPrepared,Function.update_apply,h94,h95,h249,
        hfresh 94 (by simp),hfresh 95 (by simp),hfresh 249 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
