module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseRuntimePages
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRuntimeRegisters

/-! Complete post-publication cleanup. Only the published result and the original
borrowed RHS/payload survive; every owned control and work stack is released. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def releaseCellRuntime : Pr P₀ 117 Q A U :=
  .seq releaseRuntimePages (clearWords [100, 101, 102, 103, 108])

def releaseCellRuntimeCost (L q l : ℕ) : ℕ :=
  releaseRuntimePagesCost L q + 2 * (q + l + 2 * L + 2) + 11

def releasedCellBank {A : ℕ} (rhs borrowed result : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A where
  inp := inp
  out := out
  L := fun _ => []
  R := fun k => if k.val = 93 then result else if k.val = 110 then rhs ++ borrowed else []

theorem releaseCellRuntime_exec (P s t u band L q l W M : ℕ)
    (outs factors rhs borrowed outTail result : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) (v : HS 117 Q A U)
    (houts : outs.length = L * (2 * q + 8)) (hfactors : factors.length = L * (2 * q + 8))
    (hrhs : rhs.length = L * (2 * q + 8)) :
    let B := cellRuntimeBank P s t u band L q l W M outs factors rhs borrowed outTail inp out
    ∃ v' m, v'.user = v.user ∧ m ≤ releaseCellRuntimeCost L q l ∧
      Exec body releaseCellRuntime (mk v { B with R := Function.update B.R 93 result }) m
        (mk v' (releasedCellBank rhs borrowed result inp out)) := by
  let B := cellRuntimeBank P s t u band L q l W M outs factors rhs borrowed outTail inp out
  let S : Stacks 117 A := { B with R := Function.update B.R 93 result }
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := releaseRuntimePages_exec (body := body) L q
    (generatorPage A P s t u band L q (M + 1)) outs rhs factors borrowed v S
    (by simp [S, B, cellRuntimeBank_R, cellRuntimeRegisters])
    (by simp [S, B, cellRuntimeBank_R, cellRuntimeRegisters])
    (by simp [S, B, cellRuntimeBank_R, cellRuntimeRegisters])
    (generatorPage_length _ _ _ _ _ _ _ _ _) houts hrhs hfactors
    (by simp [S, B, cellRuntimeBank_R, cellRuntimeRegisters, List.append_assoc]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [S, B, cellRuntimeBank_R, cellRuntimeRegisters])
  let S₁ : Stacks 117 A := { S with R := (Function.update (Function.update S.R 94 []) 110 (rhs ++ borrowed)) }
  obtain ⟨v₂, hu₂, he₂⟩ := clearWords_exec (body := body) [100, 101, 102, 103, 108] (by decide) v₁ S₁
  have hsum : ([(100 : Fin 117), 101, 102, 103, 108].map (fun k => (S₁.R k).length)).sum =
      q + l + 2 * L + 2 := by
    simp [S₁, S, B, cellRuntimeBank_R, cellRuntimeRegisters]
    omega
  refine ⟨v₂, m₁ + (2 * (q + l + 2 * L + 2) + 11), hu₂.trans hu₁,
    by unfold releaseCellRuntimeCost; omega, (Exec.seq he₁ he₂).cast (by rw [hsum]; rfl) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases h93 : k.val = 93
    · have he : k = 93 := Fin.ext h93
      subst k
      simp [S₁, S, releasedCellBank]
    by_cases h110 : k.val = 110
    · have he : k = 110 := Fin.ext h110
      subst k
      simp [S₁, releasedCellBank]
    simp [S₁, S, B, cellRuntimeBank_R, cellRuntimeRegisters,
      releasedCellBank, Function.update_apply, Fin.ext_iff, h93, h110]
    intro h100 h101 h102 h103 h108 h94
    simp [h100, h101, h102, h103, h108, h94]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
