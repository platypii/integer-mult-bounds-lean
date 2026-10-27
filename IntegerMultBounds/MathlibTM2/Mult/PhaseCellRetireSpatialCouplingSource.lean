module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCountedLine

/-! Retire exactly the owned padded source and restore its borrowed suffix and controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 144 Q A U}

def retireSpatialCouplingSource : Pr P 144 Q A U :=
  .seq (ucopy 97 116 105)
    (.seq (umul 2 100 116 105)
      (.seq (retireCountedLine 116 94 141 108 104 105) (uclear 116)))

def retireSpatialCouplingSourceCost (s band w : ℕ) : ℕ :=
  retireCountedLineCost (s+2*band) w+6*s+8*band+10

theorem retireSpatialCouplingSource_exec (s band w : ℕ)
    (words tail : List (Fin (A+4))) (hlen : words.length = (s+2*band)*w)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hs : (S.R 97).length = s) (hb : (S.R 100).length = band) (hw : (S.R 94).length = w)
    (hsrc : S.R 141 = words++tail) (h116 : S.R 116 = [])
    (h108 : S.R 108 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retireSpatialCouplingSourceCost s band w ∧
      Exec body retireSpatialCouplingSource (mk v S) m
        (mk v' {S with R := Function.update S.R 141 tail}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body (show (97 : Fin 144) ≠ 116 by decide)
    (show (97 : Fin 144) ≠ 105 by decide) (show (116 : Fin 144) ≠ 105 by decide) v S h105
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 116 (List.replicate s tick)}
  have he₁' : Exec body (ucopy 97 116 105) (mk v S) (4*s+4) (mk v₁ S₁) := by
    simpa [S₁,hs,h116] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := umul_exec (body := body) 2 (a := 100) (b := 116) (t := 105)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using h105)
  let S₂ : Stacks 144 A := {S₁ with R := Function.update S₁.R 116 (List.replicate (s+2*band) tick)}
  have hrep : List.replicate (2*band) (tick : Fin (A+4))++List.replicate s tick =
      List.replicate (s+2*band) tick := by
    rw [← List.replicate_add]
    congr 1
    omega
  have he₂' : Exec body (umul 2 100 116 105) (mk v₁ S₁) (4*band+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hb,hrep,← Nat.mul_assoc] using he₂
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := retireCountedLine_exec (body := body)
    116 94 141 108 104 105 (by decide) (s+2*band) w words tail hlen v₂ S₂
    (by simp [S₂]) (by simpa [S₂,S₁] using hw) (by simpa [S₂,S₁] using hsrc)
    (by simpa [S₂,S₁] using h108) (by simpa [S₂,S₁] using h104) (by simpa [S₂,S₁] using h105)
  let S₃ : Stacks 144 A := {S₂ with R := Function.update S₂.R 141 tail}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) 116 v₃ S₃
  refine ⟨v₄,(4*s+4)+((4*band+4)+(m₃+(2*(s+2*band)+2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),by dsimp only [retireSpatialCouplingSourceCost]; omega,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄))).cast (by simp [S₃,S₂]) ?_⟩
  apply congrArg (mk v₄)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h116' : k = 116 <;> by_cases h141 : k = 141 <;>
    simp [S₃,S₂,S₁,h116',h141,h116]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
