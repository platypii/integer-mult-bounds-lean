module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSetupFits
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! # Generate the common setup width from ordinary P/M/q headers -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateSetupWidth : Pr P₀ 117 Q A U :=
  .seq (unaryProduct 114 101 94 104 105)
    (.seq (umul 2 114 94 104)
      (.seq (uadd 112 94 104) (.act (pushN 94 (fun _ => tick) 5 .done))))

theorem generateSetupWidth_exec (P M q : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP : (S.R 114).length = P) (hM : (S.R 101).length = M) (hq : (S.R 112).length = q)
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 105], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 4 * (P * M) + 13 * P + 4 * q + 13 ∧
      Exec body generateSetupWidth (mk v S) m
        (mk v' { S with R := (Function.update S.R 94
          (List.replicate (integerSetupWidth P q (M + 1) 0) tick)) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [(114 : Fin 117), 101, 94, 104, 105].Nodup by decide) v S
    (hfresh 104 (by simp)) (hfresh 105 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 94 (List.replicate (P * M) tick) }
  have he₁' : Exec body (unaryProduct 114 101 94 104 105) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁, hP, hM, hfresh 94 (by simp)] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := umul_exec (body := body) 2 (a := 114) (b := 94) (t := 104)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hfresh 104 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 94 (List.replicate (P * (M + 2)) tick) }
  have he₂' : Exec body (umul 2 114 94 104) (mk v₁ S₁) (4 * P + 4) (mk v₂ S₂) := by
    have hlen : 2 * P + P * M = P * (M + 2) := by ring
    simpa [S₂, S₁, hP, List.replicate_append_replicate, hlen] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := uadd_exec (body := body) (a := 112) (b := 94) (t := 104)
    (by decide) (by decide) (by decide) v₂ S₂ (by simpa [S₂, S₁] using hfresh 104 (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 94 (List.replicate (q + P * (M + 2)) tick) }
  have he₃' : Exec body (uadd 112 94 104) (mk v₂ S₂) (4 * q + 4) (mk v₃ S₃) := by
    simpa [S₃, S₂, S₁, hq, List.replicate_append_replicate] using he₃
  have he₄ := Exec.act (body := body) (pushN 94 (fun _ => tick) 5 .done) (mk v₃ S₃)
  rw [pushN_run] at he₄
  rw [hP, hM] at hm₁
  refine ⟨v₃, m₁ + ((4 * P + 4) + ((4 * q + 4) + 1)), hu₃.trans (hu₂.trans hu₁), by nlinarith only [hm₁],
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄))).cast rfl ?_⟩
  have hlen : 5 + (q + P * (M + 2)) = integerSetupWidth P q (M + 1) 0 := by
    unfold integerSetupWidth; ring
  simp only [S₃, Function.update_self, List.replicate_append_replicate, hlen, Action.run]
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  simp [S₃, S₂, S₁, Function.update_apply]
  split_ifs <;> rfl

/-- One generated width meets iteration, encoding and reciprocal requirements.
The runtime precision range covers q=4b with n=2b+2. -/
theorem integerSetupWidth_generator {P M q : ℕ} (hP : 13 ≤ P) (hq : q ≤ 2 * (M + 1)) :
    let W := integerSetupWidth P q (M + 1) 0
    P * (M + 2) + 3 ≤ W ∧ q ≤ P * (M + 1) + 1 ∧
      P * (M + 1) + 1 - q + (2 * q + 8) ≤ W ∧
      q + P * (M + 1) < W ∧ 2 * q + 8 ≤ W := by
  have hqr : q ≤ P * (M + 1) + 1 := by nlinarith
  refine ⟨?_, hqr, integerSetupWidth_slice (by omega) hqr, ?_, ?_⟩
  all_goals unfold integerSetupWidth; nlinarith

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
