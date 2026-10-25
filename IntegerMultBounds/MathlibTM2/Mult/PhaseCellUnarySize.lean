module

public import IntegerMultBounds.MathlibTM2.Fast.LoadRing
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! # Generate a unary bit length while retaining the original header

Reuse the existing gamma writer's halving loop and discard its binary output.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.Spec.SignedRingProduct

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def unarySize (src dst a h par bits saved : Fin T) : Pr P T Q A U :=
  .seq (ucopy src a saved) (.seq (ldrLoop a h par bits dst) (uclear bits))

/-- Only the output gains the bit-length ticks; arbitrary input symbols and the
output's suffix are retained. All five work registers return empty. -/
theorem unarySize_exec {src dst a h par bits saved : Fin T}
    (hreg : [src, dst, a, h, par, bits, saved].Nodup)
    (n : ℕ) (v : HS T Q A U) (S : Stacks T A) (hn : (S.R src).length = n)
    (hfresh : ∀ k ∈ [a, h, par, bits, saved], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 19 * n + 8 ∧
      Exec body (unarySize src dst a h par bits saved) (mk v S) m
        (mk v' { S with R := Function.update S.R dst (List.replicate (Nat.size n) tick ++ S.R dst) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec (body := body) ‹src ≠ a› ‹src ≠ saved› ‹a ≠ saved› v S
    (hfresh saved (by simp))
  let S₁ : Stacks T A := { S with R := Function.update S.R a (List.replicate n tick) }
  have he₁' : Exec body (ucopy src a saved) (mk v S) (4 * n + 4) (mk v₁ S₁) := by
    simpa [S₁, hn, hfresh a (by simp)] using he₁
  have hp := Exec.act (body := body) (peekR a) (mk v₁ S₁)
  rw [peekR_run] at hp
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := ldr_loop_aux (body := body)
    (show [a, h, par, bits, dst].Nodup by simp_all [ne_comm]) n
    { v₁ with flag := (S₁.R a).head?.isSome } S₁ (by simp [S₁])
    (by simpa [S₁, ‹a ≠ h›.symm] using hfresh h (by simp))
    (by simpa [S₁, ‹a ≠ par›.symm] using hfresh par (by simp)) rfl
  let S₂ : Stacks T A := { S₁ with R := ldrLoopR a bits dst S₁.R n }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body bits v₂ S₂
  have hlen : (S₂.R bits).length = Nat.size n := by
    simp [S₂, S₁, ldrLoopR, ‹dst ≠ bits›.symm, ‹a ≠ bits›.symm,
      hfresh bits (by simp), msbBits]
  refine ⟨v₃, (4 * n + 4) + ((1 + m₂) + (2 * Nat.size n + 2)), hu₃.trans (hu₂.trans hu₁),
    by have hs := ldr_size_le n; omega,
    (Exec.seq he₁' (Exec.seq (Exec.seq hp he₂) he₃)).cast (by rw [hlen]) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases hb : k = bits
  · subst k; simp [hfresh bits (by simp), ‹dst ≠ bits›.symm]
  by_cases ha : k = a
  · subst k; simp [S₂, S₁, ldrLoopR, ‹dst ≠ a›.symm, ‹a ≠ bits›, hfresh a (by simp)]
  by_cases hd : k = dst
  · subst k; simp [S₂, S₁, ldrLoopR, ‹dst ≠ a›, ‹dst ≠ bits›]
  simp [S₂, S₁, ldrLoopR, hb, ha, hd, Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
