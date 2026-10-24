module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalGapGenerate

/-! Generate the canonical gap and its reservoir-compatible stride from binary
 dimension, sharing scratch and preserving the gap output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def canonicalStrideGapSlot : Fin 9 → Fin 10 := Fin.castSucc
theorem canonicalStrideGapSlot_injective : Function.Injective canonicalStrideGapSlot := by decide +kernel

def canonicalStrideGenerateProgram (rg : Fin 10 → Fin T) : Pr P T Q A U :=
  .seq (canonicalGapGenerateProgram (rg ∘ canonicalStrideGapSlot))
    (.seq (bcopy (rg 4) (rg 9) (rg 5) (rg 6))
      (binaryShiftBitsProgram (rg 9) (rg 5) [false,false,false,false,false,false]))

theorem canonicalStrideGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2 ^ L) (hfit : canonicalRouterStride n < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R (rg 0) = binSyms L n)
    (hblank : ∀ j : Fin 10, j ≠ 0 → j ≠ 8 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 4 * L * L + 108 * L + 170 ∧
      Exec body (canonicalStrideGenerateProgram rg) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update S.R (rg 4)
          (binSyms L (canonicalRouterGap n))) (rg 9) (binSyms L (canonicalRouterStride n))) }) := by
  have hgapFit : canonicalRouterGap n < 2 ^ L := by
    unfold canonicalRouterStride at hfit
    omega
  have hsmallBlank : ∀ j : Fin 9, j ≠ 0 → j ≠ 8 → S.R ((rg ∘ canonicalStrideGapSlot) j) = [] := by
    intro j hj0 hj8
    apply hblank
    · exact fun he => hj0 (Fin.ext (congrArg (fun a : Fin 10 => a.val) he))
    · exact fun he => hj8 (Fin.ext (congrArg (fun a : Fin 10 => a.val) he))
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := canonicalGapGenerate_exec body (rg ∘ canonicalStrideGapSlot)
    (hrg.comp canonicalStrideGapSlot_injective) L n hn hgapFit v S hsrc hsmallBlank
  let C : Stacks T A := { S with R := Function.update S.R (rg 4) (binSyms L (canonicalRouterGap n)) }
  obtain ⟨v₂, hu₂, he₂⟩ := bcopy_exec (body := body) (a := rg 4) (c := rg 9) (t₁ := rg 5) (t₂ := rg 6)
    (by simp [List.nodup_cons, hrg.eq_iff]) v₁ C
    (by simp [C, hrg.eq_iff, hblank 5 (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 6 (by decide) (by decide)])
  have hc4 : C.R (rg 4) = binSyms L (canonicalRouterGap n) := by simp [C]
  have hc9 : C.R (rg 9) = [] := by simp [C, hrg.eq_iff, hblank 9 (by decide) (by decide)]
  rw [hc4, hc9, List.append_nil, length_binSyms] at he₂
  let D : Stacks T A := { C with R := Function.update C.R (rg 9) (binSyms L (canonicalRouterGap n)) }
  obtain ⟨v₃, hu₃, he₃⟩ := binaryShiftBits_exec body (rg 9) (rg 5) (hrg.ne (by decide))
    [false,false,false,false,false,false] L (canonicalRouterGap n) v₂ D (by simp [D])
    (by simp [D, C, hrg.eq_iff, hblank 5 (by decide) (by decide)])
  have hscale : binaryShiftBitsValue (canonicalRouterGap n) [false,false,false,false,false,false] =
      canonicalRouterStride n := by
    simp [binaryShiftBitsValue, canonicalRouterStride]
    omega
  rw [hscale] at he₃
  refine ⟨v₃, m₁ + ((6 * L + 6) + (6 * (4 * L + 8) + 1)), hu₃.trans (hu₂.trans hu₁), ?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · omega
  · simp [D, C]

end IntegerMultBounds.MathlibTM2.Routing
