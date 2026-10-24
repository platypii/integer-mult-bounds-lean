module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalHeaderOperandReady

/-! Serialize the entire inner header-work bank from binary dimension/residue.
All earlier metadata remains available, and arbitrary output suffix is retained. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def canonicalHeaderSerializeProgram (rg : Fin 120 → Fin T) (dst : Fin T)
    (delimiter : Fin (A + 4)) : Pr P T Q A U :=
  .seq (canonicalHeaderScalarGenerateProgram rg) (headerOperandCopy rg dst delimiter)

theorem canonicalHeaderSerialize_exec (body : P → Pr P T Q A U)
    (rg : Fin 120 → Fin T) (hrg : Function.Injective rg) (dst : Fin T)
    (hoff : ∀ i, rg i ≠ dst) (delimiter : Fin (A + 4)) (L n : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hblank : ∀ i : Fin 120, i ≠ 0 → i ≠ 9 → i ≠ 18 → S.R (rg i) = []) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let W := (canonicalStageWidths p).coordinateBits
    let words := canonicalHeaderOperands (canonicalScalarWidth 1) (canonicalScalarWidth p.wc) 1 p.wc
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ canonicalClassifierGeneratePrice L W p + 10 * W + 13 +
        (Fintype.card HeaderWorkRole * (6 * W + 7) + 1) ∧
      Exec body (canonicalHeaderSerializeProgram rg dst delimiter) (mk v S) m
        (mk v' { S with R := (Function.update (canonicalHeaderScalarGeneratedBank S.R rg L n r.val)
          dst (headerOperandFrame delimiter rg words ++ S.R dst)) }) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let W := (canonicalStageWidths p).coordinateBits
  let words := canonicalHeaderOperands (A := A) (canonicalScalarWidth 1) (canonicalScalarWidth p.wc) 1 p.wc
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalHeaderScalarGenerate_exec body rg hrg L n hn hlarge hdivisor
    r v S hdimension hresidue hblank
  let C : Stacks T A := { S with R := canonicalHeaderScalarGeneratedBank S.R rg L n r.val }
  have hpos : 1 ≤ W := by
    change 1 ≤ (liveDescriptorArithmeticWidths p 0 repairLiveMode).indexBits + 1 +
      (liveDescriptorArithmeticWidths p 0 repairLiveMode).strideBits
    omega
  have hwc : canonicalScalarWidth p.wc ≤ W := Nat.clog_le_of_le_pow
    (Nat.succ_le_of_lt (repairDescriptorScalarPalette_fit p r.isLt 6))
  have wordBound (role : HeaderWorkRole) : (words role).length ≤ W := by
    cases role with
    | binary i =>
      fin_cases i
      · change 1 ≤ W
        exact hpos
      · simpa [words,canonicalHeaderOperands] using hwc
    | _ => simp [words,canonicalHeaderOperands]
  have hb := canonicalHeaderScalarGeneratedBank_operands S.R rg hrg L n r.val hblank
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := headerOperandCopy_exec body rg hrg dst hoff delimiter words W wordBound
    v₁ C (by intro role; exact congrFun hb role)
    (canonicalHeaderScalarGeneratedBank_scratch S.R rg hrg L n r.val hblank 0)
    (canonicalHeaderScalarGeneratedBank_scratch S.R rg hrg L n r.val hblank 1)
  have hk : C.R dst = S.R dst := canonicalHeaderScalarGeneratedBank_outside S.R rg L n r.val dst hoff
  rw [hk] at he₂
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  nlinarith only [hm₁,hm₂]

end
end IntegerMultBounds.MathlibTM2.Routing
