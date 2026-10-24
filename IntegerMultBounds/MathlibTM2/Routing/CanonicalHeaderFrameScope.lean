module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalHeaderSerialize
public import IntegerMultBounds.MathlibTM2.Routing.HeaderScalarRestore
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalClassifierClean

/-! Produce the complete one-row header operand frame and restore every
header, classifier, descriptor and geometry setup tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def canonicalHeaderFrameScopeProgram (rg : Fin 120 → Fin T) (dst : Fin T)
    (delimiter : Fin (A + 4)) : Pr P T Q A U :=
  .seq (canonicalHeaderSerializeProgram rg dst delimiter)
    (.seq (metadataClean [rg 118,rg 119]) (canonicalClassifierCleanProgram (rg ∘ canonicalHeaderScalarCore)))

theorem canonicalHeaderFrameScope_exec (body : P → Pr P T Q A U)
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
        (Fintype.card HeaderWorkRole * (6 * W + 7) + 1) + (2 * W + 7) + (44 * L + 166 * W + 195) ∧
      Exec body (canonicalHeaderFrameScopeProgram rg dst delimiter) (mk v S) m
        (mk v' { S with R := (Function.update S.R dst
          (headerOperandFrame delimiter rg words ++ S.R dst)) }) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let W := (canonicalStageWidths p).coordinateBits
  let core := rg ∘ canonicalHeaderScalarCore
  have hc : Function.Injective core := hrg.comp canonicalHeaderScalarCore_injective
  let B : Stacks T A := { S with R := canonicalClassifierGeneratedBank S.R core L n r.val }
  let output := headerOperandFrame delimiter rg
    (canonicalHeaderOperands (A := A) (canonicalScalarWidth 1) (canonicalScalarWidth p.wc) 1 p.wc) ++ S.R dst
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalHeaderSerialize_exec body rg hrg dst hoff delimiter L n hn hlarge
    hdivisor r v S hdimension hresidue hblank
  have newBlank (i : Fin 120) (hi : 118 ≤ i.val) : B.R (rg i) = [] := by
    have off (j : Fin 118) : core j ≠ rg i := by
      intro he
      have hv := congrArg (fun x : Fin 120 => x.val) (hrg he)
      change j.val = i.val at hv
      have := j.isLt
      omega
    rw [show B.R (rg i) = S.R (rg i) from
      (classifierGeneratedBank_outside _ core L W p _ off).trans
        (canonicalDescriptorGeneratedBank_outside S.R (core ∘ canonicalClassifierCore) L n r.val _ (fun j => off _))]
    apply hblank <;> intro he <;> subst i <;> norm_num at hi
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := headerScalarRestore_exec body (rg ∘ canonicalHeaderScalarSlot)
    (hrg.comp canonicalHeaderScalarSlot_injective) W p.wc (repairDescriptorScalarPalette_fit p r.isLt 6)
    v₁ B (newBlank 118 (by decide)) (newBlank 119 (by decide)) dst
    ⟨(hoff 118).symm,(hoff 119).symm⟩ output
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := canonicalClassifierClean_exec body core hc L n hn r v₂ S (by
      intro i h0 h9 h18
      exact hblank _ (fun he => h0 (Fin.ext (congrArg (fun x : Fin 120 => x.val) he)))
        (fun he => h9 (Fin.ext (congrArg (fun x : Fin 120 => x.val) he)))
        (fun he => h18 (Fin.ext (congrArg (fun x : Fin 120 => x.val) he))))
    dst (fun i => hoff _) output
  refine ⟨v₃,m₁+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),?_,Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  nlinarith only [hm₁,hm₂,hm₃]

end
end IntegerMultBounds.MathlibTM2.Routing
