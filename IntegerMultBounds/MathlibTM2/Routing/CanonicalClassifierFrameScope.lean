module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalClassifierSerialize
public import IntegerMultBounds.MathlibTM2.Routing.ClassifierOperandClean
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorClean

/-! Generate and serialize the complete classifier frame, then restore all
classifier, width, descriptor and geometry setup tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def canonicalClassifierFrameScopeProgram (rg : Fin 118 → Fin T) (dst : Fin T)
    (delimiter : Fin (A + 4)) : Pr P T Q A U :=
  .seq (canonicalClassifierSerializeProgram rg dst delimiter)
    (.seq (classifierOperandCleanProgram rg) (canonicalDescriptorCleanProgram (rg ∘ canonicalClassifierCore)))

theorem canonicalClassifierFrameScope_exec (body : P → Pr P T Q A U)
    (rg : Fin 118 → Fin T) (hrg : Function.Injective rg) (dst : Fin T)
    (hoff : ∀ i, rg i ≠ dst) (delimiter : Fin (A + 4)) (L n : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hblank : ∀ i : Fin 118, i ≠ 0 → i ≠ 9 → i ≠ 18 → S.R (rg i) = []) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let W := (canonicalStageWidths p).coordinateBits
    let words := canonicalClassifierOperands p (canonicalScalarWidth p.K) (canonicalScalarWidth p.n)
      (canonicalScalarWidth (p.ρ+1)) (canonicalScalarWidth p.m)
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ canonicalClassifierGeneratePrice L W p + 16 * (6 * (L+W) + 7) + 1 +
        (20 * (L+W) + 22) + (24 * L + 146 * W + 173) ∧
      Exec body (canonicalClassifierFrameScopeProgram rg dst delimiter) (mk v S) m
        (mk v' { S with R := (Function.update S.R dst
          (classifierOperandFrame delimiter rg words ++ S.R dst)) }) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let W := (canonicalStageWidths p).coordinateBits
  let core := rg ∘ canonicalClassifierCore
  have hc : Function.Injective core := hrg.comp canonicalClassifierCore_injective
  let B : Stacks T A := { S with R := canonicalDescriptorGeneratedBank S.R core L n r.val }
  let words := canonicalClassifierOperands (A := A) p (canonicalScalarWidth p.K) (canonicalScalarWidth p.n)
    (canonicalScalarWidth (p.ρ+1)) (canonicalScalarWidth p.m)
  let output := classifierOperandFrame delimiter rg words ++ S.R dst
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalClassifierSerialize_exec body rg hrg dst hoff delimiter
    L n hn hlarge hdivisor r v S hdimension hresidue hblank
  have baseBlank (i : Fin 118) (hi : 108 ≤ i.val) : B.R (rg i) = [] := by
    rw [show B.R (rg i) = S.R (rg i) from canonicalDescriptorGeneratedBank_outside S.R core L n r.val _ (by
      intro j he
      have hv := congrArg (fun x : Fin 118 => x.val) (hrg he)
      change j.val = i.val at hv
      have := j.isLt
      omega)]
    apply hblank <;> intro he <;> subst i <;> norm_num at hi
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := classifierOperandClean_exec body rg hrg L W p
    (canonicalClassifier_raw_fit L n hn r) v₁ B baseBlank dst hoff output
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := canonicalDescriptorClean_exec body core hc L n r.val v₂ S (by
      intro i h0 h9 h18
      exact hblank _ (fun he => h0 (Fin.ext (congrArg (fun x : Fin 118 => x.val) he)))
        (fun he => h9 (Fin.ext (congrArg (fun x : Fin 118 => x.val) he)))
        (fun he => h18 (Fin.ext (congrArg (fun x : Fin 118 => x.val) he))))
    dst (fun i => hoff _) output
  refine ⟨v₃,m₁+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),?_,Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  nlinarith only [hm₁,hm₂,hm₃]

end
end IntegerMultBounds.MathlibTM2.Routing
