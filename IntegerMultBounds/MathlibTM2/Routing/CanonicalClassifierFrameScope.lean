module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalClassifierSerialize
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalClassifierClean

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
    (canonicalClassifierCleanProgram rg)

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
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalClassifierSerialize_exec body rg hrg dst hoff delimiter
    L n hn hlarge hdivisor r v S hdimension hresidue hblank
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := canonicalClassifierClean_exec body rg hrg L n hn r v₁ S hblank dst hoff
    (classifierOperandFrame delimiter rg (canonicalClassifierOperands p (canonicalScalarWidth p.K)
      (canonicalScalarWidth p.n) (canonicalScalarWidth (p.ρ+1)) (canonicalScalarWidth p.m)) ++ S.R dst)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  nlinarith only [hm₁,hm₂]

end
end IntegerMultBounds.MathlibTM2.Routing
