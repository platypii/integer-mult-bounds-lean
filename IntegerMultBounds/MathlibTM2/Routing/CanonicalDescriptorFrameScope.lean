module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorSerialize
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorClean

/-! Produce a complete canonical descriptor frame from compact inputs and
restore every setup tape. The output stream is the only changed register. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def canonicalDescriptorFrameScopeProgram (rg : Fin 108 → Fin T) (dst : Fin T)
    (delimiter : Fin (A + 4)) : Pr P T Q A U :=
  .seq (canonicalDescriptorSerializeProgram rg dst delimiter) (canonicalDescriptorCleanProgram rg)

theorem canonicalDescriptorFrameScope_exec (body : P → Pr P T Q A U)
    (rg : Fin 108 → Fin T) (hrg : Function.Injective rg) (dst : Fin T)
    (hoff : ∀ i, rg i ≠ dst) (delimiter : Fin (A + 4)) (L n : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (r : Fin (canonicalRouterStride n)) (hG : 0 < canonicalRouterGap n) (hK : 0 < canonicalRouterStride n)
    (active : Fin (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val).n → Bool)
    (source : Fin (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val).n →
      SlotSource (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val) 0)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hblank : ∀ i : Fin 108, i ≠ 0 → i ≠ 9 → i ≠ 18 → S.R (rg i) = []) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let W := (canonicalStageWidths p).coordinateBits
    let words := canonicalDescriptorOperands p 0 hG hK active source (canonicalStageWidths p)
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ canonicalDescriptorSerializePrice L W + 24 * L + 146 * W + 173 ∧
      Exec body (canonicalDescriptorFrameScopeProgram rg dst delimiter) (mk v S) m
        (mk v' { S with R := (Function.update S.R dst
          (descriptorOperandFrame delimiter rg words ++ S.R dst)) }) := by
  dsimp only
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalDescriptorSerialize_exec body rg hrg dst hoff delimiter
    L n hn hlarge hdivisor r hG hK active source v S hdimension hresidue hblank
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := canonicalDescriptorClean_exec body rg hrg L n r.val v₁ S
    hblank dst hoff (descriptorOperandFrame delimiter rg
      (canonicalDescriptorOperands _ 0 hG hK active source (canonicalStageWidths _)) ++ S.R dst)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  nlinarith only [hm₁,hm₂]

end
end IntegerMultBounds.MathlibTM2.Routing
