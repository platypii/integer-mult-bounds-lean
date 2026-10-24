module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRepairSerialize
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRepairClean

/-! Generate the entire repair operand frame, then restore all numeric,
header, classifier, descriptor and geometry workspace. Only output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def canonicalRepairFrameScopeProgram (rg : Fin 130 → Fin T) (dst : Fin T)
    (delimiter : Fin (A+4)) : Pr P T Q A U :=
  .seq (canonicalRepairSerializeProgram rg dst delimiter)
    (canonicalRepairCleanProgram rg)

theorem canonicalRepairFrameScope_exec (body : P → Pr P T Q A U)
    (rg : Fin 130 → Fin T) (hrg : Function.Injective rg) (dst : Fin T)
    (hoff : ∀ i, rg i ≠ dst) (delimiter : Fin (A+4)) (L Lb n B : ℕ)
    (hn : n < 2^L) (hB : B < 2^Lb) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3*canonicalRouterGap n < 2^L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hpayload : S.R (rg 120) = binSyms Lb B)
    (hblank : ∀ i : Fin 130, i ≠ 0 → i ≠ 9 → i ≠ 18 → i ≠ 120 → S.R (rg i) = []) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let W := (canonicalStageWidths p).coordinateBits
    let words := canonicalRepairPayload (A := A) p 0 (canonicalScalarWidth 1)
      (canonicalScalarWidth (n+B+1)) (n+1) (canonicalScalarWidth B) (canonicalScalarWidth (n+1)) 1 B
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ canonicalRepairGeneratePrice L Lb n r.val +
        (repairSetupKeys.length * (6*canonicalRepairOperandWidth n B+7)+1) +
        (2*(p.wc+p.wy+(n+1)+canonicalScalarWidth (n+1)+canonicalScalarWidth B+
          canonicalScalarWidth (n+B+1))+13) + (2*W+7) + (44*L+166*W+195) ∧
      Exec body (canonicalRepairFrameScopeProgram rg dst delimiter) (mk v S) m
        (mk v' { S with R := (Function.update S.R dst
          (repairOperandFrame delimiter rg words ++ S.R dst)) }) := by
  dsimp only
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalRepairSerialize_exec body rg hrg dst hoff delimiter L Lb n B hn hB
    hlarge hdivisor r v S hdimension hresidue hpayload hblank
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := canonicalRepairClean_exec body rg hrg L n B hn r v₁ S hblank dst hoff
    (repairOperandFrame delimiter rg (canonicalRepairPayload (A := A)
      (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)
      0 (canonicalScalarWidth 1) (canonicalScalarWidth (n+B+1)) (n+1)
      (canonicalScalarWidth B) (canonicalScalarWidth (n+1)) 1 B) ++ S.R dst)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  nlinarith only [hm₁,hm₂]

end
end IntegerMultBounds.MathlibTM2.Routing
