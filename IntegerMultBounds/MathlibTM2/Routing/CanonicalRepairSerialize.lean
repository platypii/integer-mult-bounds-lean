module

public import IntegerMultBounds.MathlibTM2.Routing.RepairOperandFrame

/-! Generate and serialize all inner repair operands from binary inputs.
The output suffix and every source word survive the copy phase. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def canonicalRepairGeneratePrice (L Lb n r : ℕ) :=
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
  let W := (canonicalStageWidths p).coordinateBits
  canonicalClassifierGeneratePrice L W p + 10*W+13 +
    (4*W*(p.wc+p.wy)+22*W+8*(p.wc+p.wy)+24) +
    (L*(4*n+11)+8*n+13) + (18*L+39) + (10*Lb+12) + (44*(L+Lb)+99)

def canonicalRepairOperandWidth (n B : ℕ) :=
  n + canonicalScalarWidth (n+B+1) + (n+1) + canonicalScalarWidth B + canonicalScalarWidth (n+1)

def canonicalRepairSerializeProgram (rg : Fin 130 → Fin T) (dst : Fin T)
    (delimiter : Fin (A+4)) : Pr P T Q A U :=
  .seq (canonicalRepairBlockGenerateProgram rg) (repairOperandCopy rg dst delimiter)

theorem canonicalRepairSerialize_exec (body : P → Pr P T Q A U)
    (rg : Fin 130 → Fin T) (hrg : Function.Injective rg) (dst : Fin T)
    (hoff : ∀ i, rg i ≠ dst) (delimiter : Fin (A+4)) (L Lb n B : ℕ)
    (hn : n < 2^L) (hB : B < 2^Lb) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3*canonicalRouterGap n < 2^L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hpayload : S.R (rg 120) = binSyms Lb B)
    (hblank : ∀ i : Fin 130, i ≠ 0 → i ≠ 9 → i ≠ 18 → i ≠ 120 → S.R (rg i) = []) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let words := canonicalRepairPayload (A := A) p 0 (canonicalScalarWidth 1)
      (canonicalScalarWidth (n+B+1)) (n+1) (canonicalScalarWidth B) (canonicalScalarWidth (n+1)) 1 B
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ canonicalRepairGeneratePrice L Lb n r.val +
        (repairSetupKeys.length * (6*canonicalRepairOperandWidth n B+7)+1) ∧
      Exec body (canonicalRepairSerializeProgram rg dst delimiter) (mk v S) m
        (mk v' { S with R := (Function.update (canonicalRepairBlockGeneratedBank S.R rg L n r.val B)
          dst (repairOperandFrame delimiter rg words ++ S.R dst)) }) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let words := canonicalRepairPayload (A := A) p 0 (canonicalScalarWidth 1)
    (canonicalScalarWidth (n+B+1)) (n+1) (canonicalScalarWidth B) (canonicalScalarWidth (n+1)) 1 B
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalRepairBlockGenerate_exec body rg hrg L Lb n B hn hB hlarge
    hdivisor r v S hdimension hresidue hpayload hblank
  let C : Stacks T A := { S with R := canonicalRepairBlockGeneratedBank S.R rg L n r.val B }
  have hwords (key : RepairSetupKey) : (words key).length ≤ canonicalRepairOperandWidth n B := by
    have he := canonicalRepairPayload_length_le (A := A) p 0 (canonicalScalarWidth 1)
      (canonicalScalarWidth (n+B+1)) (n+1) (canonicalScalarWidth B) (canonicalScalarWidth (n+1)) 1 B key
    rw [canonicalRepair_fieldsLen n hlarge r] at he
    exact he
  have bank := canonicalRepairBlockGeneratedBank_operands S.R rg hrg L n B hlarge r
    (hblank 128 (by decide) (by decide) (by decide) (by decide))
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := repairOperandCopy_exec body rg hrg dst hoff delimiter words
    (canonicalRepairOperandWidth n B) hwords v₁ C (fun key => congrFun bank key)
    (canonicalRepairBlockGeneratedBank_scratch S.R rg hrg L n r.val B hblank 0)
    (canonicalRepairBlockGeneratedBank_scratch S.R rg hrg L n r.val B hblank 1)
  have offHeader : ∀ i, (rg ∘ canonicalRepairBlockHeader) i ≠ dst := fun i => hoff _
  have outside : C.R dst = S.R dst := by
    change canonicalRepairBlockGeneratedBank S.R rg L n r.val B dst = S.R dst
    have he := canonicalHeaderScalarGeneratedBank_outside S.R (rg ∘ canonicalRepairBlockHeader)
      L n r.val dst offHeader
    simpa [canonicalRepairBlockGeneratedBank,canonicalRepairKeyGeneratedBank,canonicalRepairCountGeneratedBank,
      canonicalRepairZeroGeneratedBank,repairZeroBank,canonicalRepairBlockCore,canonicalRepairKeyCore,
      canonicalRepairCountCore,canonicalRepairZeroCore,canonicalRepairZeroSlot,canonicalRepairBlockHeader,
      Function.comp_def,(hoff 121).symm,(hoff 122).symm,(hoff 124).symm,(hoff 125).symm,
      (hoff 126).symm,(hoff 127).symm] using he
  rw [outside] at he₂
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  exact Nat.add_le_add hm₁ hm₂

end
end IntegerMultBounds.MathlibTM2.Routing
