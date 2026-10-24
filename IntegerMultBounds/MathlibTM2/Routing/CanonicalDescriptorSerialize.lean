module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorOperandFrame

/-! Generate and serialize the complete canonical descriptor operand bank.
The fixed code starts from binary dimension/residue and blank workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def canonicalDescriptorSerializeProgram (rg : Fin 108 → Fin T) (dst : Fin T)
    (delimiter : Fin (A + 4)) : Pr P T Q A U :=
  .seq (canonicalDescriptorGenerateProgram rg) (descriptorOperandCopy rg dst delimiter)

def canonicalDescriptorSerializePrice (L W : ℕ) : ℕ :=
  96 * L * L + 652 * L + 875 + 10 * L * (4 * W + 11) + 224 * W +
    (8 * W + 9) + 6 * (2 * L * (4 * W + 11) + 12 * (L + W) + 26 * W + 42) + 1 +
    (55 * (2 * L * (4 * W + 11) + 38 * W + 42) + 1) +
    (Fintype.card (LiveDescriptorRole 11) * (36 * W + 7) + 1)

theorem canonicalDescriptorSerialize_exec (body : P → Pr P T Q A U)
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
      m ≤ canonicalDescriptorSerializePrice L W ∧
      Exec body (canonicalDescriptorSerializeProgram rg dst delimiter) (mk v S) m
        (mk v' { S with R := (Function.update (canonicalDescriptorGeneratedBank S.R rg L n r.val)
          dst (descriptorOperandFrame delimiter rg words ++ S.R dst)) }) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let w := canonicalStageWidths p
  let W := w.coordinateBits
  let words := canonicalDescriptorOperands (A := A) p 0 hG hK active source w
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalDescriptorGenerate_exec body rg hrg L n hn hlarge
    hdivisor r v S hdimension hresidue hblank
  let C : Stacks T A := { S with R := canonicalDescriptorGeneratedBank S.R rg L n r.val }
  have blank : ∀ i : Fin 108, 39 ≤ i.val → S.R (rg i) = [] := by
    intro i hi
    apply hblank <;> intro he <;> subst i <;> norm_num at hi
  have hw (role : LiveDescriptorRole 11) : (words role).length ≤ 6 * W := by
    have hlen := canonicalDescriptorOperands_length_le (A := A) p 0 hG hK active source w role
    have hwidth := canonicalDescriptorShared_width_le p 0
    have hgroup := canonicalDescriptorShared_width_le p 1
    have hindex := canonicalDescriptorShared_width_le p 2
    have hselector := canonicalDescriptorShared_width_le p 3
    have hstride := canonicalDescriptorInstall_width_le p 0
    change w.widthBits ≤ W at hwidth
    change w.groupBits ≤ W at hgroup
    change w.indexBits ≤ W at hindex
    change w.selectorBits ≤ W at hselector
    change w.strideBits ≤ W at hstride
    nlinarith only [hlen,hwidth,hgroup,hindex,hselector,hstride]
  have hbank := canonicalDescriptorGeneratedBank_operands S.R rg hrg L n r.val blank hG hK active source
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := descriptorOperandCopy_exec body rg hrg dst hoff delimiter words
    (6 * W) hw v₁ C (by intro role; exact congrFun hbank role)
    (canonicalDescriptorGeneratedBank_scratch S.R rg hrg L n r.val blank 40
      (by decide) (by decide) (by decide))
    (canonicalDescriptorGeneratedBank_scratch S.R rg hrg L n r.val blank 41
      (by decide) (by decide) (by decide))
  have hk : C.R dst = S.R dst := canonicalDescriptorGeneratedBank_outside S.R rg L n r.val dst hoff
  rw [hk] at he₂
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  dsimp only [canonicalDescriptorSerializePrice]
  nlinarith only [hm₁,hm₂]

end
end IntegerMultBounds.MathlibTM2.Routing
