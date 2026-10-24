module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRepairScalarRestore
public import IntegerMultBounds.MathlibTM2.Routing.HeaderScalarRestore
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalClassifierClean

/-! One cleanup proof for either repair serialization order. All setup tapes
restore while a disjoint caller output is retained. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def canonicalRepairCleanProgram (rg : Fin 130 → Fin T) : Pr P T Q A U :=
  .seq (metadataClean (canonicalRepairScalarSlots.map rg))
    (.seq (metadataClean [rg 118,rg 119])
      (canonicalClassifierCleanProgram (rg ∘ canonicalRepairBlockHeader ∘ canonicalHeaderScalarCore)))

theorem canonicalRepairClean_exec (body : P → Pr P T Q A U)
    (rg : Fin 130 → Fin T) (hrg : Function.Injective rg) (L n B : ℕ) (hn : n < 2^L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i : Fin 130, i ≠ 0 → i ≠ 9 → i ≠ 18 → i ≠ 120 → S.R (rg i) = [])
    (dst : Fin T) (hoff : ∀ i, rg i ≠ dst) (output : List (Fin (A+4))) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let W := (canonicalStageWidths p).coordinateBits
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ (2*(p.wc+p.wy+(n+1)+canonicalScalarWidth (n+1)+canonicalScalarWidth B+
        canonicalScalarWidth (n+B+1))+13) + (2*W+7) + (44*L+166*W+195) ∧
      Exec body (canonicalRepairCleanProgram rg)
        (mk v { S with R := Function.update (canonicalRepairBlockGeneratedBank S.R rg L n r.val B) dst output }) m
        (mk v' { S with R := Function.update S.R dst output }) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let W := (canonicalStageWidths p).coordinateBits
  let header := rg ∘ canonicalRepairBlockHeader
  have hh : Function.Injective header := hrg.comp canonicalRepairBlockHeader_injective
  let core := header ∘ canonicalHeaderScalarCore
  have hc : Function.Injective core := hh.comp canonicalHeaderScalarCore_injective
  have hb : ∀ i : Fin 120, i ≠ 0 → i ≠ 9 → i ≠ 18 → S.R (header i) = [] := by
    intro i h0 h9 h18
    apply hblank
    · intro h; exact h0 (Fin.ext (congrArg (fun k : Fin 130 => k.val) h))
    · intro h; exact h9 (Fin.ext (congrArg (fun k : Fin 130 => k.val) h))
    · intro h; exact h18 (Fin.ext (congrArg (fun k : Fin 130 => k.val) h))
    · intro h
      have hv := congrArg (fun k : Fin 130 => k.val) h
      change i.val = 120 at hv
      have := i.isLt
      omega
  obtain ⟨v₂,hu₂,he₂⟩ := canonicalRepairScalarRestore_exec body rg hrg L n r.val B v S (by
    intro i hi
    simp only [canonicalRepairScalarSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> apply hblank <;> decide) dst hoff output
  let C : Stacks T A := { S with R := canonicalClassifierGeneratedBank S.R core L n r.val }
  have newBlank (i : Fin 120) (hi : 118 ≤ i.val) : C.R (header i) = [] := by
    have off (j : Fin 118) : core j ≠ header i := by
      intro he
      have hv := congrArg (fun x : Fin 120 => x.val) (hh he)
      change j.val = i.val at hv
      have := j.isLt
      omega
    rw [show C.R (header i) = S.R (header i) from
      (classifierGeneratedBank_outside _ core L W p _ off).trans
        (canonicalDescriptorGeneratedBank_outside S.R (core ∘ canonicalClassifierCore) L n r.val _ (fun j => off _))]
    apply hb <;> intro he <;> subst i <;> norm_num at hi
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := headerScalarRestore_exec body (header ∘ canonicalHeaderScalarSlot)
    (hh.comp canonicalHeaderScalarSlot_injective) W p.wc (repairDescriptorScalarPalette_fit p r.isLt 6)
    v₂ C (newBlank 118 (by decide)) (newBlank 119 (by decide)) dst
    ⟨(hoff 118).symm,(hoff 119).symm⟩ output
  obtain ⟨v₄,m₄,hu₄,hm₄,he₄⟩ := canonicalClassifierClean_exec body core hc L n hn r v₃ S (by
    intro i h0 h9 h18
    exact hb _ (fun he => h0 (Fin.ext (congrArg (fun x : Fin 120 => x.val) he)))
      (fun he => h9 (Fin.ext (congrArg (fun x : Fin 120 => x.val) he)))
      (fun he => h18 (Fin.ext (congrArg (fun x : Fin 120 => x.val) he))))
    dst (fun i => hoff _) output
  refine ⟨v₄,(_+(m₃+m₄)),hu₄.trans (hu₃.trans hu₂),?_,
    Exec.seq he₂ (Exec.seq he₃ he₄)⟩
  rw [← canonicalRepairScalarCleanCost S.R rg hrg L n r.val B]
  nlinarith only [hm₃,hm₄]

end
end IntegerMultBounds.MathlibTM2.Routing
