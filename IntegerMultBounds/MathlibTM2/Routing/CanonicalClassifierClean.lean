module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalClassifierGenerate
public import IntegerMultBounds.MathlibTM2.Routing.ClassifierOperandClean
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorClean

/-! Reusable cleanup of all classifier and preceding descriptor setup, with
a disjoint output retained. Later metadata extensions can restore this bank once. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def canonicalClassifierCleanProgram (rg : Fin 118 → Fin T) : Pr P T Q A U :=
  .seq (classifierOperandCleanProgram rg) (canonicalDescriptorCleanProgram (rg ∘ canonicalClassifierCore))

theorem canonicalClassifierClean_exec (body : P → Pr P T Q A U)
    (rg : Fin 118 → Fin T) (hrg : Function.Injective rg) (L n : ℕ) (hn : n < 2 ^ L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i : Fin 118, i ≠ 0 → i ≠ 9 → i ≠ 18 → S.R (rg i) = [])
    (dst : Fin T) (hoff : ∀ i, rg i ≠ dst) (output : List (Fin (A + 4))) :
    let W := (canonicalStageWidths (routerProfileParameters n (canonicalRouterStride n)
      (canonicalRouterGap n) r.val)).coordinateBits
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 44 * L + 166 * W + 195 ∧
      Exec body (canonicalClassifierCleanProgram rg)
        (mk v { S with R := Function.update (canonicalClassifierGeneratedBank S.R rg L n r.val) dst output }) m
        (mk v' { S with R := Function.update S.R dst output }) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let W := (canonicalStageWidths p).coordinateBits
  let core := rg ∘ canonicalClassifierCore
  have hc : Function.Injective core := hrg.comp canonicalClassifierCore_injective
  let B : Stacks T A := { S with R := canonicalDescriptorGeneratedBank S.R core L n r.val }
  have baseBlank (i : Fin 118) (hi : 108 ≤ i.val) : B.R (rg i) = [] := by
    rw [show B.R (rg i) = S.R (rg i) from canonicalDescriptorGeneratedBank_outside S.R core L n r.val _ (by
      intro j he
      have hv := congrArg (fun x : Fin 118 => x.val) (hrg he)
      change j.val = i.val at hv
      have := j.isLt
      omega)]
    apply hblank <;> intro he <;> subst i <;> norm_num at hi
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := classifierOperandClean_exec body rg hrg L W p
    (canonicalClassifier_raw_fit L n hn r) v B baseBlank dst hoff output
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := canonicalDescriptorClean_exec body core hc L n r.val v₁ S (by
      intro i h0 h9 h18
      exact hblank _ (fun he => h0 (Fin.ext (congrArg (fun x : Fin 118 => x.val) he)))
        (fun he => h9 (Fin.ext (congrArg (fun x : Fin 118 => x.val) he)))
        (fun he => h18 (Fin.ext (congrArg (fun x : Fin 118 => x.val) he))))
    dst (fun i => hoff _) output
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  nlinarith only [hm₁,hm₂]

end
end IntegerMultBounds.MathlibTM2.Routing
