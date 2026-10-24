module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorSharedReady

/-! Execute generation of the six shared descriptor operands using only the
original binary dimension and residue. Width words and constants are generated. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}

def canonicalDescriptorSharedGenerateProgram (rg : Fin 108 → Fin T) : Pr P T Q A U :=
  .seq (canonicalDescriptorScalarGenerateProgram (rg ∘ canonicalDescriptorSharedCore))
    (descriptorSharedInstallProgram rg)

def canonicalDescriptorSharedGeneratedBank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 108 → Fin T) (L n r : ℕ) :=
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
  descriptorSharedGeneratedBank
    (canonicalDescriptorScalarBank R (rg ∘ canonicalDescriptorSharedCore) L n r)
    rg (canonicalStageWidths p).coordinateBits p (canonicalStageWidths p)

theorem canonicalDescriptorSharedGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 108 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hblank : ∀ i : Fin 108, i ≠ 0 → i ≠ 9 → i ≠ 18 → S.R (rg i) = []) :
    let W := (canonicalStageWidths (routerProfileParameters n (canonicalRouterStride n)
      (canonicalRouterGap n) r.val)).coordinateBits
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 96 * L * L + 652 * L + 875 + 10 * L * (4 * W + 11) + 224 * W +
        (8 * W + 9) + 6 * (2 * L * (4 * W + 11) + 12 * (L + W) + 26 * W + 42) + 1 ∧
      Exec body (canonicalDescriptorSharedGenerateProgram rg) (mk v S) m
        (mk v' { S with R := canonicalDescriptorSharedGeneratedBank S.R rg L n r.val }) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let W := (canonicalStageWidths p).coordinateBits
  let core := rg ∘ canonicalDescriptorSharedCore
  have hc : Function.Injective core := hrg.comp canonicalDescriptorSharedCore_injective
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalDescriptorScalarGenerate_exec body core hc L n hn hlarge
    hdivisor r v S hdimension hresidue (by
      intro i h0 h9 h18
      exact hblank _ (fun he => h0 (Fin.ext (congrArg (fun x : Fin 108 => x.val) he)))
        (fun he => h9 (Fin.ext (congrArg (fun x : Fin 108 => x.val) he)))
        (fun he => h18 (Fin.ext (congrArg (fun x : Fin 108 => x.val) he))))
  let C : Stacks T A := { S with R := canonicalDescriptorScalarBank S.R core L n r.val }
  obtain ⟨hw,hv,hz⟩ := canonicalDescriptorShared_inputs S.R rg hrg L n hlarge r
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := descriptorSharedInstall_exec body rg hrg L W p
    (canonicalStageWidths p)
    (fun i => (canonicalDescriptorShared_width_le p i).trans_lt
      (canonicalDescriptorInstall_width_fit L n hn hlarge r))
    (canonicalDescriptorShared_value_fit L n hn hlarge r) v₁ C hw hv hz (by
      intro i hi
      apply canonicalDescriptorShared_blank S.R rg hrg L n r.val
      · intro k hk
        apply hblank <;> intro he <;> subst k <;> norm_num at hk
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hcost := descriptorSharedInstallCost_le L W W (canonicalStageWidths p)
    (canonicalDescriptorShared_width_le p)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  nlinarith only [hm₁,hm₂,hcost]

end IntegerMultBounds.MathlibTM2.Routing
