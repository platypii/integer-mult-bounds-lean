module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalClassifierReady

/-! Execute classifier setup from the original binary dimension and residue.
All six raw operands and four exact width words are generated internally. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def canonicalClassifierGenerateProgram (rg : Fin 118 → Fin T) : Pr P T Q A U :=
  .seq (canonicalDescriptorGenerateProgram (rg ∘ canonicalClassifierCore)) (classifierGenerateProgram rg)

def canonicalClassifierGeneratedBank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 118 → Fin T) (L n r : ℕ) :=
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
  classifierGeneratedBank (canonicalDescriptorGeneratedBank R (rg ∘ canonicalClassifierCore) L n r)
    rg L (canonicalStageWidths p).coordinateBits p

def canonicalClassifierGeneratePrice (L W : ℕ) (p : Par) : ℕ :=
  96 * L * L + 652 * L + 875 + 10 * L * (4 * W + 11) + 224 * W +
    (8 * W + 9) + 6 * (2 * L * (4 * W + 11) + 12 * (L + W) + 26 * W + 42) + 1 +
    (55 * (2 * L * (4 * W + 11) + 38 * W + 42) + 1) +
    (8 * (L*L + W*W) + 52 * (L+W) + 89) +
    binaryResizeBatchCost (classifierScalarInputWidth L W) (classifierScalarInputWidth L W)
      (classifierScalarWidth p) classifierScalarJobs

theorem canonicalClassifierGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 118 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hblank : ∀ i : Fin 118, i ≠ 0 → i ≠ 9 → i ≠ 18 → S.R (rg i) = []) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ canonicalClassifierGeneratePrice L (canonicalStageWidths p).coordinateBits p ∧
      Exec body (canonicalClassifierGenerateProgram rg) (mk v S) m
        (mk v' { S with R := canonicalClassifierGeneratedBank S.R rg L n r.val }) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let W := (canonicalStageWidths p).coordinateBits
  let core := rg ∘ canonicalClassifierCore
  have hc : Function.Injective core := hrg.comp canonicalClassifierCore_injective
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalDescriptorGenerate_exec body core hc L n hn hlarge hdivisor
    r v S hdimension hresidue (by
      intro i h0 h9 h18
      exact hblank _ (fun he => h0 (Fin.ext (congrArg (fun x : Fin 118 => x.val) he)))
        (fun he => h9 (Fin.ext (congrArg (fun x : Fin 118 => x.val) he)))
        (fun he => h18 (Fin.ext (congrArg (fun x : Fin 118 => x.val) he))))
  let C : Stacks T A := { S with R := canonicalDescriptorGeneratedBank S.R core L n r.val }
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := classifierGenerate_exec body rg hrg L W p
    (canonicalClassifier_raw_fit L n hn r) v₁ C
    (canonicalClassifier_sources S.R rg hrg L n hlarge r hresidue)
    (canonicalClassifier_blank S.R rg hrg L n r.val hblank)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  dsimp only [canonicalClassifierGeneratePrice]
  nlinarith only [hm₁,hm₂]

end
end IntegerMultBounds.MathlibTM2.Routing
