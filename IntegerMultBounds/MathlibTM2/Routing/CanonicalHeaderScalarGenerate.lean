module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalClassifierGenerate
public import IntegerMultBounds.MathlibTM2.Routing.HeaderScalarGenerate

/-! Generate the inner one-row header operands after canonical classifier and
descriptor setup, using the already generated borrowed-width palette word. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def canonicalHeaderScalarCore : Fin 118 → Fin 120 := Fin.castLE (by decide)
theorem canonicalHeaderScalarCore_injective : Function.Injective canonicalHeaderScalarCore := by decide +kernel
def canonicalHeaderScalarSlot : Fin 5 → Fin 120 := ![34,118,119,40,41]
theorem canonicalHeaderScalarSlot_injective : Function.Injective canonicalHeaderScalarSlot := by decide +kernel

def canonicalHeaderScalarGenerateProgram (rg : Fin 120 → Fin T) : Pr P T Q A U :=
  .seq (canonicalClassifierGenerateProgram (rg ∘ canonicalHeaderScalarCore))
    (headerScalarGenerateProgram (rg ∘ canonicalHeaderScalarSlot))

def canonicalHeaderScalarGeneratedBank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 120 → Fin T) (L n r : ℕ) :=
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
  headerScalarBank (canonicalClassifierGeneratedBank R (rg ∘ canonicalHeaderScalarCore) L n r)
    (rg ∘ canonicalHeaderScalarSlot) p.wc

theorem canonicalHeaderScalarGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 120 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hblank : ∀ i : Fin 120, i ≠ 0 → i ≠ 9 → i ≠ 18 → S.R (rg i) = []) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let W := (canonicalStageWidths p).coordinateBits
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ canonicalClassifierGeneratePrice L W p + 10 * W + 13 ∧
      Exec body (canonicalHeaderScalarGenerateProgram rg) (mk v S) m
        (mk v' { S with R := canonicalHeaderScalarGeneratedBank S.R rg L n r.val }) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let W := (canonicalStageWidths p).coordinateBits
  let core := rg ∘ canonicalHeaderScalarCore
  have hc : Function.Injective core := hrg.comp canonicalHeaderScalarCore_injective
  let D := canonicalDescriptorGeneratedBank S.R (core ∘ canonicalClassifierCore) L n r.val
  let C : Stacks T A := { S with R := canonicalClassifierGeneratedBank S.R core L n r.val }
  have cb : ∀ i : Fin 118, i ≠ 0 → i ≠ 9 → i ≠ 18 → S.R (core i) = [] := by
    intro i h0 h9 h18
    exact hblank _ (fun he => h0 (Fin.ext (congrArg (fun x : Fin 120 => x.val) he)))
      (fun he => h9 (Fin.ext (congrArg (fun x : Fin 120 => x.val) he)))
      (fun he => h18 (Fin.ext (congrArg (fun x : Fin 120 => x.val) he)))
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalClassifierGenerate_exec body core hc L n hn hlarge
    hdivisor r v S hdimension hresidue cb
  have hsrc : C.R (rg 34) = binSyms W p.wc := by
    have h₁ := classifierGeneratedBank_low D core hc L W p 34 (by decide)
    have h₂ := canonicalDescriptorGeneratedBank_low S.R (core ∘ canonicalClassifierCore)
      (hc.comp canonicalClassifierCore_injective) L n r.val 34 (by decide)
    have h₃ := canonicalDescriptorInstall_palette S.R
      (rg ∘ (Fin.castLE (by decide) : Fin 101 → Fin 120))
      (hrg.comp (by decide +kernel)) L n r.val 6
    exact h₁.trans (h₂.trans h₃)
  have scratch (i : Fin 118)
      (hi : i ∈ ([39,40,41,42,43,45,108,109,110,111,112,113,114,115,116,117] : List (Fin 118)))
      (hlo : i.val < 108) : C.R (core i) = [] :=
    (classifierGeneratedBank_low D core hc L W p i hlo).trans
      (canonicalClassifier_blank S.R core hc L n r.val cb i hi)
  have outside (i : Fin 120) (hi : 118 ≤ i.val) : C.R (rg i) = [] := by
    have off (j : Fin 118) : core j ≠ rg i := by
      intro he
      have hv := congrArg (fun x : Fin 120 => x.val) (hrg he)
      change j.val = i.val at hv
      have := j.isLt
      omega
    rw [show C.R (rg i) = S.R (rg i) from
      (classifierGeneratedBank_outside D core L W p _ off).trans
        (canonicalDescriptorGeneratedBank_outside S.R (core ∘ canonicalClassifierCore) L n r.val _ (fun j => off _))]
    apply hblank <;> intro he <;> subst i <;> norm_num at hi
  obtain ⟨v₂,hu₂,he₂⟩ := headerScalarGenerate_exec body (rg ∘ canonicalHeaderScalarSlot)
    (hrg.comp canonicalHeaderScalarSlot_injective) W p.wc
    (repairDescriptorScalarPalette_fit p r.isLt 6) v₁ C hsrc (by
      intro i hi
      fin_cases i
      · exact (hi rfl).elim
      · exact outside 118 (by decide)
      · exact outside 119 (by decide)
      · exact scratch 40 (by simp) (by decide)
      · exact scratch 41 (by simp) (by decide))
  refine ⟨v₂,m₁+(10*W+13),hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  nlinarith only [hm₁]

end
end IntegerMultBounds.MathlibTM2.Routing
