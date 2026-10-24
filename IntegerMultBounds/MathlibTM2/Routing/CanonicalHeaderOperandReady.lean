module

public import IntegerMultBounds.MathlibTM2.Routing.HeaderOperandFrame

/-! Complete header-frame readiness follows from generated classifier and
descriptor banks. Unrelated registers and prior metadata remain unchanged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T A : ℕ}

theorem canonicalHeaderBase_blank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 120 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ)
    (hblank : ∀ i : Fin 120, i ≠ 0 → i ≠ 9 → i ≠ 18 → R (rg i) = [])
    (i : Fin 118) (hi : i ∈ ([39,40,41,42,43,45] : List (Fin 118))) :
    canonicalClassifierGeneratedBank R (rg ∘ canonicalHeaderScalarCore) L n r
      (rg (canonicalHeaderScalarCore i)) = [] := by
  let core := rg ∘ canonicalHeaderScalarCore
  have hc : Function.Injective core := hrg.comp canonicalHeaderScalarCore_injective
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
  have hlo : i.val < 108 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  change canonicalClassifierGeneratedBank R core L n r (core i) = []
  rw [show canonicalClassifierGeneratedBank R core L n r (core i) =
      canonicalDescriptorGeneratedBank R (core ∘ canonicalClassifierCore) L n r (core i) from
      classifierGeneratedBank_low _ core hc L (canonicalStageWidths p).coordinateBits p i hlo]
  apply canonicalClassifier_blank R core hc L n r
  · intro j h0 h9 h18
    exact hblank _ (fun he => h0 (Fin.ext (congrArg (fun x : Fin 120 => x.val) he)))
      (fun he => h9 (Fin.ext (congrArg (fun x : Fin 120 => x.val) he)))
      (fun he => h18 (Fin.ext (congrArg (fun x : Fin 120 => x.val) he)))
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem canonicalHeaderScalarGeneratedBank_low (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 120 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ)
    (i : Fin 120) (hi : i.val < 118) :
    canonicalHeaderScalarGeneratedBank R rg L n r (rg i) =
      canonicalClassifierGeneratedBank R (rg ∘ canonicalHeaderScalarCore) L n r (rg i) := by
  have h118 : i ≠ 118 := by intro h; subst i; norm_num at hi
  have h119 : i ≠ 119 := by intro h; subst i; norm_num at hi
  simp [canonicalHeaderScalarGeneratedBank,headerScalarBank,canonicalHeaderScalarSlot,
    hrg.eq_iff,h118,h119]

theorem canonicalHeaderScalarGeneratedBank_palette (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 120 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ) (j : Fin 11) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
    canonicalHeaderScalarGeneratedBank R rg L n r
      (rg ⟨28+j.val,by have := j.isLt; omega⟩) =
        binSyms (canonicalStageWidths p).coordinateBits (repairDescriptorScalarPalette p j) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
  let W := (canonicalStageWidths p).coordinateBits
  let core := rg ∘ canonicalHeaderScalarCore
  have hc : Function.Injective core := hrg.comp canonicalHeaderScalarCore_injective
  have h₁ := canonicalHeaderScalarGeneratedBank_low R rg hrg L n r
    ⟨28+j.val,by have := j.isLt; omega⟩ (by change 28+j.val < 118; have := j.isLt; omega)
  have h₂ := classifierGeneratedBank_low
    (canonicalDescriptorGeneratedBank R (core ∘ canonicalClassifierCore) L n r) core hc L W p
    ⟨28+j.val,by have := j.isLt; omega⟩ (by change 28+j.val < 108; have := j.isLt; omega)
  have h₃ := canonicalDescriptorGeneratedBank_low R (core ∘ canonicalClassifierCore)
    (hc.comp canonicalClassifierCore_injective) L n r
    ⟨28+j.val,by have := j.isLt; omega⟩ (by change 28+j.val < 46; have := j.isLt; omega)
  have h₄ := canonicalDescriptorInstall_palette R
    (rg ∘ (Fin.castLE (by decide) : Fin 101 → Fin 120))
    (hrg.comp (by decide +kernel)) L n r j
  exact h₁.trans (h₂.trans (h₃.trans h₄))

theorem canonicalHeaderScalarGeneratedBank_dimension (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 120 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ) :
    canonicalHeaderScalarGeneratedBank R rg L n r (rg 0) = R (rg 0) := by
  let core := rg ∘ canonicalHeaderScalarCore
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
  have hc : Function.Injective core := hrg.comp canonicalHeaderScalarCore_injective
  have hd := hc.comp canonicalClassifierCore_injective
  let scalar := (core ∘ canonicalClassifierCore) ∘ canonicalDescriptorSharedCore
  have hs : Function.Injective scalar := hd.comp canonicalDescriptorSharedCore_injective
  have h₁ := canonicalHeaderScalarGeneratedBank_low R rg hrg L n r 0 (by decide)
  have h₂ := classifierGeneratedBank_low
    (canonicalDescriptorGeneratedBank R (core ∘ canonicalClassifierCore) L n r) core hc
    L (canonicalStageWidths p).coordinateBits p 0 (by decide)
  have h₃ := canonicalDescriptorGeneratedBank_low R (core ∘ canonicalClassifierCore) hd L n r 0 (by decide)
  have h₄ := canonicalDescriptorScalarBank_keep R scalar L n r (scalar 0)
    (by simp [canonicalDescriptorScalarTargets,hs.eq_iff])
  exact h₁.trans (h₂.trans (h₃.trans h₄))

theorem canonicalHeaderScalarGeneratedBank_operands (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 120 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ)
    (hblank : ∀ i : Fin 120, i ≠ 0 → i ≠ 9 → i ≠ 18 → R (rg i) = []) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
    (fun role => canonicalHeaderScalarGeneratedBank R rg L n r (rg (headerOperandSource role))) =
      canonicalHeaderOperands (canonicalScalarWidth 1) (canonicalScalarWidth p.wc) 1 p.wc := by
  exact headerScalarBank_operands _ rg hrg _ (canonicalHeaderBase_blank R rg hrg L n r hblank 39 (by simp))

theorem canonicalHeaderScalarGeneratedBank_scratch (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 120 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ)
    (hblank : ∀ i : Fin 120, i ≠ 0 → i ≠ 9 → i ≠ 18 → R (rg i) = []) (i : Fin 2) :
    canonicalHeaderScalarGeneratedBank R rg L n r (rg (if i = 0 then 40 else 41)) = [] := by
  fin_cases i
  · change canonicalHeaderScalarGeneratedBank R rg L n r (rg 40) = []
    rw [canonicalHeaderScalarGeneratedBank_low R rg hrg L n r 40 (by decide)]
    exact canonicalHeaderBase_blank R rg hrg L n r hblank 40 (by simp)
  · change canonicalHeaderScalarGeneratedBank R rg L n r (rg 41) = []
    rw [canonicalHeaderScalarGeneratedBank_low R rg hrg L n r 41 (by decide)]
    exact canonicalHeaderBase_blank R rg hrg L n r hblank 41 (by simp)

theorem canonicalHeaderScalarGeneratedBank_outside (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 120 → Fin T) (L n r : ℕ) (k : Fin T) (hoff : ∀ i, rg i ≠ k) :
    canonicalHeaderScalarGeneratedBank R rg L n r k = R k := by
  let core := rg ∘ canonicalHeaderScalarCore
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
  have he : canonicalHeaderScalarGeneratedBank R rg L n r k =
      canonicalClassifierGeneratedBank R core L n r k := by
    simp [canonicalHeaderScalarGeneratedBank,headerScalarBank,canonicalHeaderScalarSlot,
      (hoff 118).symm,(hoff 119).symm,core]
  rw [he]
  exact (classifierGeneratedBank_outside _ core L (canonicalStageWidths p).coordinateBits p k (fun i => hoff _)).trans
    (canonicalDescriptorGeneratedBank_outside R (core ∘ canonicalClassifierCore) L n r k (fun i => hoff _))

end IntegerMultBounds.MathlibTM2.Routing
