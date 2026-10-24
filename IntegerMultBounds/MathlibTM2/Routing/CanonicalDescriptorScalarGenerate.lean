module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalScalarInputGenerate

/-! Generate the shared descriptor scalar bank from binary dimension and residue.
All geometric inputs, target widths and encoding widths are computed at runtime. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}

def canonicalDescriptorScalarGenerateProgram (rg : Fin 46 → Fin T) : Pr P T Q A U :=
  .seq (canonicalScalarInputProgram rg)
    (descriptorScalarResizeProgram (rg ∘ canonicalDescriptorScalarSlot))

theorem canonicalDescriptorScalarGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 46 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hblank : ∀ j : Fin 46, j ≠ 0 → j ≠ 9 → j ≠ 18 → S.R (rg j) = []) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let W := (canonicalStageWidths p).coordinateBits
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 96 * L * L + 652 * L + 875 + 10 * L * (4 * W + 11) + 224 * W ∧
      Exec body (canonicalDescriptorScalarGenerateProgram rg) (mk v S) m
        (mk v' { S with R := (descriptorScalarResizedBank (canonicalDescriptorScalarInputBank S.R rg L n r.val)
          (rg ∘ canonicalDescriptorScalarSlot) W p) }) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let W := (canonicalStageWidths p).coordinateBits
  obtain ⟨v₂,m₂,hu₂,hm₂,hex₂⟩ := canonicalScalarInput_exec body rg hrg L n hn hlarge hdivisor
    r v S hdimension hresidue hblank
  let D : Stacks T A := { S with R := canonicalDescriptorScalarInputBank S.R rg L n r.val }
  obtain ⟨raw, width⟩ := canonicalDescriptorScalarInputBank_ready S.R rg hrg L n hlarge r hresidue
  have hfit := repairDescriptorScalarPalette_fit p r.isLt 10
  change p.wy + 2 * p.wc + 1 < 2 ^ W at hfit
  have hW : W < 2 ^ L := by
    obtain ⟨hi,hgroup,hstride,hselector,hw⟩ := canonicalStageWidths_router n hlarge r
    have hcoord : W ≤ canonicalRouterGap n := by
      change (canonicalStageWidths p).coordinateBits ≤ _
      rw [← canonicalStageWidths_selector]
      change (canonicalStageWidths (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)).selectorBits ≤ _
      rw [hselector]
      exact canonicalDescriptorCoordinateWidth_le_gap n
    have hgap : canonicalRouterGap n ≤ n := by change 64 * canonicalRouterGap n ≤ n at hlarge; omega
    exact hcoord.trans hgap |>.trans_lt hn
  obtain ⟨v₃, m₃, hu₃, hm₃, hex₃⟩ := descriptorScalarResize_exec body (rg ∘ canonicalDescriptorScalarSlot)
    (hrg.comp canonicalDescriptorScalarSlot_injective) L L W p hW hfit
    (canonicalDescriptorScalarRaw_fit L n hn hlarge r) v₂ D width raw
    (canonicalDescriptorScalarInputBank_blank S.R rg hrg L n r.val hblank)
  exact ⟨v₃, m₂ + m₃, hu₃.trans hu₂, by nlinarith only [hm₂, hm₃],
    Exec.seq hex₂ hex₃⟩

end IntegerMultBounds.MathlibTM2.Routing
