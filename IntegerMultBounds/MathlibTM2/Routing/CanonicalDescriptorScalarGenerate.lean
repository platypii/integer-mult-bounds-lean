module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorScalarLayout

/-! Generate the shared descriptor scalar bank from binary dimension and residue.
All geometric inputs, target widths and encoding widths are computed at runtime. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}

def canonicalDescriptorScalarGenerateProgram (rg : Fin 46 → Fin T) : Pr P T Q A U :=
  .seq (canonicalProfileSetupProgram (rg ∘ canonicalDescriptorGeometrySlot))
    (.seq (routerTargetWidthGenerateProgram (rg ∘ canonicalDescriptorTargetSlot))
      (descriptorScalarResizeProgram (rg ∘ canonicalDescriptorScalarSlot)))

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
  have hg := hrg.comp canonicalDescriptorGeometrySlot_injective
  have hgeometryBlank : ∀ j : Fin 28, j ≠ 0 → j ≠ 9 → j ≠ 18 →
      S.R ((rg ∘ canonicalDescriptorGeometrySlot) j) = [] := by
    intro j h0 h9 h18
    apply hblank
    · exact fun h => h0 (Fin.ext (congrArg (fun k : Fin 46 => k.val) h))
    · exact fun h => h9 (Fin.ext (congrArg (fun k : Fin 46 => k.val) h))
    · exact fun h => h18 (Fin.ext (congrArg (fun k : Fin 46 => k.val) h))
  obtain ⟨v₁, m₁, hu₁, hm₁, hex₁⟩ := canonicalProfileSetup_exec body (rg ∘ canonicalDescriptorGeometrySlot)
    hg L n r.val hn hlarge hdivisor r.isLt v S hdimension hresidue hgeometryBlank
  let C : Stacks T A := { S with R := canonicalProfileSetupBank S.R (rg ∘ canonicalDescriptorGeometrySlot) L n r.val }
  have keep (j : Fin 46) (hj : j ∉ canonicalProfileTargets canonicalDescriptorGeometrySlot) :
      C.R (rg j) = S.R (rg j) := by
    apply canonicalProfileSetupBank_keep
    simpa [canonicalProfileTargets, hrg.eq_iff] using hj
  have borrowed : C.R (rg 16) = binSyms L (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) := by
    simp [C, canonicalProfileSetupBank, canonicalDescriptorWidthsBank, canonicalResidueGeometryBank,
      canonicalGeometryBank, routerReservoirGeometryBank, routerGeometryBank, canonicalProfileWidthSlot,
      canonicalProfileGeometrySlot, canonicalResidueCommonSlot, routerReservoirCommonSlot,
      canonicalDescriptorGeometrySlot, canonicalRouterStride, hrg.eq_iff]
  have targetBlank : ∀ j : Fin 9, j ≠ 0 → j ≠ 1 → j ≠ 8 →
      C.R ((rg ∘ canonicalDescriptorTargetSlot) j) = [] := by
    intro j h0 h1 h8
    have sep : canonicalDescriptorTargetSlot j ∉ canonicalProfileTargets canonicalDescriptorGeometrySlot ∧
        canonicalDescriptorTargetSlot j ≠ 0 ∧ canonicalDescriptorTargetSlot j ≠ 9 ∧ canonicalDescriptorTargetSlot j ≠ 18 := by
      fin_cases j <;> simp_all [canonicalDescriptorTargetSlot, canonicalProfileTargets, canonicalDescriptorGeometrySlot]
    exact (keep _ sep.1).trans (hblank _ sep.2.1 sep.2.2.1 sep.2.2.2)
  have hdecomp := routerGeometry_decomposition n (canonicalRouterStride n) (canonicalRouterGap n) hlarge
  obtain ⟨v₂, hu₂, hex₂⟩ := routerTargetWidthGenerate_exec body (rg ∘ canonicalDescriptorTargetSlot)
    (hrg.comp canonicalDescriptorTargetSlot_injective) L n (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
    hn (by omega) v₁ C ((keep 0 (by decide)).trans hdimension) borrowed targetBlank
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
  exact ⟨v₃, m₁ + ((30 * L + 34) + m₃), hu₃.trans (hu₂.trans hu₁), by nlinarith only [hm₁, hm₃],
    Exec.seq hex₁ (Exec.seq hex₂ hex₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
