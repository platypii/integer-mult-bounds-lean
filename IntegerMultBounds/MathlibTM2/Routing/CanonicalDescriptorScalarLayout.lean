module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorScalarResize
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalProfileScope
public import IntegerMultBounds.MathlibTM2.Routing.RouterTargetWidthGenerate

/-! Concrete shared layout for canonical geometry, target-width generation and
the descriptor scalar palette. Raw inputs alias geometry outputs directly. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T A : ℕ}

def canonicalDescriptorGeometrySlot : Fin 28 → Fin 46 := Fin.castLE (by decide)
def canonicalDescriptorTargetSlot : Fin 9 → Fin 46 := ![0,16,20,22,44,23,24,3,9]
def canonicalDescriptorScalarSlot : Fin 24 → Fin 46 :=
  ![28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,9,1,2,18,44,16,26,45]
theorem canonicalDescriptorGeometrySlot_injective : Function.Injective canonicalDescriptorGeometrySlot := by decide +kernel
theorem canonicalDescriptorTargetSlot_injective : Function.Injective canonicalDescriptorTargetSlot := by decide +kernel
theorem canonicalDescriptorScalarSlot_injective : Function.Injective canonicalDescriptorScalarSlot := by decide +kernel

def canonicalDescriptorScalarInputBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 46 → Fin T)
    (L n r : ℕ) : Fin T → List (Fin (A + 4)) :=
  Function.update (canonicalProfileSetupBank R (rg ∘ canonicalDescriptorGeometrySlot) L n r) (rg 44)
    (binSyms L (routerTargetWidth n (canonicalRouterStride n) (canonicalRouterGap n)))

theorem canonicalDescriptorScalarInputBank_blank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 46 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ)
    (hblank : ∀ j : Fin 46, j ≠ 0 → j ≠ 9 → j ≠ 18 → R (rg j) = [])
    (j : Fin 24) (hj : j ∉ ([16,17,18,19,20,21,22] : List (Fin 24))) :
    canonicalDescriptorScalarInputBank R rg L n r (rg (canonicalDescriptorScalarSlot j)) = [] := by
  have sep : canonicalDescriptorScalarSlot j ≠ 44 ∧
      canonicalDescriptorScalarSlot j ∉ canonicalProfileTargets canonicalDescriptorGeometrySlot ∧
      canonicalDescriptorScalarSlot j ≠ 0 ∧ canonicalDescriptorScalarSlot j ≠ 9 ∧
      canonicalDescriptorScalarSlot j ≠ 18 := by
    fin_cases j <;> simp_all [canonicalDescriptorScalarSlot, canonicalProfileTargets, canonicalDescriptorGeometrySlot]
  unfold canonicalDescriptorScalarInputBank
  rw [Function.update_of_ne (hrg.ne sep.1)]
  rw [canonicalProfileSetupBank_keep R (rg ∘ canonicalDescriptorGeometrySlot) L n r _ (by
    simpa [canonicalProfileTargets, hrg.eq_iff] using sep.2.1)]
  exact hblank _ sep.2.2.1 sep.2.2.2.1 sep.2.2.2.2

/-- All five compact geometric values fit the original dimension encoding. -/
theorem canonicalDescriptorScalarRaw_fit (L n : ℕ) (hn : n < 2 ^ L)
    (hlarge : canonicalRouterStride n ≤ n) (r : Fin (canonicalRouterStride n)) (j : Fin 5) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    repairDescriptorScalarPalette p (descriptorScalarInputIndex j) < 2 ^ L := by
  dsimp only
  have hdecomp := routerGeometry_decomposition n (canonicalRouterStride n) (canonicalRouterGap n) hlarge
  have hborrowed : routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n) ≤ n := by omega
  have hwidth := routerProfileParameters_width n (canonicalRouterStride n) (canonicalRouterGap n) hlarge r
  have hg : canonicalRouterGap n ≤ n := by
    change 64 * canonicalRouterGap n ≤ n at hlarge
    omega
  have hr := r.isLt
  fin_cases j <;> simp [repairDescriptorScalarPalette, descriptorScalarInputIndex,
    routerProfileParameters_borrowed, hwidth, routerTargetWidth]
  all_goals first | exact hlarge.trans_lt hn | exact hg.trans_lt hn | exact hr.trans (hlarge.trans_lt hn) | exact (Nat.sub_le _ _).trans_lt hn | exact hborrowed.trans_lt hn

theorem canonicalDescriptorScalarInputBank_ready (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 46 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hlarge : canonicalRouterStride n ≤ n) (r : Fin (canonicalRouterStride n))
    (hresidue : R (rg 18) = binSyms L r.val) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let B := canonicalDescriptorScalarInputBank R rg L n r.val
    (∀ j : Fin 5, B (rg (canonicalDescriptorScalarSlot ⟨17 + j.val, by have := j.isLt; omega⟩)) =
      binSyms L (repairDescriptorScalarPalette p (descriptorScalarInputIndex j))) ∧
      B (rg (canonicalDescriptorScalarSlot 22)) = binSyms L (canonicalStageWidths p).coordinateBits := by
  dsimp only
  let C := canonicalProfileSetupBank R (rg ∘ canonicalDescriptorGeometrySlot) L n r.val
  have hgeo := hrg.comp canonicalDescriptorGeometrySlot_injective
  obtain ⟨hK,hρ,hn,hW,hcoord⟩ := canonicalProfileSetup_parameters R (rg ∘ canonicalDescriptorGeometrySlot)
    hgeo L n hlarge r hresidue
  have keep (j : Fin 46) (hj : j ≠ 44) :
      canonicalDescriptorScalarInputBank R rg L n r.val (rg j) = C (rg j) := by
    simp [canonicalDescriptorScalarInputBank, hrg.eq_iff, hj, C]
  constructor
  · intro j
    fin_cases j
    · change canonicalDescriptorScalarInputBank R rg L n r.val (rg 1) = _
      exact (keep 1 (by decide)).trans hK
    · change canonicalDescriptorScalarInputBank R rg L n r.val (rg 2) = _
      have hg : C (rg 2) = binSyms L (canonicalRouterGap n) := by
        simp [C, canonicalProfileSetupBank, canonicalDescriptorWidthsBank, canonicalResidueGeometryBank,
          canonicalGeometryBank, routerReservoirGeometryBank, routerGeometryBank, canonicalProfileWidthSlot,
          canonicalProfileGeometrySlot, canonicalResidueCommonSlot, routerReservoirCommonSlot,
          canonicalDescriptorGeometrySlot, hrg.eq_iff]
      exact (keep 2 (by decide)).trans hg
    · change canonicalDescriptorScalarInputBank R rg L n r.val (rg 18) = _
      exact (keep 18 (by decide)).trans hρ
    · change canonicalDescriptorScalarInputBank R rg L n r.val (rg 44) = _
      simp [canonicalDescriptorScalarInputBank, descriptorScalarInputIndex, repairDescriptorScalarPalette,
        routerProfileParameters_width n _ _ hlarge r]
    · change canonicalDescriptorScalarInputBank R rg L n r.val (rg 16) = _
      rw [keep 16 (by decide)]
      simp [C, canonicalProfileSetupBank, canonicalDescriptorWidthsBank, canonicalResidueGeometryBank,
        canonicalGeometryBank, routerReservoirGeometryBank, routerGeometryBank, canonicalProfileWidthSlot,
        canonicalProfileGeometrySlot, canonicalResidueCommonSlot, routerReservoirCommonSlot,
        canonicalDescriptorGeometrySlot, descriptorScalarInputIndex, repairDescriptorScalarPalette,
        routerProfileParameters_borrowed, canonicalRouterStride, hrg.eq_iff]
  · change canonicalDescriptorScalarInputBank R rg L n r.val (rg 26) = _
    exact (keep 26 (by decide)).trans hcoord

end IntegerMultBounds.MathlibTM2.Routing
