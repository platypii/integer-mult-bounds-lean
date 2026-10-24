module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorScalarGenerate

/-! Exact cleanup ledger for generated geometry and the shared descriptor scalar
bank. Every generated word is erased once; source inputs and spectators restore. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {T A : ℕ}

def canonicalDescriptorScalarBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 46 → Fin T)
    (L n r : ℕ) : Fin T → List (Fin (A + 4)) :=
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
  descriptorScalarResizedBank (canonicalDescriptorScalarInputBank R rg L n r)
    (rg ∘ canonicalDescriptorScalarSlot) (canonicalStageWidths p).coordinateBits p

def canonicalDescriptorScalarTargets (rg : Fin 46 → Fin T) : List (Fin T) :=
  [rg 1,rg 2,rg 11,rg 14,rg 16,rg 17,rg 19,rg 21,rg 25,rg 26,rg 27,rg 44,
    rg 28,rg 29,rg 30,rg 31,rg 32,rg 33,rg 34,rg 35,rg 36,rg 37,rg 38]

theorem canonicalDescriptorScalarBank_keep
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 46 → Fin T) (L n r : ℕ)
    (x : Fin T) (hx : x ∉ canonicalDescriptorScalarTargets rg) :
    canonicalDescriptorScalarBank R rg L n r x = R x := by
  simp only [canonicalDescriptorScalarTargets, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  simp_all [canonicalDescriptorScalarBank, descriptorScalarResizedBank, descriptorScalarBank,
    binaryResizeBatchBank, descriptorScalarResizeSlot, descriptorScalarInputIndex, descriptorScalarCoreSlot,
    canonicalDescriptorScalarInputBank, canonicalProfileSetupBank, canonicalDescriptorWidthsBank,
    canonicalResidueGeometryBank, canonicalGeometryBank, routerReservoirGeometryBank, routerGeometryBank,
    canonicalDescriptorScalarSlot, canonicalDescriptorGeometrySlot, canonicalProfileWidthSlot,
    canonicalProfileGeometrySlot, canonicalResidueCommonSlot, routerReservoirCommonSlot]

theorem canonicalDescriptorScalarBank_clean
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 46 → Fin T) (L n r : ℕ)
    (hblank : ∀ x ∈ canonicalDescriptorScalarTargets rg, R x = []) :
    metadataCleared (canonicalDescriptorScalarBank R rg L n r) (canonicalDescriptorScalarTargets rg) = R := by
  funext x
  by_cases hx : x ∈ canonicalDescriptorScalarTargets rg
  · rw [metadataCleared_at _ _ _ hx]
    exact (hblank x hx).symm
  · rw [metadataCleared_keep _ _ _ hx, canonicalDescriptorScalarBank_keep R rg L n r x hx]

theorem canonicalDescriptorScalarBank_cleanCost
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 46 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ) :
    metadataCleanCost (canonicalDescriptorScalarBank R rg L n r) (canonicalDescriptorScalarTargets rg) =
      24 * L + 22 * (canonicalStageWidths
        (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r)).coordinateBits + 47 := by
  simp [canonicalDescriptorScalarTargets, metadataCleanCost, canonicalDescriptorScalarBank,
    descriptorScalarResizedBank, descriptorScalarBank, binaryResizeBatchBank, descriptorScalarResizeSlot,
    descriptorScalarInputIndex, descriptorScalarCoreSlot, canonicalDescriptorScalarInputBank,
    canonicalProfileSetupBank, canonicalDescriptorWidthsBank, canonicalResidueGeometryBank,
    canonicalGeometryBank, routerReservoirGeometryBank, routerGeometryBank, canonicalDescriptorScalarSlot,
    canonicalDescriptorGeometrySlot, canonicalProfileWidthSlot, canonicalProfileGeometrySlot,
    canonicalResidueCommonSlot, routerReservoirCommonSlot, hrg.eq_iff, length_binSyms]
  ring

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
variable {Q : ℕ} {P U : Type}

def canonicalDescriptorScalarScope (rg : Fin 46 → Fin T) (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq (canonicalDescriptorScalarGenerateProgram rg) (.seq call (metadataClean (canonicalDescriptorScalarTargets rg)))

theorem canonicalDescriptorScalarScope_exec (body : P → Pr P T Q A U)
    (rg : Fin 46 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hblank : ∀ j : Fin 46, j ≠ 0 → j ≠ 9 → j ≠ 18 → S.R (rg j) = [])
    (dst : Fin T) (hdst : dst ∉ canonicalDescriptorScalarTargets rg) (output : List (Fin (A + 4)))
    (call : Pr P T Q A U) (price : ℕ)
    (hcall : ∀ u : HS T Q A U,
      let C : Stacks T A := { S with R := canonicalDescriptorScalarBank S.R rg L n r.val }
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ m ≤ price ∧
        Exec body call (mk u C) m (mk u' { C with R := Function.update C.R dst output })) :
    let W := (canonicalStageWidths (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)).coordinateBits
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ price + 96 * L * L + 676 * L + 922 + 10 * L * (4 * W + 11) + 246 * W ∧
      Exec body (canonicalDescriptorScalarScope rg call) (mk v S) m
        (mk v' { S with R := Function.update S.R dst output }) := by
  dsimp only
  let W := (canonicalStageWidths (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)).coordinateBits
  obtain ⟨v₁, m₁, hu₁, hm₁, hex₁⟩ := canonicalDescriptorScalarGenerate_exec body rg hrg L n hn hlarge hdivisor r
    v S hdimension hresidue hblank
  let C : Stacks T A := { S with R := canonicalDescriptorScalarBank S.R rg L n r.val }
  obtain ⟨v₂, m₂, hu₂, hm₂, hex₂⟩ := hcall v₁
  let D : Stacks T A := { C with R := Function.update C.R dst output }
  obtain ⟨v₃, hu₃, hex₃⟩ := metadataClean_exec body (canonicalDescriptorScalarTargets rg)
    (by simp [canonicalDescriptorScalarTargets, List.nodup_cons, hrg.eq_iff]) v₂ D
  have hcost : metadataCleanCost D.R (canonicalDescriptorScalarTargets rg) = 24 * L + 22 * W + 47 := by
    rw [metadataCleanCost_congr _ (R' := C.R) (by
      intro x hx
      apply Function.update_of_ne
      intro h
      exact hdst (h ▸ hx))]
    exact canonicalDescriptorScalarBank_cleanCost S.R rg hrg L n r.val
  have ht : ∀ x ∈ canonicalDescriptorScalarTargets rg, S.R x = [] := by
    intro x hx
    simp only [canonicalDescriptorScalarTargets, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> apply hblank <;> decide
  have hf : metadataCleared D.R (canonicalDescriptorScalarTargets rg) = Function.update S.R dst output := by
    rw [show D.R = Function.update C.R dst output from rfl, metadataCleared_update _ _ _ _ hdst]
    exact congrArg (fun R => Function.update R dst output) (canonicalDescriptorScalarBank_clean S.R rg L n r.val ht)
  rw [hcost, hf] at hex₃
  exact ⟨v₃, m₁ + (m₂ + (24 * L + 22 * W + 47)), hu₃.trans (hu₂.trans hu₁),
    by nlinarith only [hm₁, hm₂], Exec.seq hex₁ (Exec.seq hex₂ hex₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
