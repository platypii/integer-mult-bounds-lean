module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorGenerate
public import IntegerMultBounds.MathlibTM2.Routing.ClassifierGenerate

/-! The existing canonical descriptor/geometry bank supplies every classifier
source. Classifier setup therefore needs no additional numerical operands. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T A : ℕ}

def canonicalClassifierCore : Fin 108 → Fin 118 := Fin.castLE (by decide)
theorem canonicalClassifierCore_injective : Function.Injective canonicalClassifierCore := by decide +kernel

theorem canonicalClassifier_raw_fit (L n : ℕ) (hn : n < 2 ^ L)
    (r : Fin (canonicalRouterStride n)) (i : Fin 6) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    classifierScalarValue p i < 2 ^ classifierScalarInputWidth L (canonicalStageWidths p).coordinateBits i := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  have palette (j : Fin 11) := repairDescriptorScalarPalette_fit p r.isLt j
  have hd : p.n ≤ n := by
    have h := Nat.div_le_self (n - canonicalRouterStride n)
      (canonicalRouterStride n + 3 * canonicalRouterGap n)
    change (n - canonicalRouterStride n) / (canonicalRouterStride n + 3 * canonicalRouterGap n) ≤ n
    omega
  have ht : p.m ≤ n := by
    dsimp [p,routerProfileParameters,routerTail,routerTargetWidth]
    omega
  fin_cases i <;> first
    | exact palette 0 | exact palette 1 | exact hd.trans_lt hn
    | exact palette 3 | exact palette 2 | exact ht.trans_lt hn

theorem canonicalDescriptorGeneratedBank_low (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 108 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ)
    (i : Fin 108) (hi : i.val < 46) :
    canonicalDescriptorGeneratedBank R rg L n r (rg i) =
      canonicalDescriptorScalarBank R (rg ∘ canonicalDescriptorSharedCore) L n r (rg i) := by
  unfold canonicalDescriptorGeneratedBank descriptorScalarInstalledBank
  rw [binaryResizeBatchBank_keep]
  · exact descriptorSharedGeneratedBank_low _ rg hrg _ _ _ i (by omega)
  · intro hm
    obtain ⟨q,_,he⟩ := List.mem_map.mp hm
    have hv := congrArg (fun x : Fin 108 => x.val) (hrg he)
    change 46 + 5 * q.1.val + q.2.val = i.val at hv
    omega

theorem canonicalClassifier_sources (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 118 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hlarge : canonicalRouterStride n ≤ n) (r : Fin (canonicalRouterStride n))
    (hresidue : R (rg 18) = binSyms L r.val) (i : Fin 6) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    canonicalDescriptorGeneratedBank R (rg ∘ canonicalClassifierCore) L n r.val
      (rg (classifierScalarSource i)) =
        binSyms (classifierScalarInputWidth L (canonicalStageWidths p).coordinateBits i)
          (classifierScalarValue p i) := by
  dsimp only
  let core := rg ∘ canonicalClassifierCore
  let scalar := core ∘ canonicalDescriptorSharedCore
  have hc : Function.Injective core := hrg.comp canonicalClassifierCore_injective
  have hs : Function.Injective scalar := hc.comp canonicalDescriptorSharedCore_injective
  have keep (j : Fin 108) (hj : j.val < 46) := canonicalDescriptorGeneratedBank_low R core hc L n r.val j hj
  have palette (j : Fin 11) := canonicalDescriptorInstall_palette R
    (rg ∘ (Fin.castLE (by decide) : Fin 101 → Fin 118))
    (hrg.comp (by decide +kernel)) L n r.val j
  have controls (j : Fin 46) (hj : j = 11 ∨ j = 19) :
      canonicalDescriptorScalarBank R scalar L n r.val (scalar j) =
        canonicalProfileSetupBank R (scalar ∘ canonicalDescriptorGeometrySlot) L n r.val (scalar j) := by
    rcases hj with rfl | rfl <;>
      simp [canonicalDescriptorScalarBank,descriptorScalarResizedBank,descriptorScalarBank,
        binaryResizeBatchBank,descriptorScalarResizeSlot,descriptorScalarInputIndex,
        descriptorScalarCoreSlot,canonicalDescriptorScalarInputBank,canonicalDescriptorScalarSlot,hs.eq_iff]
  obtain ⟨_,_,hd,_,_⟩ := canonicalProfileSetup_parameters R
    (scalar ∘ canonicalDescriptorGeometrySlot) (hs.comp canonicalDescriptorGeometrySlot_injective)
    L n hlarge r hresidue
  have ht : canonicalProfileSetupBank R (scalar ∘ canonicalDescriptorGeometrySlot) L n r.val (scalar 19) =
      binSyms L (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val).m := by
    simp [canonicalProfileSetupBank,canonicalDescriptorWidthsBank,canonicalResidueGeometryBank,
      canonicalProfileWidthSlot,canonicalProfileGeometrySlot,canonicalDescriptorGeometrySlot,hs.eq_iff]
  fin_cases i
  · exact (keep 28 (by decide)).trans (palette 0)
  · exact (keep 29 (by decide)).trans (palette 1)
  · exact (keep 11 (by decide)).trans ((controls 11 (Or.inl rfl)).trans hd)
  · exact (keep 31 (by decide)).trans (palette 3)
  · exact (keep 30 (by decide)).trans (palette 2)
  · exact (keep 19 (by decide)).trans ((controls 19 (Or.inr rfl)).trans ht)

theorem canonicalClassifier_blank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 118 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ)
    (hblank : ∀ i : Fin 118, i ≠ 0 → i ≠ 9 → i ≠ 18 → R (rg i) = [])
    (i : Fin 118)
    (hi : i ∈ ([39,40,41,42,43,45,108,109,110,111,112,113,114,115,116,117] : List (Fin 118))) :
    canonicalDescriptorGeneratedBank R (rg ∘ canonicalClassifierCore) L n r (rg i) = [] := by
  let core := rg ∘ canonicalClassifierCore
  have hc : Function.Injective core := hrg.comp canonicalClassifierCore_injective
  have initial (i : Fin 118) (hi : 39 ≤ i.val) : R (rg i) = [] := by
    apply hblank <;> intro he <;> subst i <;> norm_num at hi
  have scratch (i : Fin 108) (hlo : 39 ≤ i.val) (hhi : i.val < 46) (h44 : i ≠ 44) :
      canonicalDescriptorGeneratedBank R core L n r (core i) = [] := by
    apply canonicalDescriptorGeneratedBank_scratch R core hc L n r
    · intro j hj
      exact initial _ hj
    · exact hlo
    · exact hhi
    · exact h44
  have outside (i : Fin 118) (hi : 108 ≤ i.val) :
      canonicalDescriptorGeneratedBank R core L n r (rg i) = R (rg i) := by
    apply canonicalDescriptorGeneratedBank_outside
    intro j he
    have hv := congrArg (fun x : Fin 118 => x.val) (hrg he)
    change j.val = i.val at hv
    have := j.isLt
    omega
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact scratch 39 (by decide) (by decide) (by decide)
  · exact scratch 40 (by decide) (by decide) (by decide)
  · exact scratch 41 (by decide) (by decide) (by decide)
  · exact scratch 42 (by decide) (by decide) (by decide)
  · exact scratch 43 (by decide) (by decide) (by decide)
  · exact scratch 45 (by decide) (by decide) (by decide)
  all_goals exact (outside _ (by decide)).trans (initial _ (by decide))

end IntegerMultBounds.MathlibTM2.Routing
