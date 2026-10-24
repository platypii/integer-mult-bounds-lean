module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorGenerate

/-! Erase per-mode fields, shared operands, then scalar geometry. Each stage
restores the preceding bank and preserves the serialized output frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}

def canonicalDescriptorFieldTargets (rg : Fin 108 → Fin T) : List (Fin T) :=
  descriptorScalarJobs.map (fun q => rg (canonicalDescriptorFieldCore (descriptorScalarDestination q)))

def canonicalDescriptorCleanProgram (rg : Fin 108 → Fin T) : Pr P T Q A U :=
  .seq (metadataClean (canonicalDescriptorFieldTargets rg))
    (.seq (metadataClean (descriptorSharedTargets rg))
      (metadataClean (canonicalDescriptorScalarTargets (rg ∘ canonicalDescriptorSharedCore))))

theorem canonicalDescriptorClean_exec (body : P → Pr P T Q A U)
    (rg : Fin 108 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i : Fin 108, i ≠ 0 → i ≠ 9 → i ≠ 18 → S.R (rg i) = [])
    (dst : Fin T) (hoff : ∀ i, rg i ≠ dst) (output : List (Fin (A + 4))) :
    let W := (canonicalStageWidths (routerProfileParameters n (canonicalRouterStride n)
      (canonicalRouterGap n) r)).coordinateBits
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 24 * L + 146 * W + 173 ∧
      Exec body (canonicalDescriptorCleanProgram rg)
        (mk v { S with R := Function.update (canonicalDescriptorGeneratedBank S.R rg L n r) dst output }) m
        (mk v' { S with R := Function.update S.R dst output }) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
  let w := canonicalStageWidths p
  let W := w.coordinateBits
  let core := rg ∘ canonicalDescriptorSharedCore
  let fields := rg ∘ canonicalDescriptorFieldCore
  let B := canonicalDescriptorScalarBank S.R core L n r
  let C := canonicalDescriptorSharedGeneratedBank S.R rg L n r
  let D := canonicalDescriptorGeneratedBank S.R rg L n r
  have hc : Function.Injective core := hrg.comp canonicalDescriptorSharedCore_injective
  have hf : Function.Injective fields := hrg.comp canonicalDescriptorFieldCore_injective
  have blank : ∀ i : Fin 108, 39 ≤ i.val → S.R (rg i) = [] := by
    intro i hi
    apply hblank <;> intro he <;> subst i <;> norm_num at hi
  have cb (i : Fin 108) (hi : 39 ≤ i.val) (h44 : i ≠ 44) : B (rg i) = [] :=
    canonicalDescriptorShared_blank S.R rg hrg L n r blank i hi h44
  have fieldblank (q : Fin 11 × Fin 5) : C (fields (descriptorScalarDestination q)) = [] := by
    rw [show C (fields (descriptorScalarDestination q)) = B (fields (descriptorScalarDestination q)) from
      descriptorSharedGeneratedBank_low B rg hrg W p w _ (descriptorScalarDestination q).isLt]
    apply cb
    · change 39 ≤ 46 + 5 * q.1.val + q.2.val
      omega
    · intro h
      have hv := congrArg (fun x : Fin 108 => x.val) h
      change 46 + 5 * q.1.val + q.2.val = 44 at hv
      omega
  have sharedblank : ∀ k ∈ descriptorSharedTargets rg, B k = [] := by
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact cb 101 (by decide) (by decide)
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hk
      apply cb
      · change 39 ≤ 102 + i.val
        omega
      · intro h
        have hv := congrArg (fun x : Fin 108 => x.val) h
        change 102 + i.val = 44 at hv
        omega
  have scalarblank : ∀ k ∈ canonicalDescriptorScalarTargets core, S.R k = [] := by
    intro k hk
    simp only [canonicalDescriptorScalarTargets,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> apply hblank <;> decide
  have hfield : (canonicalDescriptorFieldTargets rg).Nodup :=
    descriptorScalarJobs_nodup.map (hf.comp descriptorScalarDestination_injective)
  have hshared : (descriptorSharedTargets rg).Nodup := by
    simp [descriptorSharedTargets,descriptorSharedJobs,descriptorSharedDestination,hrg.eq_iff]
  have hscalar : (canonicalDescriptorScalarTargets core).Nodup := by
    simp [canonicalDescriptorScalarTargets,hc.eq_iff]
  have offField : dst ∉ canonicalDescriptorFieldTargets rg := by
    intro hm
    obtain ⟨q,_,he⟩ := List.mem_map.mp hm
    exact hoff _ he
  have offShared : dst ∉ descriptorSharedTargets rg := by
    intro hm
    rcases List.mem_cons.mp hm with he | hm
    · exact hoff 101 he.symm
    · obtain ⟨i,_,he⟩ := List.mem_map.mp hm
      exact hoff _ he
  have offScalar : dst ∉ canonicalDescriptorScalarTargets core := by
    have hn (i : Fin 108) : dst ≠ rg i := (hoff i).symm
    simp [canonicalDescriptorScalarTargets,core,Function.comp_apply,hn]
  have restoreField : metadataCleared D (canonicalDescriptorFieldTargets rg) = C :=
    binaryResizeBatchBank_clean C (fun q => fields ∘ descriptorScalarInstallSlot q)
      (fun q => repairDescriptorScalarWidth w q.2)
      (fun q => repairDescriptorScalarPalette p (repairDescriptorScalarSlot q.1 q.2))
      descriptorScalarJobs (fun q _ => fieldblank q)
  have restoreShared : metadataCleared C (descriptorSharedTargets rg) = B :=
    descriptorSharedGeneratedBank_clean B rg W p w sharedblank
  have restoreScalar : metadataCleared B (canonicalDescriptorScalarTargets core) = S.R :=
    canonicalDescriptorScalarBank_clean S.R core L n r scalarblank
  obtain ⟨v₁,hu₁,he₁⟩ := metadataClean_framed_exec body _ hfield D C restoreField dst offField output v S
  obtain ⟨v₂,hu₂,he₂⟩ := metadataClean_framed_exec body _ hshared C B restoreShared dst offShared output v₁ S
  obtain ⟨v₃,hu₃,he₃⟩ := metadataClean_framed_exec body _ hscalar B S.R restoreScalar dst offScalar output v₂ S
  have costField : metadataCleanCost D (canonicalDescriptorFieldTargets rg) ≤ 55 * (2 * W + 2) + 1 := by
    have hx := binaryResizeBatchBank_cleanCost_le C (fun q => fields ∘ descriptorScalarInstallSlot q)
      (fun q => repairDescriptorScalarWidth w q.2)
      (fun q => repairDescriptorScalarPalette p (repairDescriptorScalarSlot q.1 q.2))
      descriptorScalarJobs hfield W (fun q _ => canonicalDescriptorInstall_width_le p q.2)
    have hl : descriptorScalarJobs.length = 55 := by decide +kernel
    simpa [hl,D,C,p,w,canonicalDescriptorGeneratedBank,descriptorScalarInstalledBank,
      fields,canonicalDescriptorFieldTargets,descriptorScalarInstallSlot] using hx
  have costShared : metadataCleanCost C (descriptorSharedTargets rg) ≤ 7 * (2 * W + 2) + 1 :=
    descriptorSharedGeneratedBank_cleanCost_le B rg hrg W p w W le_rfl (canonicalDescriptorShared_width_le p)
  have costScalar := canonicalDescriptorScalarBank_cleanCost S.R core hc L n r
  refine ⟨v₃,_,hu₃.trans (hu₂.trans hu₁),?_,Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  nlinarith only [costField,costShared,costScalar]

end IntegerMultBounds.MathlibTM2.Routing
