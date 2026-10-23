module

public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorPrograms

/-! Instantiate both grouped A compilers from the common live bank. The concrete
layout discharges every register condition and the bank supplies every operand. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {N J Q A : ℕ} {P U : Type}

theorem liveGroupedDescriptor_exec (body : P → Pr P (liveDescriptorT N J) Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (mode : Fin J → LiveDescriptorMode) (w : LiveDescriptorWidths)
    (j : Fin J) (out : Fin N) (k : Fin 2) (hmode : mode j = .grouped k) (hpositive : 0 < p.wy)
    (v : HS (liveDescriptorT N J) Q A U) (S : Stacks (liveDescriptorT N J) A)
    (h : LiveDescriptorReady p X hG hK active s mode w S.R) :
    ∃ (v' : HS (liveDescriptorT N J) Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (LiveDescriptorMode.grouped k).backendCost p X hG hK active s
        w.indexBits w.groupBits w.strideBits w.selectorBits w.widthBits ∧
      Exec body (liveGroupedDescriptorProgram j out) (mk v S) steps
        (mk v' { S with R := Function.update S.R (liveDescriptorCore out) (repairDescriptorWord p X hG hK active s (some (.A, k)) ++ S.R (liveDescriptorCore out)) }) := by
  obtain ⟨v', steps, hu, ht, he⟩ := repairADescriptor_exec body p X hG hK hGK active s k
    (liveBankProfile j) (liveBankProfile_injective j) (liveDescriptorAux .profileSaved) (liveBankProfile_saved j)
    liveBankCoordinate liveBankCoordinate_injective rfl
    (liveDescriptorAux .coordinateSaved) liveBankCoordinate_saved liveBankZero liveBankZero_injective
    liveBankRuns liveBankRuns_injective liveBankRun_input liveBankZero_block liveBankZero_coordinate liveBankRun_coordinate
    liveBankZero_input liveBankRun_coordinateInput (liveBankMask j) (liveBankMask_injective j)
    (liveDescriptorAux .archive) (liveDescriptorCore out) liveBankDense_archive
    (liveDescriptorCore_aux out (liveRunRole .dst)).symm (liveDescriptorCore_aux out .archive).symm
    (liveBankDense_mask j) (liveBankArchive_mask j) (fun r => liveDescriptorCore_aux out (liveMaskRole j r))
    (liveBankMask_input j) liveBankArchive_coordinateInput (liveDescriptorCore_aux out (liveCoordinateRole .src))
    w.indexBits w.groupBits w.strideBits w.selectorBits w.widthBits (h.bounds j).group_fits
    (by simpa only [hmode, LiveDescriptorMode.stride] using (h.bounds j).stride_fits)
    (h.bounds j).group_width
    (by simpa only [hmode, LiveDescriptorMode.key, repairCompactRows, selectiveTargetWidth, LiveDescriptorWidths.coordinateBits] using (h.bounds j).coordinate_fits)
    hpositive (by simpa only [hmode, LiveDescriptorMode.slots] using (h.bounds j).slots_fit)
    (by simpa only [hmode, LiveDescriptorMode.key, repairCompactSourceWidth] using (h.bounds j).source_fits)
    (h.bounds j).selector_fits v S
    (by rw [h.profile]; simp only [liveProfileRole, liveDescriptorData, hmode, LiveDescriptorMode.profileFrames])
    (h.profile_archive j)
    (by rw [h.profile]; rfl) (by rw [h.profile]; rfl)
    (by rw [h.profile]; simp only [liveProfileRole, liveDescriptorData, hmode, LiveDescriptorMode.stride])
    (by rw [h.profile]; simp only [liveProfileRole, liveDescriptorData, hmode, LiveDescriptorMode.base, LiveDescriptorWidths.coordinateBits])
    (by rw [h.profile]; simp only [liveProfileRole, liveDescriptorData, hmode, LiveDescriptorMode.key, repairCompactRows, selectiveTargetWidth, LiveDescriptorWidths.coordinateBits])
    (by rw [h.profile]; rfl) h.profile_saved (h.profile_blank j)
    (h.coordinate_blank .src (by decide) (by decide)) (h.coordinate_blank .archive (by decide) (by decide))
    h.coordinate_cursor h.coordinate_one h.coordinate_saved (h.coordinate_blank .dst (by decide) (by decide))
    (fun r _ _ hc ho _ => h.coordinate_blank r hc ho) h.zero_width (h.zero_blank .unary (by decide))
    (fun i => h.zero_blank (.scratch i) (by simp)) (h.runs_blank .archive) (h.runs_blank .block)
    (fun r _ _ _ _ => h.runs_blank r) (h.runs_blank .dst)
    (by simpa only [hmode, LiveDescriptorMode.key, repairCompactSourceWidth] using h.compiler j) h.compiler_archive
  exact ⟨v', steps, hu, ht, he⟩

end
end IntegerMultBounds.MathlibTM2.Routing
