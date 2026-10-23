module

public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorPrograms

/-! Instantiate the affine compiler from one common live bank. All input words,
workspace readiness and separation facts come from the concrete layout. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {N J Q A : ℕ} {P U : Type}

theorem liveAffineDescriptor_exec (body : P → Pr P (liveDescriptorT N J) Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (mode : Fin J → LiveDescriptorMode) (w : LiveDescriptorWidths)
    (j : Fin J) (out : Fin N) (key : RepairDescriptorKey) (hkey : ∀ k, key ≠ some (.A, k))
    (hmode : mode j = .affine key hkey) (hpositive : 0 < repairCompactRows p key)
    (v : HS (liveDescriptorT N J) Q A U) (S : Stacks (liveDescriptorT N J) A)
    (h : LiveDescriptorReady p X hG hK active s mode w S.R) :
    ∃ (v' : HS (liveDescriptorT N J) Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (LiveDescriptorMode.affine key hkey).backendCost p X hG hK active s
        w.indexBits w.groupBits w.strideBits w.selectorBits w.widthBits ∧
      Exec body (liveAffineDescriptorProgram j out) (mk v S) steps
        (mk v' { S with R := Function.update S.R (liveDescriptorCore out) (repairDescriptorWord p X hG hK active s key ++ S.R (liveDescriptorCore out)) }) := by
  obtain ⟨v', steps, hu, ht, he⟩ := repairAffineDescriptor_exec body p X hG hK active s key hkey
    (sharedAffineProfile (liveBankProfile j)) (sharedAffineProfile_injective _ (liveBankProfile_injective j))
    (liveDescriptorAux .profileSaved) (fun r => liveBankProfile_saved j (affineGroupedRole r))
    liveBankCoordinate liveBankCoordinate_injective rfl
    (liveDescriptorAux .coordinateSaved) liveBankCoordinate_saved liveBankZero liveBankZero_injective
    liveBankRuns liveBankRuns_injective liveBankRun_input liveBankZero_block liveBankZero_coordinate liveBankRun_coordinate
    liveBankZero_input liveBankRun_coordinateInput (liveBankMask j) (liveBankMask_injective j)
    (liveDescriptorAux .archive) (liveDescriptorCore out) liveBankDense_archive
    (liveDescriptorCore_aux out (liveRunRole .dst)).symm (liveDescriptorCore_aux out .archive).symm
    (liveBankDense_mask j) (liveBankArchive_mask j) (fun r => liveDescriptorCore_aux out (liveMaskRole j r))
    (liveBankMask_input j) liveBankArchive_coordinateInput (liveDescriptorCore_aux out (liveCoordinateRole .src))
    w.indexBits w.strideBits w.selectorBits w.widthBits
    (by simpa only [hmode, LiveDescriptorMode.stride] using (h.bounds j).stride_fits)
    (by simpa only [hmode, LiveDescriptorMode.key, LiveDescriptorWidths.coordinateBits] using (h.bounds j).coordinate_fits)
    hpositive (by simpa only [hmode, LiveDescriptorMode.slots] using (h.bounds j).slots_fit)
    (by simpa only [hmode, LiveDescriptorMode.key] using (h.bounds j).source_fits) (h.bounds j).selector_fits v S
    (by
      change S.R (liveBankProfile j .src) = _
      rw [h.profile]
      simp only [liveProfileRole, liveDescriptorData, hmode, LiveDescriptorMode.profileFrames])
    (h.profile_archive j)
    (by change S.R (liveBankProfile j (.coordinate (.arithmetic .index))) = _; rw [h.profile]; rfl)
    (by
      change S.R (liveBankProfile j (.coordinate (.arithmetic .stride))) = _
      rw [h.profile]
      simp only [liveProfileRole, liveDescriptorData, hmode, LiveDescriptorMode.stride])
    (by
      change S.R (liveBankProfile j (.coordinate (.arithmetic .base))) = _
      rw [h.profile]
      simp only [liveProfileRole, liveDescriptorData, hmode, LiveDescriptorMode.base, LiveDescriptorWidths.coordinateBits])
    (by
      change S.R (liveBankProfile j (.coordinate .last)) = _
      rw [h.profile]
      simp only [liveProfileRole, liveDescriptorData, hmode, LiveDescriptorMode.key, LiveDescriptorWidths.coordinateBits])
    (by change S.R (liveBankProfile j (.coordinate .one)) = _; rw [h.profile]; rfl)
    h.profile_saved (fun r hs ha hi hk ho hl h1 hd => h.affine_blank j r hs ha hi hk ho hl h1 hd)
    (h.coordinate_blank .src (by decide) (by decide)) (h.coordinate_blank .archive (by decide) (by decide))
    h.coordinate_cursor h.coordinate_one h.coordinate_saved (h.coordinate_blank .dst (by decide) (by decide))
    (fun r _ _ hc ho _ => h.coordinate_blank r hc ho) h.zero_width (h.zero_blank .unary (by decide))
    (fun i => h.zero_blank (.scratch i) (by simp)) (h.runs_blank .archive) (h.runs_blank .block)
    (fun r _ _ _ _ => h.runs_blank r) (h.runs_blank .dst)
    (by simpa only [hmode, LiveDescriptorMode.key] using h.compiler j) h.compiler_archive
  exact ⟨v', steps, hu, ht, he⟩

end
end IntegerMultBounds.MathlibTM2.Routing
