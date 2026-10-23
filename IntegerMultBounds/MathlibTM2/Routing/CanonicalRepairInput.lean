module

public import IntegerMultBounds.MathlibTM2.Routing.RepairClassifierData
public import IntegerMultBounds.MathlibTM2.Routing.RepairFramedConfig
public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorBank
public import IntegerMultBounds.MathlibTM2.Routing.RepairStreamFrame
public import IntegerMultBounds.MathlibTM2.Routing.RepairClassifierInputFrame

/-! Construct the initial exact-repair bank from scalar dimensions and records.
Descriptors, masks, row counters and headers start empty; the generated pipeline
must produce them. No readiness structure is supplied by the caller. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {A : ℕ}

def canonicalRepairPayload (p : Par) (X rb wb wm wp wk R B : ℕ) :
    RepairSetupKey → List (Fin (A + 4))
  | .inl (.field f) => binSyms (selectiveLen p X f) 0
  | .inl .block => binSyms wb (fieldsLen (selectiveKeyLen p X rb) + B)
  | .inl .records => binSyms wm (R * 2 ^ fieldsLen (selectiveLen p X))
  | .inr .payload => binSyms wp B
  | .inr .keyLength => binSyms wk (fieldsLen (selectiveKeyLen p X rb))
  | _ => []

def canonicalRepairInput (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records : List (Fin (A + 4))) : Fin repairT → List (Fin (A + 4)) :=
  Function.extend repairSetupSource (canonicalRepairPayload p X rb wb wm wp wk R B)
    (fun j => if j = repairHost.src then records else [])

theorem canonicalRepairInput_source (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records : List (Fin (A + 4))) (key : RepairSetupKey) :
    canonicalRepairInput p X rb wb wm wp wk R B records (repairSetupSource key) =
      canonicalRepairPayload p X rb wb wm wp wk R B key :=
  repairSetupSource_injective.extend_apply _ _ key

theorem canonicalRepairInput_off (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records : List (Fin (A + 4))) (j : Fin repairT)
    (hoff : ∀ key, repairSetupSource key ≠ j) :
    canonicalRepairInput p X rb wb wm wp wk R B records j =
      if j = repairHost.src then records else [] := by
  unfold canonicalRepairInput
  apply Function.extend_apply'
  rintro ⟨key, hk⟩
  exact hoff key hk

theorem canonicalRepairInput_stream (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records : List (Fin (A + 4))) :
    canonicalRepairInput p X rb wb wm wp wk R B records repairHost.src = records := by
  rw [canonicalRepairInput_off _ _ _ _ _ _ _ _ _ _ _ repairSetup_source_src]
  simp

theorem canonicalRepairInput_targets (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records : List (Fin (A + 4))) (key : RepairSetupKey) :
    canonicalRepairInput p X rb wb wm wp wk R B records (repairSetupTarget key) = [] := by
  rw [canonicalRepairInput_off _ _ _ _ _ _ _ _ _ _ _ (fun k => repairSetup_sources k key)]
  exact ite_eq_right (repairSetup_target_src key)

theorem repairSetupSource_not_blank (key : RepairSetupKey) (j : Fin repairT)
    (hj : RepairBlank j) : repairSetupSource key ≠ j := by
  intro he
  subst j
  rcases hj with hh | hh | ⟨r, hf, hd, hst, he⟩ | ⟨r, hf, hm, hp, hst, he⟩
  · rcases hh with hh | ⟨d, he⟩ | ⟨d, he⟩ | ⟨off, r, hf, hd, he⟩ | ⟨c, r, hr, he⟩
    · cases key with
      | inl key => cases key <;> simp [repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole,
          repairHost, SelectiveHost.map, placedSelectiveHost] at hh
      | inr key => cases key <;> simp [repairSetupSource, repairHost, SelectiveHost.map, placedSelectiveHost, repairRoutingRole] at hh
    all_goals
      cases key with
      | inl key => cases key <;> simp_all [repairSetupSource, repairRoutingConfig, placedSelectiveConfig,
          repairRoutingRole, repairHost, SelectiveHost.map, placedSelectiveHost]
      | inr key => cases key <;> simp_all [repairSetupSource, repairHost, SelectiveHost.map,
          placedSelectiveHost, repairRoutingRole]
  · cases key with
    | inl key => cases key <;> simp [repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole] at hh
    | inr key => cases key <;> simp [repairSetupSource] at hh
  all_goals
    cases key with
    | inl key => cases key <;> cases r <;> simp_all [repairSetupSource, repairRoutingConfig, placedSelectiveConfig,
        repairRoutingRole, repairKey, repairBad]
    | inr key => cases key <;> cases r <;> simp_all [repairSetupSource, repairKey, repairBad]

theorem canonicalRepairInput_scratch (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records : List (Fin (A + 4))) (j : Fin repairT) (hj : RepairBlank j) :
    canonicalRepairInput p X rb wb wm wp wk R B records j = [] := by
  rw [canonicalRepairInput_off _ _ _ _ _ _ _ _ _ _ _ (fun key => repairSetupSource_not_blank key j hj)]
  exact ite_eq_right (repairBlank_src j hj)

/-- Every scalar and empty-header premise follows from the constructed bank. -/
theorem canonicalRepairInput_data (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records : List (Fin (A + 4)))
    (hblock : fieldsLen (selectiveKeyLen p X rb) + B < 2 ^ wb)
    (hrecords : R * 2 ^ fieldsLen (selectiveLen p X) < 2 ^ wm)
    (hpayload : B < 2 ^ wp) (hkey : fieldsLen (selectiveKeyLen p X rb) < 2 ^ wk) :
    RepairPendingMaskData p X rb wb wm wp wk R B (fun _ _ => [])
      (canonicalRepairInput p X rb wb wm wp wk R B records) := by
  constructor
  · intro f
    change (canonicalRepairInput p X rb wb wm wp wk R B records (repairSetupSource (.inl (.field f)))).length = _
    rw [canonicalRepairInput_source]
    exact length_binSyms _ _
  · exact canonicalRepairInput_source p X rb wb wm wp wk R B records (.inl .block)
  · exact canonicalRepairInput_source p X rb wb wm wp wk R B records (.inl .records)
  · exact hblock
  · exact hrecords
  · intro c k
    exact canonicalRepairInput_source p X rb wb wm wp wk R B records (.inl (.header c k))
  · exact canonicalRepairInput_source p X rb wb wm wp wk R B records (.inr .payload)
  · exact hpayload
  · exact canonicalRepairInput_source p X rb wb wm wp wk R B records (.inr .keyLength)
  · exact hkey

theorem canonicalRepairInput_descriptors (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records : List (Fin (A + 4))) (key : RepairDescriptorKey) :
    canonicalRepairInput p X rb wb wm wp wk R B records (repairDescriptorSource key) = [] := by
  cases key with
  | none => exact canonicalRepairInput_source p X rb wb wm wp wk R B records (.inr .keyDescriptor)
  | some pair =>
    rcases pair with ⟨off, k⟩
    exact canonicalRepairInput_source p X rb wb wm wp wk R B records (.inl (.desc off k))

def canonicalProfileKey : Fin repairT := repairKey .st

def canonicalProfileRaw : Fin repairT := repairBad .st

def canonicalProfileActivity : Fin repairT := repairRoutingConfig (.field 4)

theorem canonicalProfile_registers : [canonicalProfileKey, canonicalProfileRaw, canonicalProfileActivity].Nodup := by
  simp [List.nodup_cons, canonicalProfileKey, canonicalProfileRaw, canonicalProfileActivity,
    repairKey, repairBad, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]

theorem canonicalProfileKey_source (key : RepairSetupKey) : repairSetupSource key ≠ canonicalProfileKey := by
  cases key with
  | inl key => cases key <;> simp [repairSetupSource, canonicalProfileKey, repairKey, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  | inr key => cases key <;> simp [repairSetupSource, canonicalProfileKey, repairKey]

theorem canonicalProfileRaw_source (key : RepairSetupKey) : repairSetupSource key ≠ canonicalProfileRaw := by
  cases key with
  | inl key => cases key <;> simp [repairSetupSource, canonicalProfileRaw, repairBad, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  | inr key => cases key <;> simp [repairSetupSource, canonicalProfileRaw, repairBad]

theorem canonicalRepairInput_profileKey (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records : List (Fin (A + 4))) :
    canonicalRepairInput p X rb wb wm wp wk R B records canonicalProfileKey = [] := by
  rw [canonicalRepairInput_off _ _ _ _ _ _ _ _ _ _ _ canonicalProfileKey_source]
  simp [canonicalProfileKey, repairKey, repairHost, SelectiveHost.map, placedSelectiveHost, repairRoutingRole]

theorem canonicalRepairInput_profileRaw (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records : List (Fin (A + 4))) :
    canonicalRepairInput p X rb wb wm wp wk R B records canonicalProfileRaw = [] := by
  rw [canonicalRepairInput_off _ _ _ _ _ _ _ _ _ _ _ canonicalProfileRaw_source]
  simp [canonicalProfileRaw, repairBad, repairHost, SelectiveHost.map, placedSelectiveHost, repairRoutingRole]

/-- The empty spectator-width word provides the third source-profile tape.
Its scalar width remains zero when the generated activity word is erased. -/
theorem canonicalRepairInput_profileActivity (p : Par) (rb wb wm wp wk R B : ℕ)
    (records : List (Fin (A + 4))) :
    canonicalRepairInput p 0 rb wb wm wp wk R B records canonicalProfileActivity = [] := by
  change canonicalRepairInput p 0 rb wb wm wp wk R B records (repairSetupSource (.inl (.field 4))) = []
  rw [canonicalRepairInput_source]
  simp [canonicalRepairPayload, selectiveLen, binSyms_eq]

theorem canonicalProfileKey_target (key : RepairSetupKey) : repairSetupTarget key ≠ canonicalProfileKey := by
  cases key with
  | inl key => cases key <;> simp [repairSetupTarget, SetupKey.target, repairHost, SelectiveHost.map,
      placedSelectiveHost, repairRoutingRole, canonicalProfileKey, repairKey]
  | inr key => cases key <;> simp [repairSetupTarget, repairExtraTarget, canonicalProfileKey, repairKey, repairBad]

theorem canonicalProfileKey_not_blank : ¬RepairBlank canonicalProfileKey := by
  intro hj
  rcases hj with hh | hh | ⟨r, hf, hd, hst, he⟩ | ⟨r, hf, hm, hp, hst, he⟩
  · rcases hh with hh | ⟨d, he⟩ | ⟨d, he⟩ | ⟨off, r, hf, hd, he⟩ | ⟨c, r, hr, he⟩
    · simp [canonicalProfileKey, repairKey, repairHost, SelectiveHost.map, placedSelectiveHost, repairRoutingRole] at hh
    all_goals simp_all [canonicalProfileKey, repairKey, repairHost, SelectiveHost.map, placedSelectiveHost, repairRoutingRole]
  · simp [canonicalProfileKey, repairKey] at hh
  · have hr : r = .st := repairKey_injective he
    exact hst hr
  · cases r <;> simp_all [canonicalProfileKey, repairKey, repairBad]

def canonicalProfileCoreBank (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records coordinates : List (Fin (A + 4))) : Fin repairT → List (Fin (A + 4)) :=
  Function.update (canonicalRepairInput p X rb wb wm wp wk R B records) canonicalProfileKey coordinates

theorem canonicalProfileCoreBank_data (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records coordinates : List (Fin (A + 4)))
    (hblock : fieldsLen (selectiveKeyLen p X rb) + B < 2 ^ wb)
    (hrecords : R * 2 ^ fieldsLen (selectiveLen p X) < 2 ^ wm)
    (hpayload : B < 2 ^ wp) (hkey : fieldsLen (selectiveKeyLen p X rb) < 2 ^ wk) :
    RepairPendingMaskData p X rb wb wm wp wk R B (fun _ _ => [])
      (canonicalProfileCoreBank p X rb wb wm wp wk R B records coordinates) := by
  apply (canonicalRepairInput_data p X rb wb wm wp wk R B records hblock hrecords hpayload hkey).congr p X rb
  intro key
  exact Function.update_of_ne (canonicalProfileKey_source key) _ _

theorem canonicalProfileCoreBank_targets (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records coordinates : List (Fin (A + 4))) (key : RepairSetupKey) :
    canonicalProfileCoreBank p X rb wb wm wp wk R B records coordinates (repairSetupTarget key) = [] := by
  rw [canonicalProfileCoreBank, Function.update_of_ne (canonicalProfileKey_target key)]
  exact canonicalRepairInput_targets p X rb wb wm wp wk R B records key

theorem canonicalProfileCoreBank_scratch (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records coordinates : List (Fin (A + 4))) (j : Fin repairT) (hj : RepairBlank j) :
    canonicalProfileCoreBank p X rb wb wm wp wk R B records coordinates j = [] := by
  have hne : j ≠ canonicalProfileKey := by intro he; subst j; exact canonicalProfileKey_not_blank hj
  rw [canonicalProfileCoreBank, Function.update_of_ne hne]
  exact canonicalRepairInput_scratch p X rb wb wm wp wk R B records j hj

theorem canonicalProfileCoreBank_key (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records coordinates : List (Fin (A + 4))) :
    canonicalProfileCoreBank p X rb wb wm wp wk R B records coordinates canonicalProfileKey = coordinates :=
  Function.update_self _ _ _

theorem canonicalProfileCoreBank_raw (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records coordinates : List (Fin (A + 4))) :
    canonicalProfileCoreBank p X rb wb wm wp wk R B records coordinates canonicalProfileRaw = [] := by
  have hne : canonicalProfileRaw ≠ canonicalProfileKey := by simp [canonicalProfileRaw, canonicalProfileKey, repairKey, repairBad]
  rw [canonicalProfileCoreBank, Function.update_of_ne hne]
  exact canonicalRepairInput_profileRaw p X rb wb wm wp wk R B records

theorem canonicalProfileCoreBank_activity (p : Par) (rb wb wm wp wk R B : ℕ)
    (records coordinates : List (Fin (A + 4))) :
    canonicalProfileCoreBank p 0 rb wb wm wp wk R B records coordinates canonicalProfileActivity = [] := by
  have hne : canonicalProfileActivity ≠ canonicalProfileKey := canonicalProfileKey_source (.inl (.field 4))
  rw [canonicalProfileCoreBank, Function.update_of_ne hne]
  exact canonicalRepairInput_profileActivity p rb wb wm wp wk R B records

theorem canonicalProfileCoreBank_stream (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records coordinates : List (Fin (A + 4))) :
    canonicalProfileCoreBank p X rb wb wm wp wk R B records coordinates repairHost.src = records := by
  have hne : repairHost.src ≠ canonicalProfileKey := by
    simp [canonicalProfileKey, repairKey, repairHost, SelectiveHost.map, placedSelectiveHost, repairRoutingRole]
  rw [canonicalProfileCoreBank, Function.update_of_ne hne]
  exact canonicalRepairInput_stream p X rb wb wm wp wk R B records

theorem canonicalProfileCoreBank_descriptors (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records coordinates : List (Fin (A + 4))) (key : RepairDescriptorKey) :
    canonicalProfileCoreBank p X rb wb wm wp wk R B records coordinates (repairDescriptorSource key) = [] := by
  have hne : repairDescriptorSource key ≠ canonicalProfileKey := by
    cases key with
    | none => exact canonicalProfileKey_source (.inr .keyDescriptor)
    | some pair => exact canonicalProfileKey_source (.inl (.desc pair.1 pair.2))
  rw [canonicalProfileCoreBank, Function.update_of_ne hne]
  exact canonicalRepairInput_descriptors p X rb wb wm wp wk R B records key

theorem canonicalProfileCoreBank_source (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records coordinates : List (Fin (A + 4))) (key : RepairSetupKey) :
    canonicalProfileCoreBank p X rb wb wm wp wk R B records coordinates (repairSetupSource key) =
      canonicalRepairPayload p X rb wb wm wp wk R B key := by
  rw [canonicalProfileCoreBank, Function.update_of_ne (canonicalProfileKey_source key), canonicalRepairInput_source]

end
end IntegerMultBounds.MathlibTM2.Routing
