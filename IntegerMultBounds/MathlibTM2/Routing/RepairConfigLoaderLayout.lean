module

public import IntegerMultBounds.MathlibTM2.Routing.RepairFramedConfig
public import IntegerMultBounds.MathlibTM2.Routing.RepairRawSourceLayout
public import IntegerMultBounds.MathlibTM2.Routing.RepairWidthFrame

/-! Concrete reusable configuration loading inside the existing repair bank.
Three unused key-field aliases hold input, scanner scratch and rewind archive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
noncomputable section
variable {A : ℕ}

def repairConfigInput : Fin repairT := repairRawSource 0
def repairConfigTmp : Fin repairT := repairRawSource 1
def repairConfigArchive : Fin repairT := repairRawSource 2

theorem repairConfigLoader_nodup : [repairConfigInput, repairConfigTmp, repairConfigArchive].Nodup := by
  simp [repairConfigInput, repairConfigTmp, repairConfigArchive, List.nodup_cons,
    repairRawSource_injective.eq_iff]

theorem repairConfigLoader_stream_nodup : [repairConfigInput, repairConfigArchive, repairHost.src].Nodup := by
  have h0 := repairRawSource_src 0
  have h2 := repairRawSource_src 2
  simp_all [repairConfigInput, repairConfigArchive, List.nodup_cons,
    repairRawSource_injective.eq_iff]

theorem repairConfigLoader_separate : ∀ d ∈ repairConfigDestinations,
    d ≠ repairConfigInput ∧ d ≠ repairConfigTmp ∧ d ≠ repairConfigArchive := by
  intro d hd
  obtain ⟨key, _, rfl⟩ := List.mem_map.mp hd
  exact ⟨(repairRawSource_setupSource 0 key).symm,
    (repairRawSource_setupSource 1 key).symm, (repairRawSource_setupSource 2 key).symm⟩

theorem repairBlank_setupSource (j : Fin repairT) (hj : RepairBlank j)
    (key : RepairSetupKey) : j ≠ repairSetupSource key := by
  cases key with
  | inr key => exact repairBlank_extraSource j hj key
  | inl key =>
    intro he
    subst j
    rcases hj with hh | he | ⟨r, _, _, _, hr⟩ | ⟨r, _, _, _, _, hr⟩
    · have hb : placedSelectiveHost.Blank (placedSelectiveConfig key) :=
        (SelectiveHost.Blank.map_iff placedSelectiveHost repairRoutingEmbed repairRoutingEmbed_injective _).mp hh
      rcases hb with hm | ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨o, r, hr, _, he⟩ | ⟨c, i, _, hi⟩
      · simp [placedSelectiveHost, placedSelectiveConfig] at hm
      · simp [placedSelectiveHost, placedSelectiveConfig] at hi
      · simp [placedSelectiveHost, placedSelectiveConfig] at hi
      · simp [placedSelectiveHost, placedSelectiveConfig, hr] at he
      · simp [placedSelectiveHost, placedSelectiveConfig] at hi
    · simp [repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole] at he
    · cases r <;> simp [repairKey, repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole] at hr
    · cases r <;> simp [repairBad, repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole] at hr

theorem repairConfigLoader_blank (delimiter : Fin (A + 4)) (rest : List (Fin (A + 4)))
    (words bank : Fin repairT → List (Fin (A + 4))) (j : Fin repairT) (hj : RepairBlank j) :
    delimitedBankLoaded repairConfigInput repairConfigTmp repairConfigArchive delimiter rest
      (repairConfigLoadJobs words) bank j = bank j := by
  have hraw (f : Fin 6) : j ≠ repairRawSource f := by
    intro he
    subst j
    exact repairRawSource_not_blank f hj
  apply delimitedBankLoaded_keep repairConfigInput repairConfigTmp repairConfigArchive j delimiter rest
    (repairConfigLoadJobs words) (hraw 0) (hraw 1) (hraw 2)
  intro job hjob
  obtain ⟨key, _, rfl⟩ := List.mem_map.mp hjob
  exact repairBlank_setupSource j hj key

theorem repairConfigLoader_targets (delimiter : Fin (A + 4)) (rest : List (Fin (A + 4)))
    (words bank : Fin repairT → List (Fin (A + 4))) (key : RepairSetupKey) :
    delimitedBankLoaded repairConfigInput repairConfigTmp repairConfigArchive delimiter rest
      (repairConfigLoadJobs words) bank (repairSetupTarget key) = bank (repairSetupTarget key) := by
  apply delimitedBankLoaded_keep
    repairConfigInput repairConfigTmp repairConfigArchive (repairSetupTarget key) delimiter rest
    (repairConfigLoadJobs words)
    (repairRawSource_setupTarget 0 key).symm (repairRawSource_setupTarget 1 key).symm
    (repairRawSource_setupTarget 2 key).symm
  intro job hj
  obtain ⟨other, _, rfl⟩ := List.mem_map.mp hj
  exact (repairSetup_sources other key).symm

theorem repairConfigLoader_stream (delimiter : Fin (A + 4)) (rest : List (Fin (A + 4)))
    (words bank : Fin repairT → List (Fin (A + 4))) :
    delimitedBankLoaded repairConfigInput repairConfigTmp repairConfigArchive delimiter rest
      (repairConfigLoadJobs words) bank repairHost.src = bank repairHost.src := by
  apply delimitedBankLoaded_keep
    repairConfigInput repairConfigTmp repairConfigArchive repairHost.src delimiter rest
    (repairConfigLoadJobs words)
    (repairRawSource_src 0).symm (repairRawSource_src 1).symm (repairRawSource_src 2).symm
  intro job hj
  obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
  exact (repairSetup_source_src key).symm

end
end IntegerMultBounds.MathlibTM2.Routing
