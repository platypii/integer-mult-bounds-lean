module

public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankReady
public import IntegerMultBounds.MathlibTM2.Routing.RepairInputFrame

/-! The fixed raw R2 configuration bank as framed loader jobs. Loading derives
actual repair readiness by equality on its source registers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {A : ℕ}

theorem repairSetupSource_injective : Function.Injective repairSetupSource := by
  intro key other he
  cases key <;> cases other <;>
    simp_all [repairSetupSource, repairRoutingConfig, placedSelectiveConfig,
      repairRoutingEmbed_reg, repairRoutingRole]

def repairConfigDestinations : List (Fin repairT) := repairSetupKeys.map repairSetupSource

def repairConfigLoadJobs (words : Fin repairT → List (Fin (A + 4))) :
    List (Fin repairT × List (Fin (A + 4))) :=
  repairSetupKeys.map fun key => (repairSetupSource key, words (repairSetupSource key))

theorem repairConfigLoadJobs_destinations (words : Fin repairT → List (Fin (A + 4))) :
    (repairConfigLoadJobs words).map Prod.fst = repairConfigDestinations := by
  simp only [repairConfigLoadJobs, repairConfigDestinations, List.map_map, Function.comp_def]

theorem repairConfigDestinations_nodup : repairConfigDestinations.Nodup :=
  repairSetupKeys_nodup.map repairSetupSource_injective

theorem repairConfigDestinations_stream : repairHost.src ∉ repairConfigDestinations := by
  intro hm
  obtain ⟨key, _, he⟩ := List.mem_map.mp hm
  exact repairSetup_source_src key he

theorem repairConfigLoaded_source (src tmp saved : Fin repairT)
    (delimiter : Fin (A + 4)) (rest : List (Fin (A + 4)))
    (words bank : Fin repairT → List (Fin (A + 4)))
    (hsrc : ∀ key, repairSetupSource key ≠ src)
    (htmp : ∀ key, repairSetupSource key ≠ tmp)
    (hsaved : ∀ key, repairSetupSource key ≠ saved) (key : RepairSetupKey) :
    delimitedBankLoaded src tmp saved delimiter rest (repairConfigLoadJobs words) bank
      (repairSetupSource key) = words (repairSetupSource key) := by
  apply delimitedBankLoaded_at src tmp saved delimiter rest (repairConfigLoadJobs words)
    (by rw [repairConfigLoadJobs_destinations]; exact repairConfigDestinations_nodup)
    ?_ (repairSetupSource key, words (repairSetupSource key)) ?_ bank
  · intro j hj
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
    exact ⟨hsrc key, htmp key, hsaved key⟩
  · exact List.mem_map.mpr ⟨key, repairSetupKeys_mem key, rfl⟩

theorem RepairSetupData.framedLoaded (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    {wb wm wp wk R B : ℕ} {headers : Fin 2 → Fin 5 → List Bool}
    {words : Fin repairT → List (Fin (A + 4))}
    (data : RepairSetupData p X rb hG hK active s wb wm wp wk R B headers words)
    (src tmp saved : Fin repairT) (delimiter : Fin (A + 4)) (rest : List (Fin (A + 4)))
    (bank : Fin repairT → List (Fin (A + 4)))
    (hsrc : ∀ key, repairSetupSource key ≠ src)
    (htmp : ∀ key, repairSetupSource key ≠ tmp)
    (hsaved : ∀ key, repairSetupSource key ≠ saved) :
    RepairSetupData p X rb hG hK active s wb wm wp wk R B headers
      (delimitedBankLoaded src tmp saved delimiter rest (repairConfigLoadJobs words) bank) := by
  apply data.congr p X rb hG hK active s
  exact repairConfigLoaded_source src tmp saved delimiter rest words bank hsrc htmp hsaved

end
end IntegerMultBounds.MathlibTM2.Routing
