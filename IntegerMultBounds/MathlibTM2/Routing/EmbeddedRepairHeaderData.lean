module

public import IntegerMultBounds.MathlibTM2.Routing.EmbeddedRepairHeaders
public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorData

/-! Generated headers replace only the ten raw header words. The remaining
pending-descriptor data is transported unchanged over any embedded repair core. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {N A : ℕ} (e : Fin repairT → Fin N) (he : Function.Injective e)
  (p : Par) (X rb R B : ℕ)

theorem embeddedRepairHeaderPair_keep (tapes : Fin (sharedHeaderT N) → List (Fin (A + 4))) (i : Fin N)
    (hi : ∀ c k, i ≠ e (repairRoutingConfig (.header c k))) :
    repairHeaderPairBank p X rb R B (embeddedRepairHeaderBank e) tapes (sharedHeaderCore i) = tapes (sharedHeaderCore i) := by
  apply repairHeaderPairBank_keep
  intro c k
  rw [embeddedRepairHeaderBank_header]
  exact sharedHeaderCore_injective.ne (hi c k)

include he

theorem embeddedRepairHeaderPair_raw_keep (tapes : Fin (sharedHeaderT N) → List (Fin (A + 4))) (i : Fin repairT)
    (hi : ∀ c k, i ≠ repairRoutingConfig (.header c k)) :
    repairHeaderPairBank p X rb R B (embeddedRepairHeaderBank e) tapes (embeddedRepairHeaderRaw e i) =
      tapes (embeddedRepairHeaderRaw e i) :=
  embeddedRepairHeaderPair_keep e p X rb R B tapes (e i) (fun c k => he.ne (hi c k))

theorem embeddedRepairHeaderPair_raw_header (tapes : Fin (sharedHeaderT N) → List (Fin (A + 4))) (c : Fin 2) (k : Fin 5) :
    repairHeaderPairBank p X rb R B (embeddedRepairHeaderBank e) tapes
      (embeddedRepairHeaderRaw e (repairRoutingConfig (.header c k))) =
        (repairCanonicalHeaders p X rb R B c k).map bitSymbol := by
  exact repairHeaderPairBank_contents p X rb R B (embeddedRepairHeaderBank e)
    (embeddedRepairHeaderBank_injective e he) (embeddedRepairHeaderBank_cross e he) tapes c k

theorem RepairPendingDescriptorData.embeddedHeaders {wb wm wp wk : ℕ}
    {oldHeaders : Fin 2 → Fin 5 → List Bool} {tapes : Fin (sharedHeaderT N) → List (Fin (A + 4))}
    (data : RepairPendingDescriptorData p X rb wb wm wp wk R B oldHeaders (fun i => tapes (embeddedRepairHeaderRaw e i))) :
    RepairPendingDescriptorData p X rb wb wm wp wk R B (repairCanonicalHeaders p X rb R B)
      (fun i => repairHeaderPairBank p X rb R B (embeddedRepairHeaderBank e) tapes (embeddedRepairHeaderRaw e i)) := by
  have hkeep := embeddedRepairHeaderPair_raw_keep e he p X rb R B tapes
  constructor
  · intro f
    rw [hkeep]
    · exact data.widths f
    · intro c k; simp [repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  · rw [hkeep]
    · exact data.block
    · intro c k; simp [repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  · rw [hkeep]
    · exact data.records
    · intro c k; simp [repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  · exact data.block_lt
  · exact data.records_lt
  · intro c k
    exact embeddedRepairHeaderPair_raw_header e he p X rb R B tapes c k
  · rw [hkeep]
    · exact data.row
    · intro c k; simp [repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  · rw [hkeep]
    · exact data.keyMask
    · intro c k; simp [repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  · rw [hkeep]
    · exact data.badMask
    · intro c k; simp [repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  · rw [hkeep]
    · exact data.badPhase
    · intro c k; simp [repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  · rw [hkeep]
    · exact data.payload
    · intro c k; simp [repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  · exact data.payload_lt
  · rw [hkeep]
    · exact data.keyLength
    · intro c k; simp [repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  · exact data.keyLength_lt

end
end IntegerMultBounds.MathlibTM2.Routing
