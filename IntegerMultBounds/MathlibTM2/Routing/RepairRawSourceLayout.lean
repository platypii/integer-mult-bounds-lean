module

public import IntegerMultBounds.MathlibTM2.Routing.RepairSetupBlank

/-! Unused physical key-field aliases provide raw-input storage. Actual key
fields use the shared field bank, so these aliases are outside repair scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
noncomputable section

def repairRawSource (f : Fin 6) : Fin repairT := repairReg (.key (.fld f))

theorem repairRawSource_injective : Function.Injective repairRawSource := by
  intro i j h
  simpa [repairRawSource] using h

theorem repairRawSource_key (f : Fin 6) (r : PatternReg 6) : repairRawSource f ≠ repairKey r := by
  cases r <;> simp [repairRawSource, repairKey]

theorem repairRawSource_bad (f : Fin 6) (r : BadReg) : repairRawSource f ≠ repairBad r := by
  cases r <;> simp [repairRawSource, repairBad]

theorem repairRawSource_routing (f : Fin 6) (k : Fin selectiveT) :
    repairRawSource f ≠ repairRoutingEmbed k := by
  obtain ⟨r, rfl⟩ := (Fintype.equivFin SelectiveReg).surjective k
  change repairRawSource f ≠ repairRoutingEmbed (selectiveReg r)
  rw [repairRoutingEmbed_reg]
  cases r <;> simp [repairRawSource, repairRoutingRole]

theorem repairRawSource_not_blank (f : Fin 6) : ¬ RepairBlank (repairRawSource f) := by
  intro hj
  rcases hj with hj | he | ⟨r, _, _, _, he⟩ | ⟨r, _, _, _, _, he⟩
  · rcases hj with hm | ⟨d, he⟩ | ⟨d, he⟩ | ⟨off, r, _, _, he⟩ | ⟨c, r, _, he⟩
    · simp only [repairHost, SelectiveHost.map, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with he | he | he <;> exact repairRawSource_routing f _ he
    · exact repairRawSource_routing f _ he.symm
    · exact repairRawSource_routing f _ he.symm
    · exact repairRawSource_routing f _ he.symm
    · exact repairRawSource_routing f _ he.symm
  · simp [repairRawSource] at he
  · exact repairRawSource_key f r he.symm
  · exact repairRawSource_bad f r he.symm

theorem repairRawSource_setupSource (f : Fin 6) (key : RepairSetupKey) :
    repairRawSource f ≠ repairSetupSource key := by
  cases key with
  | inl key => exact repairRawSource_routing f _
  | inr key => simp [repairRawSource, repairSetupSource]

theorem repairRawSource_setupTarget (f : Fin 6) (key : RepairSetupKey) :
    repairRawSource f ≠ repairSetupTarget key := by
  cases key with
  | inl key => rw [repairSetupTarget_inl]; exact repairRawSource_routing f _
  | inr key => cases key <;> simp [repairRawSource, repairSetupTarget, repairExtraTarget, repairKey, repairBad]

theorem repairRawSource_header (f : Fin 6) (c : Fin 2) (k : Fin 5) :
    repairRawSource f ≠ repairRoutingConfig (.header c k) := repairRawSource_routing f _

theorem repairRawSource_src (f : Fin 6) : repairRawSource f ≠ repairHost.src :=
  repairRawSource_routing f _

/-- Installing raw input in these slots preserves every required blank register. -/
theorem repairRawSource_update_blank {A : ℕ} (R : Fin repairT → List (Fin (A + 4)))
    (f : Fin 6) (word : List (Fin (A + 4)))
    (j : Fin repairT) (hj : RepairBlank j) :
    Function.update R (repairRawSource f) word j = R j := by
  apply Function.update_of_ne
  intro he
  subst j
  exact repairRawSource_not_blank f hj

end
end IntegerMultBounds.MathlibTM2.Routing
