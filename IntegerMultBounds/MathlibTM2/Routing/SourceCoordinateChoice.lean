module

public import IntegerMultBounds.MathlibTM2.Routing.ProfileSourceRecords
public import IntegerMultBounds.MathlibTM2.Routing.SourceRegionDispatch

/-! Piecewise numeric decoder specification, matching the typed Y-source
constructor and the canonical raw-record representation exactly. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

def sourceCoordinateChoice (q low high k : ℕ) (enabled : Bool) : GatedSelectedSourceChoice :=
  if q < low then ⟨0, q, false, false, enabled⟩
  else if q < high then ⟨(q - low) / k, (q - low) % k, true, false, enabled⟩
  else ⟨0, q - high, false, true, enabled⟩

theorem sourceCoordinateChoice_sourceOfY (p : Par) (hK : 0 < p.K) (X : ℕ)
    (q : Fin p.wy) (enabled : Bool) :
    sourceCoordinateChoice q.val p.ρ (p.ρ + p.n * p.K) p.K enabled =
      (sourceOfY p hK q : SlotSource p X).gatedChoice enabled := by
  unfold sourceCoordinateChoice sourceOfY
  split_ifs <;>
    simp [SlotSource.gatedChoice, SlotSource.index, SlotSource.offset, SlotSource.tag,
      sourceTagLo, sourceTagHi]

theorem sourceCoordinateChoice_profile (p : Par) (hK : 0 < p.K) (X : ℕ)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy) (c : Fin p.n) :
    sourceCoordinateChoice (profileSourceCoordinate p hK targets source c).val
      p.ρ (p.ρ + p.n * p.K) p.K (profileActive p hK targets c) =
      (profileSources (X := X) p hK targets source c).gatedChoice (profileActive p hK targets c) :=
  sourceCoordinateChoice_sourceOfY p hK X _ _

end IntegerMultBounds.MathlibTM2.Routing
