module

public import IntegerMultBounds.NLogN.PhaseCellNaturalGroups

/-! Artificial halo endpoints clip the original ambient phase intervals.
No phase is restarted and no new periodic wrap is introduced at a halo edge. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open PhaseCellMatrix

def haloStart (s t band a phase : ℕ) : ℕ := max (naturalStart s t band phase) (a+band)
def haloStop (s t band b phase : ℕ) : ℕ := min (naturalStop s t band phase) (b-band)
def haloLength (s t band a b phase : ℕ) : ℕ := haloStop s t band b phase-haloStart s t band a phase

def haloInterior (s t band a b : ℕ) : Finset (ZMod s) :=
  (interiorSet s t band).filter (fun j => a+band ≤ j.val ∧ j.val < b-band)

def haloCellPhases (s t band a b : ℕ) : List ℕ :=
  (List.range (t-s+1)).filter (fun phase => decide (0 < haloLength s t band a b phase))

theorem mem_haloCellPhases (s t band a b phase : ℕ) :
    phase ∈ haloCellPhases s t band a b ↔ phase ≤ t-s ∧ 0 < haloLength s t band a b phase := by
  simp [haloCellPhases]

theorem haloStop_le (s t band b phase : ℕ) : haloStop s t band b phase ≤ s :=
  (min_le_left _ _).trans (naturalStop_le s t band phase)

theorem haloInterior_phase_iff {s t : ℕ} [NeZero s] (hst : s < t)
    (band a b phase : ℕ) (j : ZMod s) :
    j ∈ haloInterior s t band a b ∧ cell s t j = (phase : ℤ) ↔
      haloStart s t band a phase ≤ j.val ∧ j.val < haloStop s t band b phase := by
  have hs : 0 < s := NeZero.pos s
  have hbase : j ∈ interiorSet s t band ∧ cell s t j = (phase : ℤ) ↔
      naturalStart s t band phase ≤ j.val ∧ j.val < naturalStop s t band phase := by
    rw [mem_interiorSet,← mem_coordinateSet band (phase : ℤ) j,coordinateSet_eq_Ico hs hst,Finset.mem_Ico]
  simp only [haloInterior,Finset.mem_filter,haloStart,haloStop,max_le_iff,lt_min_iff]
  constructor
  · rintro ⟨⟨hI,ha,hb⟩,hphase⟩
    obtain ⟨hstart,hstop⟩ := hbase.mp ⟨hI,hphase⟩
    exact ⟨⟨hstart,ha⟩,hstop,hb⟩
  · rintro ⟨⟨hstart,ha⟩,hstop,hb⟩
    obtain ⟨hI,hphase⟩ := hbase.mpr ⟨hstart,hstop⟩
    exact ⟨⟨hI,ha,hb⟩,hphase⟩

theorem cell_eq_naturalPhase {s t : ℕ} [NeZero s] (hst : s < t) (j : ZMod s) :
    cell s t j = (naturalPhase s t j.val : ℤ) := by
  simpa only [PhaseCellMatrix.cell,phaseIndex_eq (NeZero.pos s)] using phaseIndex_nat hst.le j.val

/-- Every selected interior point lies in a generated positive clipped cell. -/
theorem haloCells_cover {s t : ℕ} [NeZero s] (hst : s < t) (band a b : ℕ)
    (j : ZMod s) (hj : j ∈ haloInterior s t band a b) :
    ∃ phase ∈ haloCellPhases s t band a b,
      haloStart s t band a phase ≤ j.val ∧ j.val < haloStop s t band b phase := by
  let phase := naturalPhase s t j.val
  have hphase : cell s t j = (phase : ℤ) := cell_eq_naturalPhase hst j
  have hinterval := (haloInterior_phase_iff hst band a b phase j).mp ⟨hj,hphase⟩
  refine ⟨phase,(mem_haloCellPhases s t band a b phase).mpr ⟨?_,?_⟩,hinterval⟩
  · exact naturalPhase_le_gap (NeZero.pos s) (ZMod.val_lt j).le
  · dsimp only [haloLength]
    omega

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
