module

public import IntegerMultBounds.NLogN.PhaseCellHaloGroups
public import IntegerMultBounds.ListFilterInterval

/-! Only phases intersecting the halo need scanning. Restricting the existing
phase list preserves the exact generated group and its ambient order. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open PhaseCellMatrix

def haloPhaseStart (s t a : ℕ) : ℕ := naturalPhase s t a

def haloPhaseCount (s t a b : ℕ) : ℕ := naturalPhase s t b+1-haloPhaseStart s t a

theorem haloCellPhase_bounds {s t : ℕ} [NeZero s] (hst : s < t) (band a b phase : ℕ)
    (hpos : 0 < haloLength s t band a b phase) :
    naturalPhase s t a ≤ phase ∧ phase ≤ naturalPhase s t b := by
  let start := haloStart s t band a phase
  have hstop := haloStop_le s t band b phase
  have hlt : start < haloStop s t band b phase := by change 0 < haloStop s t band b phase-start at hpos; omega
  have hstart : start < s := by omega
  have ha : a ≤ start := by dsimp [start,haloStart]; omega
  have hb : start ≤ b := by
    have hh : haloStop s t band b phase ≤ b := by unfold haloStop; omega
    omega
  have hv : (start : ZMod s).val = start := ZMod.val_cast_of_lt hstart
  have hm := (haloInterior_phase_iff hst band a b phase (start : ZMod s)).mpr (by rw [hv]; exact ⟨le_rfl,hlt⟩)
  have hc := cell_eq_naturalPhase hst (start : ZMod s)
  rw [hv] at hc
  have he : phase = naturalPhase s t start := Int.natCast_inj.mp (hm.2.symm.trans hc)
  rw [he]
  exact ⟨naturalPhase_monotone s t ha,naturalPhase_monotone s t hb⟩

theorem haloPhaseRange_end {s t : ℕ} (hs : 0 < s) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ s) :
    haloPhaseStart s t a+haloPhaseCount s t a b = naturalPhase s t b+1 ∧
      naturalPhase s t b+1 ≤ t-s+1 := by
  have hm := naturalPhase_monotone s t hab
  have hn := naturalPhase_le_gap (t := t) hs hb
  dsimp only [haloPhaseStart,haloPhaseCount] at *
  omega

/-- The local phase range selects the same positive length class as the full scan. -/
theorem haloLengthGroup_local {s t : ℕ} [NeZero s] (hst : s < t)
    (band a b L : ℕ) (hab : a ≤ b) (hb : b ≤ s) :
    (((List.range (haloPhaseCount s t a b)).map (haloPhaseStart s t a+·)).filter
      (fun phase => decide (0 < L ∧ haloLength s t band a b phase = L))) = haloLengthGroup s t band a b L := by
  let start := haloPhaseStart s t a
  let count := haloPhaseCount s t a b
  have hend := haloPhaseRange_end (t := t) (NeZero.pos s) a b hab hb
  have hfit : start+count ≤ t-s+1 := by omega
  have hslice : ((List.range (t-s+1)).drop start).take count = (List.range count).map (start+·) := by
    apply List.ext_getElem (by simp only [List.length_take,List.length_drop,List.length_range,List.length_map]; omega)
    intro j hj hk
    simp only [List.getElem_take,List.getElem_drop,List.getElem_range,List.getElem_map]
  have hh := List.filter_take_drop_of_support (List.range (t-s+1))
    (fun phase => decide (0 < L ∧ haloLength s t band a b phase = L)) start count (by
      intro phase hphase hp
      simp only [List.getElem_range,decide_eq_true_eq] at hp
      have hbnd := haloCellPhase_bounds hst band a b phase (by omega)
      dsimp only [start,haloPhaseStart,count,haloPhaseCount]
      omega)
  rw [hslice] at hh
  exact hh

/-- The scan cost is local: phase count times period is bounded by halo span times gap. -/
theorem haloPhaseCount_scaled_le {s t : ℕ} (hs : 0 < s) (a b : ℕ) (hab : a ≤ b) :
    2*s*haloPhaseCount s t a b ≤ 2*(t-s)*(b-a)+4*s := by
  have hm := naturalPhase_monotone s t hab
  have he : naturalPhase s t a+haloPhaseCount s t a b = naturalPhase s t b+1 := by
    dsimp only [haloPhaseCount,haloPhaseStart]
    omega
  have hmod := Nat.mod_lt (2*(t-s)*a+s) (show 0 < 2*s by omega)
  have hnum := Nat.mod_add_div (2*(t-s)*a+s) (2*s)
  have hqa : 2*(t-s)*a+s < 2*s*(naturalPhase s t a+1) := by
    dsimp only [naturalPhase]
    nlinarith only [hmod,hnum]
  have hqb : 2*s*naturalPhase s t b ≤ 2*(t-s)*b+s := by
    exact Nat.mul_div_le _ _
  have hmul := congrArg (fun n => 2*s*n) he
  have hspan : 2*(t-s)*b = 2*(t-s)*a+2*(t-s)*(b-a) := by
    rw [← Nat.mul_add,Nat.add_sub_of_le hab]
  nlinarith only [hqa,hqb,hmul,hspan]

/-- In the near-one regime, only linearly many phases can touch the local interval. -/
theorem haloPhaseCount_le_length {s t : ℕ} (hs : 0 < s) (hgap : t-s ≤ s)
    (a b : ℕ) (hab : a ≤ b) : haloPhaseCount s t a b ≤ b-a+2 := by
  have hh := haloPhaseCount_scaled_le (t := t) hs a b hab
  have hg := Nat.mul_le_mul_right (2*(b-a)) hgap
  nlinarith only [hh,hg,hs]

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
